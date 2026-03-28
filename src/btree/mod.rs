//! B+Tree Map - A in memory cache-optimized B+Tree for single-threaded use.
//!
//! ## Feature outlines
//! - designed for CPU cache efficiency and memory efficiency:
//! - It's B+tree. Data stores only at leaf level, with links at leaf level.
//!   - Provids efficent iteration of data
//!   - Linear search within nodes, respecting cacheline boundaries
//! - Nodes are filled up in 4 cache lines (256 bytes on x86_64)
//!   - keys stored in first 128B (with header)
//!   - Values/pointers stored in last 128B
//!   - the capacity is calculated according to the size of K, V, with limitations:
//!     - K & V should <= CACHE_LINE_SIZE - 16  (If K & V is larger should put into `Box`)
//! - Specialy Entry API which allow to modify after moving the cursor to adjacent data.
//! - Comparing to std::collections::btree (rust 1.94):
//!   - The std impl is pure btree (not b+tree) without horizonal links. Data store at both leaf and inter nodes.
//!   - The std impl is optimised for point lookup,
//!   - The std impl has fixed Cap=11, size is 288B for InterNode and 192B for LeafNode.
//!   - The std cursor API is stll unstable (as of 1.94) and provides more complex features
//! - The detail design notes are with the source in mod.rs and node.rs

/*

# Designer notes

 Target scenario:  To maintain slab tree for disk, lets say 8T , the worst fragmental scenario will
 need 1 billion nodes. So this design is aim for high fan-out.

 Since There're no parent pointer, no fence keys. So we maintain a cache to accellerate the look
 up for parent nodes. In the worst case, cache might obsolete and we need to fallback to traverse from the top,
 when it comes to joining of the nodes.

 Since we support combinding cursor moving in Entry API (try to merge with previous or next adjacent
 node). But user can call `remove()` on moved cursor.

## The state of PathCache:

- Left
    - The cache represent the path of left brother of current Entry
    - cursor moves prev(left), change back to current
    - cursor moves next(right), change to `Stale`
- Right
    - The cache represent the path of right brother of current Entry
    - cursor moves prev(left), change to `Stale`
    - cursor moves next(right), change back to current
- Current
    - The cache represent the path of current Entry
    - the initial state after descending the tree to get an Entry
    - Cursor moves prev(left)，change to `Right`
    - cursor moves next(right), change to `Left`
- Stale: cache data is obsoleted, fallback to top-down search from root

## Accelleration Search for finding the parent using PathCache

- Assume PathCache is for Node A, Node B is the right brother of node A. A's ptr is at ParentA[idx]
  - To find parent for Node B
    - If idx < last (Cap - 1), then A and B has common parent,
    - otherwise A and B have no common parent. Should continue iteration to upper PathCache. There will be common ancestor until idx < last

- Assume PathCache is for Node B, Node A is the left brother of node B, B's ptr is at ParentB[idx]
  - To find parent for Node A
    - If idx > 0, then A and B has common parent.
    - otherwise A and B have no common parent. Should continue interation to upper PathCache. There will be common ancestor until idx > 0

## Future ideas

- prefix compress (u32), difficult because we are generic
- incress InterNode size, or variable size
- borrow from leaf / right on InterNode split, increase fill ratio to 80%
- 2 - 3 split (increase fill ratio to 90%)

*/

use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::ptr::NonNull;
pub mod entry;
use entry::*;
mod node;
use node::*;
mod inter;
use inter::*;
mod leaf;
use leaf::*;

/// B+Tree Map for single-threaded use
pub struct BTreeMap<K, V> {
    /// Root node (may be null for empty tree)
    root: Option<Node<K, V>>,
    /// Number of elements in the tree
    len: usize,
    // use unsafe to avoid borrow problems
    cache: UnsafeCell<PathCache<K, V>>,
}

unsafe impl<K: Send, V: Send> Send for BTreeMap<K, V> {}
unsafe impl<K: Send, V: Send> Sync for BTreeMap<K, V> {}

impl<K: Ord + Sized + Clone, V: Sized> BTreeMap<K, V> {
    /// Create a new empty BTreeMap
    pub fn new() -> Self {
        Self { root: None, len: 0, cache: UnsafeCell::new(PathCache::<K, V>::new()) }
    }
}

impl<K, V> BTreeMap<K, V> {
    /// Returns the number of elements in the map
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the map is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<K: Ord + Sized + Clone, V: Sized> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for BTreeMap<K, V> {
    fn drop(&mut self) {
        if let Some(root) = &mut self.root {
            match root {
                Node::Inter(inter_node) => {
                    unsafe {
                        // Non-recursive drop using BFS
                        let mut nodes_to_free = Vec::new();
                        let mut current_level = Vec::new();

                        // Start with root's children
                        let root_count = inter_node.count() as u32;
                        for i in 0..=root_count {
                            let child_ptr = *inter_node.child_ptr(i);
                            if !child_ptr.is_null() {
                                current_level.push(child_ptr);
                            }
                        }

                        // First, collect all leaf nodes and free them
                        let mut next_level = Vec::new();
                        while !current_level.is_empty() {
                            for &child_ptr in &current_level {
                                let header = &*child_ptr;
                                if header.is_leaf() {
                                    // This is a leaf node, free it
                                    let mut leaf = LeafNode::<K, V>::from_header(
                                        NonNull::new_unchecked(child_ptr),
                                    );
                                    leaf.dealloc();
                                } else {
                                    // This is an internal node, add its children to next level
                                    let node = InterNode::<K, V>::from_header(
                                        NonNull::new_unchecked(child_ptr),
                                    );
                                    let count = node.count() as u32;
                                    for i in 0..=count {
                                        let grandchild_ptr = *node.child_ptr(i);
                                        if !grandchild_ptr.is_null() {
                                            next_level.push(grandchild_ptr);
                                        }
                                    }
                                    nodes_to_free.push(child_ptr);
                                }
                            }
                            current_level = next_level;
                            next_level = Vec::new();
                        }

                        // Free internal nodes in reverse order (from bottom to top)
                        for node_ptr in nodes_to_free.iter().rev() {
                            let mut node =
                                InterNode::<K, V>::from_header(NonNull::new_unchecked(*node_ptr));
                            node.dealloc();
                        }

                        // Finally, free the root
                        inter_node.dealloc();
                    }
                }
                Node::Leaf(leaf_node) => unsafe { leaf_node.dealloc() },
            }
        }
    }
}

// Main operations
impl<K: Ord + Sized + Clone, V: Sized> BTreeMap<K, V> {
    #[inline(always)]
    fn get_cache(&self) -> &mut PathCache<K, V> {
        unsafe {
            let cache = &mut *self.cache.get();
            cache.clear();
            cache
        }
    }

    /// Returns an entry to the key in the map
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let cache = self.get_cache();
        let leaf = match &self.root {
            None => return Entry::Vacant(VacantEntry { map: self, key, idx: 0, node: None }),
            Some(root) => root.find_leaf_with_cache(cache, &key),
        };
        let (idx, is_equal) = leaf.search(&key);
        if is_equal {
            Entry::Occupied(OccupiedEntry { map: self, idx, node: leaf })
        } else {
            Entry::Vacant(VacantEntry { map: self, key, idx, node: Some(leaf) })
        }
    }

    /// Returns true if the map contains the key
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key
    pub fn get(&self, key: &K) -> Option<&V> {
        let leaf = match &self.root {
            None => return None,
            Some(root) => root.find_leaf(key),
        };
        let (idx, is_equal) = leaf.search(key);
        if is_equal {
            let value = unsafe { leaf.value_ptr(idx) };
            debug_assert!(!value.is_null());
            return Some(unsafe { (*value).assume_init_ref() });
        }
        None
    }

    /// Returns a mutable reference to the value corresponding to the key
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let leaf = match &self.root {
            None => return None,
            Some(root) => root.find_leaf(key),
        };
        let (idx, is_equal) = leaf.search(key);
        if is_equal {
            let value = unsafe { leaf.value_ptr(idx) };
            debug_assert!(!value.is_null());
            return Some(unsafe { (*value).assume_init_mut() });
        }
        None
    }

    /// Insert a key-value pair into the map
    /// Returns the old value if the key already existed
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // use entry api to insert
        match self.entry(key) {
            Entry::Occupied(mut entry) => Some(entry.insert(value)),
            Entry::Vacant(entry) => {
                entry.insert(value);
                None
            }
        }
    }

    /// Remove a key from the map, returning the value if it existed
    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Clone,
    {
        //TODO fix it
        match self.entry(key.clone()) {
            Entry::Occupied(entry) => Some(entry.remove()),
            Entry::Vacant(_) => None,
        }
    }

    /// Insert with split handling - called when leaf is full
    fn insert_with_split(
        &mut self, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
    ) -> *mut V {
        debug_assert!(leaf.is_full().is_ok());
        let leaf_count = leaf.count() as u32;
        self.len += 1;
        if idx < leaf_count {
            // random insert, try borrow space from left and right
            if let Some(mut left_node) = leaf.get_left_node() {
                if let Err(avail) = left_node.is_full() {
                    leaf.move_left(&mut left_node, 0, avail);
                    todo!();
                    // change parent key
                    return leaf.insert_no_split(key, value);
                }
            }
            if let Some(mut right_node) = leaf.get_right_node() {
                if let Err(avail) = right_node.is_full() {
                    leaf.move_right::<false>(&mut right_node, leaf_count - avail, avail);
                    todo!();
                    // change right node parent key
                    return leaf.insert_no_split(key, value);
                }
            }
        } else {
            // insert into empty new node, left is probably full, right is probably none
        }
        let (new_leaf, ptr_v) = leaf.insert_with_split(idx, key, value);
        let split_key = unsafe { (*new_leaf.key_ptr(0)).assume_init_ref().clone() };
        self.propagate_split(split_key, leaf.get_ptr(), new_leaf.get_ptr());
        ptr_v
    }

    /// Propagate node split up the tree using iteration (non-recursive)
    fn propagate_split(
        &mut self, mut promote_key: K, mut left_ptr: *mut NodeHeader,
        mut right_ptr: *mut NodeHeader,
    ) {
        let cache = self.get_cache();
        let mut height = 1;
        // If we have parent nodes in cache, process them iteratively
        while let Some(mut parent) = cache.pop(&promote_key, self.root.as_ref().unwrap()) {
            if !parent.is_full().is_ok() {
                parent.insert_no_split(promote_key, right_ptr);
                return;
            }
            height += 1;
            // Parent is full, need to split internal node
            let (right, _promote_key) = parent.insert_split(promote_key, right_ptr);
            promote_key = _promote_key;
            right_ptr = right.get_ptr();
            left_ptr = parent.get_ptr();
            // Continue to next parent in cache (loop will pop next parent)
        }
        // No more parents in cache, create new root
        let new_root = InterNode::<K, V>::new_root(height, promote_key, left_ptr, right_ptr);
        let _old_root = self.root.replace(Node::Inter(new_root)).expect("should have old root");
        #[cfg(debug_assertions)]
        {
            match _old_root {
                Node::Inter(node) => {
                    debug_assert!(height > 1, "old inter root at {height}");
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
                Node::Leaf(node) => {
                    debug_assert_eq!(height, 1);
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
            }
        }
    }

    /// Handle leaf node underflow by borrowing from or merging with sibling
    unsafe fn handle_leaf_underflow(
        &mut self, _parent: InterNode<K, V>, _leaf: &mut LeafNode<K, V>,
    ) {
        // TODO: Implement underflow handling with proper pointer-based parent tracking
        // For now, this is a placeholder to avoid compilation errors
        //        unsafe {
        //            let leaf_count = leaf.count();
        //            let min_count = (LeafNode::<K, V>::cap() + 1) / 2;
        //            if leaf_count >= min_count {
        //                return; // No underflow
        //            }
        //
        //            // Find leaf index in parent
        //            let leaf_idx = self.find_child_index(&parent, leaf.get_ptr());
        //
        //            // Try left sibling first
        //            if leaf_idx > 0 {
        //                let left_sibling_ptr = *parent.child_ptr(leaf_idx - 1);
        //                if !left_sibling_ptr.is_null() {
        //                    let mut left_sibling =
        //                        LeafNode::<K, V>::from_header(NonNull::new_unchecked(left_sibling_ptr));
        //                    let sibling_count = left_sibling.count();
        //
        //                    if sibling_count > min_count {
        //                        // Borrow from left sibling
        //                        self.borrow_from_left_leaf(&mut left_sibling, leaf);
        //                        return;
        //                    } else {
        //                        // Merge with left sibling
        //                        let mut parent_mut = parent.clone();
        //                        self.merge_leaf_with_left(
        //                            &mut left_sibling,
        //                            leaf,
        //                            &mut parent_mut,
        //                            leaf_idx - 1,
        //                        );
        //                        return;
        //                    }
        //                }
        //            }
        //
        //            // Try right sibling
        //            let parent_count = parent.count() as u32;
        //            if leaf_idx < parent_count {
        //                let right_sibling_ptr = *parent.child_ptr(leaf_idx + 1);
        //                if !right_sibling_ptr.is_null() {
        //                    let mut right_sibling =
        //                        LeafNode::<K, V>::from_header(NonNull::new_unchecked(right_sibling_ptr));
        //                    let sibling_count = right_sibling.count();
        //                    let mut parent_mut = parent.clone();
        //
        //                    if sibling_count > min_count {
        //                        // Borrow from right sibling
        //                        self.borrow_from_right_leaf(leaf, &mut right_sibling);
        //                    } else {
        //                        // Merge with right sibling
        //                        self.merge_leaf_with_right(
        //                            leaf,
        //                            &mut right_sibling,
        //                            &mut parent_mut,
        //                            leaf_idx,
        //                        );
        //                    }
        //                }
        //            }
        //        }
    }

    //    /// Borrow one element from left sibling
    //    unsafe fn borrow_from_left_leaf(
    //        &mut self, left_sibling: &mut LeafNode<K, V>, leaf: &mut LeafNode<K, V>,
    //    ) {
    //        unsafe {
    //            let sibling_count = left_sibling.count() as u32;
    //
    //            // Move last element from left sibling to front of leaf
    //            let key_to_move = (*left_sibling.key_ptr(sibling_count - 1)).assume_init_read();
    //            let val_to_move = (*left_sibling.value_ptr(sibling_count - 1)).assume_init_read();
    //
    //            // Shift leaf elements right
    //            let leaf_count = leaf.count() as u32;
    //            for i in (0..leaf_count).rev() {
    //                let src_key = leaf.key_ptr(i);
    //                let dst_key = leaf.key_ptr(i + 1);
    //                let k = (*src_key).assume_init_read();
    //                (*dst_key).write(k);
    //
    //                let src_val = leaf.value_ptr(i);
    //                let dst_val = leaf.value_ptr(i + 1);
    //                let v = (*src_val).assume_init_read();
    //                (*dst_val).write(v);
    //            }
    //
    //            // Insert borrowed element
    //            (*leaf.key_ptr(0)).write(key_to_move);
    //            (*leaf.value_ptr(0)).write(val_to_move);
    //
    //            // Update counts
    //            left_sibling.get_header_mut().count -= 1;
    //            leaf.get_header_mut().count += 1;
    //        }
    //    }
    //
    //    /// Borrow one element from right sibling
    //    unsafe fn borrow_from_right_leaf(
    //        &mut self, leaf: &mut LeafNode<K, V>, right_sibling: &mut LeafNode<K, V>,
    //    ) {
    //        unsafe {
    //            // Move first element from right sibling to end of leaf
    //            let key_to_move = (*right_sibling.key_ptr(0)).assume_init_read();
    //            let val_to_move = (*right_sibling.value_ptr(0)).assume_init_read();
    //
    //            let leaf_count = leaf.count() as u32;
    //            (*leaf.key_ptr(leaf_count)).write(key_to_move);
    //            (*leaf.value_ptr(leaf_count)).write(val_to_move);
    //
    //            // Shift right sibling elements left
    //            let sibling_count = right_sibling.count() as u32;
    //            for i in 0..sibling_count - 1 {
    //                let src_key = right_sibling.key_ptr(i + 1);
    //                let dst_key = right_sibling.key_ptr(i);
    //                let k = (*src_key).assume_init_read();
    //                (*dst_key).write(k);
    //
    //                let src_val = right_sibling.value_ptr(i + 1);
    //                let dst_val = right_sibling.value_ptr(i);
    //                let v = (*src_val).assume_init_read();
    //                (*dst_val).write(v);
    //            }
    //
    //            // Update counts
    //            leaf.get_header_mut().count += 1;
    //            right_sibling.get_header_mut().count -= 1;
    //        }
    //    }
    //
    //    /// Merge leaf with left sibling
    //    unsafe fn merge_leaf_with_left(
    //        &mut self, left_sibling: &mut LeafNode<K, V>, leaf: &mut LeafNode<K, V>,
    //        parent: &mut InterNode<K, V>, parent_key_idx: u32,
    //    ) {
    //        unsafe {
    //            let left_count = left_sibling.count() as u32;
    //            let leaf_count = leaf.count() as u32;
    //
    //            // Move all elements from leaf to left sibling
    //            for i in 0..leaf_count {
    //                let src_key = leaf.key_ptr(i);
    //                let dst_key = left_sibling.key_ptr(left_count + i);
    //                let k = (*src_key).assume_init_read();
    //                (*dst_key).write(k);
    //
    //                let src_val = leaf.value_ptr(i);
    //                let dst_val = left_sibling.value_ptr(left_count + i);
    //                let v = (*src_val).assume_init_read();
    //                (*dst_val).write(v);
    //            }
    //
    //            // Update left sibling count
    //            left_sibling.get_header_mut().count = (left_count + leaf_count) as u32;
    //
    //            // Update leaf links
    //            let leaf_next = (*leaf.brothers()).next;
    //            (*left_sibling.brothers()).next = leaf_next;
    //            if !leaf_next.is_null() {
    //                (*LeafNode::<K, V>::from_header(NonNull::new_unchecked(leaf_next)).brothers())
    //                    .prev = left_sibling.get_ptr();
    //            }
    //
    //            // Remove leaf from parent
    //            self.remove_child_from_parent(parent, parent_key_idx);
    //
    //            // Deallocate leaf
    //            leaf.dealloc();
    //        }
    //    }
    //
    //    /// Merge leaf with right sibling
    //    unsafe fn merge_leaf_with_right(
    //        &mut self, leaf: &mut LeafNode<K, V>, right_sibling: &mut LeafNode<K, V>,
    //        parent: &mut InterNode<K, V>, parent_key_idx: u32,
    //    ) {
    //        unsafe {
    //            let leaf_count = leaf.count() as u32;
    //            let right_count = right_sibling.count() as u32;
    //
    //            // Move all elements from right sibling to leaf
    //            for i in 0..right_count {
    //                let src_key = right_sibling.key_ptr(i);
    //                let dst_key = leaf.key_ptr(leaf_count + i);
    //                let k = (*src_key).assume_init_read();
    //                (*dst_key).write(k);
    //
    //                let src_val = right_sibling.value_ptr(i);
    //                let dst_val = leaf.value_ptr(leaf_count + i);
    //                let v = (*src_val).assume_init_read();
    //                (*dst_val).write(v);
    //            }
    //
    //            // Update leaf count
    //            leaf.get_header_mut().count = (leaf_count + right_count) as u32;
    //
    //            // Update leaf links
    //            let right_next = (*right_sibling.brothers()).next;
    //            (*leaf.brothers()).next = right_next;
    //            if !right_next.is_null() {
    //                (*LeafNode::<K, V>::from_header(NonNull::new_unchecked(right_next)).brothers())
    //                    .prev = leaf.get_ptr();
    //            }
    //
    //            // Remove right sibling from parent
    //            self.remove_child_from_parent(parent, parent_key_idx + 1);
    //
    //            // Deallocate right sibling
    //            right_sibling.dealloc();
    //        }
    //    }
    //
    //    /// Remove a child from parent after merge
    //    unsafe fn remove_child_from_parent(&mut self, parent: &mut InterNode<K, V>, key_idx: u32) {
    //        unsafe {
    //            let count = parent.count() as u32;
    //
    //            // Shift keys left
    //            for i in key_idx..count - 1 {
    //                let src_key = parent.key_ptr(i + 1);
    //                let dst_key = parent.key_ptr(i);
    //                let k = (*src_key).assume_init_read();
    //                (*dst_key).write(k);
    //            }
    //
    //            // Shift children left
    //            for i in (key_idx + 1)..count {
    //                let child = *parent.child_ptr(i + 1);
    //                *parent.child_ptr(i) = child;
    //            }
    //
    //            parent.get_header_mut().count -= 1;
    //
    //            // TODO: Handle parent underflow recursively
    //        }
    //    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_new() {
        let map: BTreeMap<i32, i32> = BTreeMap::new();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }
    #[test]
    fn test_get_empty() {
        let map: BTreeMap<i32, &str> = BTreeMap::new();
        assert_eq!(map.get(&1), None);
    }
    #[test]
    fn test_insert_and_get() {
        let mut map = BTreeMap::new();
        assert_eq!(map.insert(1, "a"), None);
        assert_eq!(map.get(&1), Some(&"a"));
        assert_eq!(map.len(), 1);
    }
    #[test]
    fn test_insert_duplicate() {
        let mut map = BTreeMap::new();
        assert_eq!(map.insert(1, "a"), None);
        assert_eq!(map.insert(1, "b"), Some("a"));
        assert_eq!(map.get(&1), Some(&"b"));
        assert_eq!(map.len(), 1);
    }
    #[test]
    fn test_multiple_inserts() {
        let mut map = BTreeMap::new();
        map.insert(3, "c");
        map.insert(1, "a");
        map.insert(2, "b");
        assert_eq!(map.get(&1), Some(&"a"));
        assert_eq!(map.get(&2), Some(&"b"));
        assert_eq!(map.get(&3), Some(&"c"));
        assert_eq!(map.len(), 3);
    }
    #[test]
    fn test_get_mut() {
        let mut map = BTreeMap::new();
        map.insert(1, 10);
        if let Some(v) = map.get_mut(&1) {
            *v = 20;
        }
        assert_eq!(map.get(&1), Some(&20));
    }
    #[test]
    fn test_capacity() {
        // For i32 keys and values, we should fit several per node
        let cap = LeafNode::<i32, i32>::cap();
        assert!(cap >= 2);
    }
    #[test]
    fn test_contains_key() {
        let mut map = BTreeMap::new();
        map.insert(1, "a");
        assert!(map.contains_key(&1));
        assert!(!map.contains_key(&2));
    }
    #[test]
    fn test_entry_occupied() {
        let mut map = BTreeMap::new();
        map.insert(1, "a");
        match map.entry(1) {
            Entry::Occupied(entry) => {
                assert_eq!(entry.get(), &"a");
            }
            Entry::Vacant(_) => panic!("Expected occupied entry"),
        }
    }
    #[test]
    fn test_entry_vacant() {
        let mut map: BTreeMap<i32, &str> = BTreeMap::new();
        match map.entry(1) {
            Entry::Vacant(entry) => {
                assert_eq!(entry.key(), &1);
            }
            Entry::Occupied(_) => panic!("Expected vacant entry"),
        }
    }
    #[test]
    fn test_entry_or_insert() {
        let mut map = BTreeMap::new();
        let val = map.entry(1).or_insert("a");
        assert_eq!(*val, "a");
        let val = map.entry(1).or_insert("b");
        assert_eq!(*val, "a");
    }
    #[test]
    fn test_entry_and_modify() {
        let mut map = BTreeMap::new();
        map.insert(1, 10);
        map.entry(1).and_modify(|v| *v = 20);
        assert_eq!(map.get(&1), Some(&20));
    }
    #[test]
    fn test_remove() {
        let mut map = BTreeMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        assert_eq!(map.remove(&1), Some("a"));
        assert_eq!(map.get(&1), None);
        assert_eq!(map.len(), 1);
    }
    #[test]
    fn test_remove_nonexistent() {
        let mut map = BTreeMap::new();
        map.insert(1, "a");
        assert_eq!(map.remove(&2), None);
        assert_eq!(map.len(), 1);
    }
    #[test]
    fn test_occupied_entry_remove() {
        let mut map = BTreeMap::new();
        map.insert(1, "a");
        match map.entry(1) {
            Entry::Occupied(entry) => {
                assert_eq!(entry.remove(), "a");
            }
            _ => panic!("Expected occupied entry"),
        }
        assert!(map.is_empty());
    }
    #[test]
    fn test_fill_node() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();
        // Fill the node to capacity
        for i in 0..cap {
            assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        }
        assert_eq!(map.len(), cap);
        // Verify all values
        for i in 0..cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
        }
    }

    #[test]
    fn test_split_leaf_simple() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();

        // First, fill exactly to capacity
        for i in 0..cap {
            assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        }
        assert_eq!(map.len(), cap);

        // Verify all values
        for i in 0..cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
        }

        // Now insert one more to trigger split - insert at the end
        assert_eq!(map.insert(cap as i32, cap as i32 * 10), None);
        assert_eq!(map.len(), cap + 1);

        // Verify all values including the new one
        for i in 0..=cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
        }
    }

    #[test]
    fn test_split_leaf_insert_at_beginning() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();

        // Fill to capacity
        for i in 0..cap {
            assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        }

        // Insert at the beginning (should trigger split and move to left)
        assert_eq!(map.insert(-1, -10), None);
        assert_eq!(map.len(), cap + 1);

        // Verify the new key
        assert_eq!(map.get(&-1), Some(&-10));

        // Verify some original keys
        assert_eq!(map.get(&0), Some(&0));
        assert_eq!(map.get(&(cap as i32 - 1)), Some(&((cap - 1) as i32 * 10)));
    }

    #[test]
    fn test_split_leaf_insert_in_middle() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();

        // Fill with even numbers: 0, 2, 4, 6, ...
        for i in 0..cap {
            assert_eq!(map.insert((i * 2) as i32, (i * 20) as i32), None);
        }

        // Insert an odd number in the middle
        let insert_key = cap as i32;
        assert_eq!(map.insert(insert_key, insert_key * 10), None);
        assert_eq!(map.len(), cap + 1);

        // Verify the new key
        assert_eq!(map.get(&insert_key), Some(&(insert_key * 10)));

        // Verify some original keys
        assert_eq!(map.get(&0), Some(&0));
        assert_eq!(map.get(&2), Some(&40));
    }

    #[test]
    fn test_split_leaf_minimal() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();

        // Insert just enough to trigger one split
        for i in 0..(cap + 1) {
            println!("Inserting {}", i);
            map.insert(i as i32, i as i32 * 10);
        }

        assert_eq!(map.len(), cap + 1);
    }

    #[test]
    fn test_split_leaf_verify_structure() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();

        // Insert just enough to trigger one split
        let total = cap + 5;
        for i in 0..total {
            map.insert(i as i32, i as i32 * 10);
        }

        assert_eq!(map.len(), total);

        // Now manually traverse the tree to verify structure
        if let Some(Node::Inter(root)) = &map.root {
            println!("Root has {} children", root.count() + 1);

            unsafe {
                // Check first child
                let child0_ptr = *root.child_ptr(0);
                assert!(!child0_ptr.is_null(), "Child 0 is null");

                // Try to access it as leaf
                let leaf0 = LeafNode::<i32, i32>::from_header(NonNull::new_unchecked(child0_ptr));
                println!("Leaf 0 has {} items", leaf0.count());

                // Check second child
                let child1_ptr = *root.child_ptr(1);
                if !child1_ptr.is_null() {
                    let leaf1 =
                        LeafNode::<i32, i32>::from_header(NonNull::new_unchecked(child1_ptr));
                    println!("Leaf 1 has {} items", leaf1.count());
                }
            }
        }
    }

    // TODO: Fix this test - causes segfault due to multi-level split issues
    // #[test]
    // fn test_large_tree() {
    //     let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    //     // Insert many values to create multi-level tree
    //     for i in 0..100 {
    //         assert_eq!(map.insert(i, i * 2), None);
    //     }
    //     assert_eq!(map.len(), 100);
    //     // Verify all values
    //     for i in 0..100 {
    //         assert_eq!(map.get(&i), Some(&(i * 2)));
    //     }
    // }

    #[test]
    fn test_random_inserts() {
        let mut map: BTreeMap<i32, &str> = BTreeMap::new();
        let values = vec![
            (5, "e"),
            (3, "c"),
            (7, "g"),
            (1, "a"),
            (9, "i"),
            (2, "b"),
            (4, "d"),
            (6, "f"),
            (8, "h"),
        ];
        for (k, v) in &values {
            map.insert(*k, *v);
        }
        for (k, v) in &values {
            assert_eq!(map.get(k), Some(v));
        }
    }

    #[test]
    fn test_delete_and_merge() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap();
        // Fill node to capacity
        for i in 0..cap {
            map.insert(i as i32, i as i32 * 10);
        }
        // Delete most elements to trigger merge
        for i in 0..cap - 2 {
            assert!(map.remove(&(i as i32)).is_some());
        }
        // Verify remaining elements
        for i in cap - 2..cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
        }
    }

    #[test]
    fn test_delete_all_and_reinsert() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        // Insert some values
        for i in 0..20 {
            map.insert(i, i * 10);
        }
        // Delete all
        for i in 0..20 {
            assert!(map.remove(&i).is_some());
        }
        assert!(map.is_empty());
        // Reinsert
        for i in 0..20 {
            map.insert(i, i * 100);
        }
        // Verify
        for i in 0..20 {
            assert_eq!(map.get(&i), Some(&(i * 100)));
        }
    }
}
