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
use core::fmt;
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

    #[inline]
    pub const fn cap() -> (u32, u32) {
        let inter_cap = InterNode::<K, V>::cap();
        let leaf_cap = LeafNode::<K, V>::cap();
        (inter_cap, leaf_cap)
    }

    /// When root is leaf, returns 0, otherwise return the number of layers of inter node
    #[inline(always)]
    pub fn height(&self) -> u32 {
        if let Some(Node::Inter(node)) = &self.root {
            return node.height();
        }
        0
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
                                    let count = node.count() + 1;
                                    for i in 0..count {
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
            cache
        }
    }

    /// Returns an entry to the key in the map
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let cache = self.get_cache();
        cache.clear();
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

    #[inline(always)]
    fn get_root_unwrap(&self) -> &Node<K, V> {
        self.root.as_ref().unwrap()
    }

    /// update the separate_key in parent after borrowing space from left/right node
    #[inline]
    fn update_parent_key(&mut self, leaf: LeafNode<K, V>, rel: PathState) {
        let cache = self.get_cache();
        cache.change_state(rel);
        let key = unsafe { (*leaf.key_ptr(0)).assume_init_ref().clone() };
        while let Some((parent, parent_idx)) = self.get_cache().pop(&key, self.get_root_unwrap()) {
            if parent_idx > 0 {
                let parent_key = unsafe { (*parent.key_ptr(parent_idx)).assume_init_mut() };
                *parent_key = key;
                return;
            }
            // if parent_idx == 0, this is the leftest node in the branch, we go up until finding a
            // split key
        }
    }

    /// Insert with split handling - called when leaf is full
    fn insert_with_split(
        &mut self, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
    ) -> *mut V {
        debug_assert!(leaf.is_full().is_ok());
        let cap = LeafNode::<K, V>::cap();
        self.len += 1;
        if idx < cap {
            // random insert, try borrow space from left and right
            if let Some(mut left_node) = leaf.get_left_node() {
                if let Err(_) = left_node.is_full() {
                    let (idx, _is_equal) = leaf.search(&key);
                    debug_assert!(!_is_equal);
                    if idx == 0 {
                        // leaf is not change, but since the insert pos is leftest, mean parent
                        // separate_key <= key, need to update its separate_key
                        self.update_parent_key(leaf, PathState::Current);
                        return left_node.insert_no_split(key, value);
                    } else {
                        leaf.move_left(&mut left_node, 0, 1);
                        let val_p = leaf.insert_no_split(key, value);
                        self.update_parent_key(leaf, PathState::Current);
                        return val_p;
                    }
                }
            }
            if let Some(mut right_node) = leaf.get_right_node() {
                if let Err(_) = right_node.is_full() {
                    let (idx, _is_equal) = leaf.search(&key);
                    debug_assert!(!_is_equal);
                    if idx == cap {
                        // leaf is not change, in this condition, right_node is the leftmost child
                        // of its parent, need to update its separate_key
                        let val_p = right_node.insert_no_split_with_idx(0, key, value);
                        self.update_parent_key(right_node, PathState::Left);
                        return val_p;
                    } else {
                        leaf.move_right::<false>(&mut right_node, cap - 1, 1);
                        let val_p = leaf.insert_no_split(key, value);
                        self.update_parent_key(right_node, PathState::Left);
                        return val_p;
                    }
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
        let mut height = 0;
        // If we have parent nodes in cache, process them iteratively
        while let Some((mut parent, _idx)) = cache.pop(&promote_key, self.get_root_unwrap()) {
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
        let new_root = InterNode::<K, V>::new_root(height + 1, promote_key, left_ptr, right_ptr);
        let _old_root = self.root.replace(Node::Inter(new_root)).expect("should have old root");
        #[cfg(debug_assertions)]
        {
            match _old_root {
                Node::Inter(node) => {
                    debug_assert_eq!(height, node.height(), "old inter root at {height}");
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
                Node::Leaf(node) => {
                    debug_assert_eq!(height, 0);
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
            }
        }
    }

    /// Dump the entire tree structure for debugging
    #[cfg(test)]
    pub fn dump(&self)
    where
        K: fmt::Debug,
        V: fmt::Debug,
    {
        println!("=== BTreeMap Dump ===");
        println!("Length: {}", self.len());
        if let Some(root) = &self.root {
            self.dump_node(root, 0);
        } else {
            println!("(empty)");
        }
        println!("=====================");
    }

    #[cfg(test)]
    fn dump_node(&self, node: &Node<K, V>, depth: usize)
    where
        K: fmt::Debug,
        V: fmt::Debug,
    {
        match node {
            Node::Leaf(leaf) => {
                print!("{:indent$}", "", indent = depth * 2);
                println!("{:?}", leaf);
            }
            Node::Inter(inter) => {
                print!("{:indent$}", "", indent = depth * 2);
                println!("{:?}", inter);
                // Dump children
                let count = inter.count() as u32;
                for i in 0..=count {
                    unsafe {
                        let child_ptr = *inter.child_ptr(i);
                        if !child_ptr.is_null() {
                            let child_node = if (*child_ptr).is_leaf() {
                                Node::Leaf(LeafNode::<K, V>::from_header(NonNull::new_unchecked(
                                    child_ptr,
                                )))
                            } else {
                                Node::Inter(InterNode::<K, V>::from_header(NonNull::new_unchecked(
                                    child_ptr,
                                )))
                            };
                            self.dump_node(&child_node, depth + 1);
                        }
                    }
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
        let cap = LeafNode::<i32, i32>::cap() as usize;
        // Fill the node to capacity
        for i in 0..cap {
            assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        }
        assert_eq!(map.len(), cap as usize);
        // Verify all values
        for i in 0..cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
        }
    }

    #[test]
    fn test_split_leaf_simple() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap() as usize;

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

        println!("verify after split");
        map.dump(); // Debug: dump tree structure

        // Verify all values including the new one
        for i in 0..=cap {
            assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)), "Failed to get key {}", i);
        }
    }

    #[test]
    fn test_split_leaf_insert_at_beginning() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap() as usize;

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
        let cap = LeafNode::<i32, i32>::cap() as usize;

        // Fill with even numbers: 0, 2, 4, 6, ...
        for i in 0..cap {
            assert_eq!(map.insert((i * 2) as i32, (i * 20) as i32), None);
        }

        // Insert an odd number in the middle (cap - 1 is odd and not in the sequence)
        let insert_key = (cap - 1) as i32;
        assert_eq!(map.insert(insert_key, insert_key * 10), None);
        assert_eq!(map.len(), cap + 1);

        // Verify the new key
        assert_eq!(map.get(&insert_key), Some(&(insert_key * 10)));

        // Verify some original keys
        assert_eq!(map.get(&0), Some(&0));
        assert_eq!(map.get(&2), Some(&20));
    }

    #[test]
    fn test_split_leaf_seq() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap() as usize;

        // Insert just enough to trigger one split
        for i in 0..(cap + 1) {
            map.insert(i as i32, i as i32 * 10);
        }
        assert_eq!(map.len(), cap + 1);
    }

    #[test]
    fn test_split_leaf_verify_structure() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let cap = LeafNode::<i32, i32>::cap() as usize;

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

    #[test]
    fn test_large_tree_split_seq() {
        let mut map: BTreeMap<i32, i32> = BTreeMap::new();
        let (inter_cap, leaf_cap) = BTreeMap::<i32, i32>::cap();
        assert!(100 > inter_cap);
        assert!(100 > leaf_cap);
        // Insert many values to create multi-level tree
        for i in 0..100 {
            assert_eq!(map.insert(i, i * 2), None);
        }
        assert_eq!(map.len(), 100);
        println!("tree height {}", map.height());
        // Verify all values
        for i in 0..100 {
            assert_eq!(map.get(&i), Some(&(i * 2)));
        }
    }

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
        let cap = LeafNode::<i32, i32>::cap() as usize;
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

    /// Test borrowing from left sibling in a height=1 tree (root is InterNode, children are LeafNode)
    /// Manually constructs a tree where middle leaf is full and left leaf has space
    #[test]
    fn test_borrow_from_left_sibling_height_1() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::Node;

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();

            // Create three leaf nodes
            let mut left_leaf = LeafNode::<i32, i32>::alloc();
            let mut middle_leaf = LeafNode::<i32, i32>::alloc();
            let mut right_leaf = LeafNode::<i32, i32>::alloc();

            // Fill left leaf to capacity - 1 (has space to borrow)
            for i in 0..(leaf_cap - 1) {
                left_leaf.insert_no_split(i as i32, i as i32 * 10);
            }

            // Fill middle leaf to capacity (full)
            for i in 0..leaf_cap {
                middle_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
            }

            // Fill right leaf to capacity - 1 (has space to borrow)
            for i in 0..(leaf_cap - 1) {
                right_leaf
                    .insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
            }

            // Link leaf nodes
            (*left_leaf.brothers()).next = middle_leaf.get_ptr();
            (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
            (*middle_leaf.brothers()).next = right_leaf.get_ptr();
            (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

            // Create root internal node with height=1
            let mut root = InterNode::<i32, i32>::alloc(1);
            root.set_left_ptr(left_leaf.get_ptr());
            let middle_first_key = (*middle_leaf.key_ptr(0)).assume_init_read();
            let right_first_key = (*right_leaf.key_ptr(0)).assume_init_read();
            root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
            root.insert_no_split(right_first_key, right_leaf.get_ptr());

            // Create BTreeMap with this structure
            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: (3 * leaf_cap - 2) as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            // Insert into middle leaf (which is full) - this will trigger either borrowing or split
            let insert_key = leaf_cap as i32 + 5;
            let insert_value = insert_key * 10;

            // Verify middle leaf is full before insert
            assert!(middle_leaf.is_full().is_ok());
            assert!(left_leaf.is_full().is_err()); // left has space

            // Perform insert
            map.insert(insert_key, insert_value);

            // Verify the insert succeeded
            assert_eq!(map.get(&insert_key), Some(&insert_value));

            // Verify tree structure is still valid
            if let Some(Node::Inter(root)) = &map.root {
                assert!(root.count() >= 2); // Should have at least 2 keys
                assert_eq!(root.height(), 1);
            } else {
                panic!("Root should be InterNode");
            }

            // Cleanup
            drop(map); // This will deallocate all nodes
        }
    }

    /// Test borrowing from right sibling in a height=1 tree
    /// Manually constructs a tree where middle leaf is full and right leaf has space
    #[test]
    fn test_borrow_from_right_sibling_height_1() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::Node;

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();

            // Create three leaf nodes
            let mut left_leaf = LeafNode::<i32, i32>::alloc();
            let mut middle_leaf = LeafNode::<i32, i32>::alloc();
            let mut right_leaf = LeafNode::<i32, i32>::alloc();

            // Fill left leaf to capacity - 1 (has space)
            for i in 0..(leaf_cap - 1) {
                left_leaf.insert_no_split(i as i32, i as i32 * 10);
            }

            // Fill middle leaf to capacity (full)
            for i in 0..leaf_cap {
                middle_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
            }

            // Fill right leaf to capacity - 1 (has space to borrow)
            for i in 0..(leaf_cap - 1) {
                right_leaf
                    .insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
            }

            // Link leaf nodes
            (*left_leaf.brothers()).next = middle_leaf.get_ptr();
            (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
            (*middle_leaf.brothers()).next = right_leaf.get_ptr();
            (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

            // Create root internal node with height=1
            let mut root = InterNode::<i32, i32>::alloc(1);
            root.set_left_ptr(left_leaf.get_ptr());
            let middle_first_key = (*middle_leaf.key_ptr(0)).assume_init_read();
            let right_first_key = (*right_leaf.key_ptr(0)).assume_init_read();
            root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
            root.insert_no_split(right_first_key, right_leaf.get_ptr());

            // Create BTreeMap with this structure
            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: (3 * leaf_cap - 2) as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            // Insert at the end of middle leaf (which is full) - should borrow from right
            let insert_key = 2 * leaf_cap as i32 - 1;
            let insert_value = insert_key * 10;

            // Verify middle leaf is full before insert
            assert!(middle_leaf.is_full().is_ok());
            assert!(right_leaf.is_full().is_err()); // right has space

            // Perform insert
            map.insert(insert_key, insert_value);

            // Verify the insert succeeded
            assert_eq!(map.get(&insert_key), Some(&insert_value));

            // Cleanup
            drop(map);
        }
    }

    /// Test update_parent_key logic by manually constructing a tree and verifying parent keys are updated
    #[test]
    fn test_update_parent_key_manual() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::Node;

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();

            // Create two leaf nodes
            let mut left_leaf = LeafNode::<i32, i32>::alloc();
            let mut right_leaf = LeafNode::<i32, i32>::alloc();

            // Fill left leaf with some keys
            for i in 0..leaf_cap {
                left_leaf.insert_no_split(i as i32, i as i32 * 10);
            }

            // Fill right leaf with some keys
            for i in 0..leaf_cap {
                right_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
            }

            // Link leaf nodes
            (*left_leaf.brothers()).next = right_leaf.get_ptr();
            (*right_leaf.brothers()).prev = left_leaf.get_ptr();

            // Create root internal node
            let mut root = InterNode::<i32, i32>::alloc(1);
            root.set_left_ptr(left_leaf.get_ptr());
            let separator_key = (*right_leaf.key_ptr(0)).assume_init_read();
            root.insert_no_split(separator_key, right_leaf.get_ptr());

            // Create BTreeMap
            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: (2 * leaf_cap) as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            // Get the original separator key
            let original_separator = separator_key;

            // Insert a new key that will be the first key in right leaf
            // This should cause update_parent_key to be called
            let new_key = leaf_cap as i32 + 5;
            map.insert(new_key, new_key * 10);

            // Verify the separator key in parent was updated if necessary
            // The separator key should be the first key of the right leaf
            if let Some(Node::Inter(root)) = &map.root {
                let current_separator = (*root.key_ptr(0)).assume_init_read();
                // If the new key is smaller than the original separator, parent key should be updated
                if new_key < original_separator {
                    assert_eq!(
                        current_separator, new_key,
                        "Parent separator key should be updated"
                    );
                }
            }

            // Cleanup
            drop(map);
        }
    }

    /// Test tree with height=2 (root -> internal nodes -> leaves)
    /// Manually constructs a 2-level tree and tests insertion with borrowing
    #[test]
    fn test_borrow_height_2() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::Node;

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();
            let inter_cap = InterNode::<i32, i32>::cap();

            // Create leaf nodes for left branch
            let mut leaf_0 = LeafNode::<i32, i32>::alloc();
            let mut leaf_1 = LeafNode::<i32, i32>::alloc();
            for i in 0..leaf_cap {
                leaf_0.insert_no_split(i as i32, i as i32 * 10);
                leaf_1.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
            }

            // Create leaf nodes for right branch
            let mut leaf_2 = LeafNode::<i32, i32>::alloc();
            let mut leaf_3 = LeafNode::<i32, i32>::alloc();
            for i in 0..leaf_cap {
                leaf_2.insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
                leaf_3.insert_no_split((3 * leaf_cap + i) as i32, (3 * leaf_cap + i) as i32 * 10);
            }

            // Link leaves
            (*leaf_0.brothers()).next = leaf_1.get_ptr();
            (*leaf_1.brothers()).prev = leaf_0.get_ptr();
            (*leaf_1.brothers()).next = leaf_2.get_ptr();
            (*leaf_2.brothers()).prev = leaf_1.get_ptr();
            (*leaf_2.brothers()).next = leaf_3.get_ptr();
            (*leaf_3.brothers()).prev = leaf_2.get_ptr();

            // Create left internal node (height=1)
            let mut internal_left = InterNode::<i32, i32>::alloc(1);
            internal_left.set_left_ptr(leaf_0.get_ptr());
            let leaf1_first_key = (*leaf_1.key_ptr(0)).assume_init_read();
            internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

            // Create right internal node (height=1)
            let mut internal_right = InterNode::<i32, i32>::alloc(1);
            internal_right.set_left_ptr(leaf_2.get_ptr());
            let leaf3_first_key = (*leaf_3.key_ptr(0)).assume_init_read();
            internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

            // Create root internal node (height=2)
            let mut root = InterNode::<i32, i32>::alloc(2);
            root.set_left_ptr(internal_left.get_ptr());
            let leaf2_first_key = (*leaf_2.key_ptr(0)).assume_init_read();
            root.insert_no_split(leaf2_first_key, internal_right.get_ptr());

            // Create BTreeMap with height=2 structure
            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: (4 * leaf_cap) as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            assert_eq!(map.height(), 2);

            // Test insertion that may trigger borrowing across the tree
            let insert_key = 2 * leaf_cap as i32 + 5;
            let insert_value = insert_key * 10;

            map.insert(insert_key, insert_value);

            // Verify insertion succeeded
            assert_eq!(map.get(&insert_key), Some(&insert_value));
            assert_eq!(map.len(), (4 * leaf_cap + 1) as usize);

            // Verify tree height is still 2
            assert_eq!(map.height(), 2);

            // Cleanup
            drop(map);
        }
    }

    /// Test two-level internal nodes with complex borrowing scenario
    /// Creates a tree where internal nodes themselves might need to borrow
    #[test]
    fn test_borrow_two_level_internal_nodes() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::Node;

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();
            let inter_cap = InterNode::<i32, i32>::cap();

            // Create multiple leaf nodes to fill internal nodes
            let mut leaves = Vec::new();
            let leaf_count = inter_cap * 2; // Enough to potentially fill internal nodes

            for i in 0..leaf_count {
                let mut leaf = LeafNode::<i32, i32>::alloc();
                let base_key = (i * leaf_cap) as i32;
                for j in 0..leaf_cap {
                    leaf.insert_no_split(base_key + j as i32, (base_key + j as i32) * 10);
                }
                leaves.push(leaf);
            }

            // Link leaves together
            for i in 0..leaf_count as usize {
                if i > 0 {
                    (*leaves[i].brothers()).prev = leaves[i - 1].get_ptr();
                }
                if i < leaf_count as usize - 1 {
                    (*leaves[i].brothers()).next = leaves[i + 1].get_ptr();
                }
            }

            // Create internal nodes that point to leaves
            let mut internal_nodes = Vec::new();
            let leaves_per_internal = inter_cap as usize; // Each internal node can have inter_cap keys

            for i in 0..((leaf_count as usize + leaves_per_internal - 1) / leaves_per_internal) {
                let mut internal = InterNode::<i32, i32>::alloc(1);
                let start_idx = i * leaves_per_internal;
                let end_idx = core::cmp::min(start_idx + leaves_per_internal, leaf_count as usize);

                internal.set_left_ptr(leaves[start_idx].get_ptr());
                for j in (start_idx + 1)..end_idx {
                    let separator_key = (*leaves[j].key_ptr(0)).assume_init_read();
                    internal.insert_no_split(separator_key, leaves[j].get_ptr());
                }
                internal_nodes.push(internal);
            }

            // Create root internal node pointing to internal nodes
            let mut root = InterNode::<i32, i32>::alloc(2);
            root.set_left_ptr(internal_nodes[0].get_ptr());
            for i in 1..internal_nodes.len() {
                let separator_key =
                    (*leaves[i * leaves_per_internal].key_ptr(0)).assume_init_read();
                root.insert_no_split(separator_key, internal_nodes[i].get_ptr());
            }

            // Calculate total elements
            let total_elements = leaf_count as u32 * leaf_cap;

            // Create BTreeMap
            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: total_elements as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            assert_eq!(map.height(), 2);

            // Test insertion in the middle of the tree structure
            let insert_key = total_elements as i32 / 2;
            let insert_value = insert_key * 10;

            map.insert(insert_key, insert_value);

            // Verify insertion
            assert_eq!(map.get(&insert_key), Some(&insert_value));
            assert_eq!(map.len(), (total_elements + 1) as usize);

            // Cleanup
            drop(map);
        }
    }

    /// Test PathCache with actual tree operations
    #[test]
    fn test_path_cache_with_tree_operations() {
        use super::inter::InterNode;
        use super::leaf::LeafNode;
        use super::node::{Node, PathState};

        unsafe {
            let leaf_cap = LeafNode::<i32, i32>::cap();

            // Create a simple tree structure
            let mut leaf1 = LeafNode::<i32, i32>::alloc();
            let mut leaf2 = LeafNode::<i32, i32>::alloc();

            for i in 0..leaf_cap {
                leaf1.insert_no_split(i as i32, i as i32 * 10);
                leaf2.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
            }

            (*leaf1.brothers()).next = leaf2.get_ptr();
            (*leaf2.brothers()).prev = leaf1.get_ptr();

            let mut root = InterNode::<i32, i32>::alloc(1);
            root.set_left_ptr(leaf1.get_ptr());
            let leaf2_first_key = (*leaf2.key_ptr(0)).assume_init_read();
            root.insert_no_split(leaf2_first_key, leaf2.get_ptr());

            let mut map = BTreeMap::<i32, i32> {
                root: Some(Node::Inter(root)),
                len: (2 * leaf_cap) as usize,
                cache: core::cell::UnsafeCell::new(super::node::PathCache::new()),
            };

            // Perform operations that should use cache
            let _ = map.get(&(leaf_cap as i32 / 2));

            // Test entry which populates cache
            let _entry = map.entry(leaf_cap as i32 + 5);

            // Cleanup
            drop(map);
        }
    }
}
