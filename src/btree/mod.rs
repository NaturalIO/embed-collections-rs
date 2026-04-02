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

 Target scenario:  To maintain slab tree for disk, lets say 1 billion nodes, this design is aim for high fan-out.

 Since There're no parent pointer, no fence keys. So we maintain a cache to accellerate the look
 up for parent nodes.
 Since we support combinding cursor moving in Entry API (try to merge with previous or next adjacent
 node). But user can call `remove()` on moved cursor.

## Accelleration Search for finding the parent using PathCache

- Assume PathCache is for Node A, Node B is the right brother of node A. A's ptr is at ParentA[idx]
  - To find parent for Node B
    - If idx < last (Cap - 1), then A and B has common parent,
    - otherwise A and B have no common parent. Should continue iteration to upper PathCache. There will be common ancestor until idx < last

- Assume PathCache is for Node B, Node A is the left brother of node B, B's ptr is at ParentB[idx]
  - To find parent for Node A
    - If idx > 0, then A and B has common parent.
    - otherwise A and B have no common parent. Should continue interation to upper PathCache. There will be common ancestor until idx > 0

## Rebalance

- When insert on a full LeafNode, we try to move items to left/right brother, to delay split operation.

- One entry remvoved, current node usage < 50% (the threshold can be adjust according to tree size)

  - we don't need to borrow data from brothers (to avoid trashing), and we have already done borrowing on insert.

  - try to merge data, with left + current < cap, or current + right < cap, or left + current + right < 2 * cap

  - No need to mere 3 -> 1, because before reaching 30% average usage, we aleady checked 3 -> 2.


## Future ideas

- dynamicly incress InterNode size, or variable size
- borrow from leaf / right on InterNode split, increase fill ratio to 80%
- 2 - 3 split (increase fill ratio to 90%)
*/

use core::cell::UnsafeCell;
pub mod entry;
use entry::*;
mod node;
use node::*;
mod inter;
use inter::*;
mod leaf;
use leaf::*;

#[cfg(test)]
mod tests;

/// B+Tree Map for single-threaded use
pub struct BTreeMap<K: Ord + Clone + Sized, V: Sized> {
    /// Root node (may be null for empty tree)
    root: Option<Node<K, V>>,
    /// Number of elements in the tree
    len: usize,
    // use unsafe to avoid borrow problems
    cache: UnsafeCell<PathCache<K, V>>,
}

unsafe impl<K: Ord + Clone + Sized + Send, V: Sized + Send> Send for BTreeMap<K, V> {}
unsafe impl<K: Ord + Clone + Sized + Send, V: Sized + Send> Sync for BTreeMap<K, V> {}

impl<K: Ord + Sized + Clone, V: Sized> BTreeMap<K, V> {
    /// Create a new empty BTreeMap
    pub fn new() -> Self {
        Self { root: None, len: 0, cache: UnsafeCell::new(PathCache::<K, V>::new()) }
    }

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

    /// return (cap_of_inter_node, cap_of_leaf_node)
    #[inline]
    pub const fn cap() -> (u32, u32) {
        let inter_cap = InterNode::<K, V>::cap();
        let leaf_cap = LeafNode::<K, V>::cap();
        (inter_cap, leaf_cap)
    }

    /// When root is leaf, returns 1, otherwise return the number of layers of inter node
    #[inline(always)]
    pub fn height(&self) -> u32 {
        if let Some(Node::Inter(node)) = &self.root {
            return node.height() + 1;
        }
        1
    }

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
    fn update_parent_key(&mut self, leaf: LeafNode<K, V>) {
        let key = unsafe { (*leaf.key_ptr(0)).assume_init_ref().clone() };
        while let Some((parent, parent_idx)) = self.get_cache().pop() {
            if parent_idx > 0 {
                let parent_key = unsafe { (*parent.key_ptr(parent_idx - 1)).assume_init_mut() };
                *parent_key = key;
                return;
            }
            // if parent_idx == 0, this is the leftmost ptr in the InterNode, we go up until finding a
            // split key
        }
    }

    /// Insert with split handling - called when leaf is full
    fn insert_with_split(
        &mut self, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
    ) -> *mut V {
        debug_assert!(leaf.is_full().is_ok());
        let cap = LeafNode::<K, V>::cap();
        if idx < cap {
            // random insert, try borrow space from left and right
            if let Some(mut left_node) = leaf.get_left_node() {
                if let Err(_) = left_node.is_full() {
                    let (idx, _is_equal) = leaf.search(&key);
                    debug_assert!(!_is_equal);
                    let val_p = if idx == 0 {
                        // leaf is not change, but since the insert pos is leftmost of this node, mean parent
                        // separate_key <= key, need to update its separate_key
                        left_node.insert_no_split(key, value)
                    } else {
                        leaf.move_left(&mut left_node, 1);
                        leaf.insert_no_split(key, value)
                    };
                    self.update_parent_key(leaf);
                    return val_p;
                }
            }
        } else {
            // insert into empty new node, left is probably full, right is probably none
        }
        if let Some(mut right_node) = leaf.get_right_node() {
            if let Err(_) = right_node.is_full() {
                let (idx, _is_equal) = leaf.search(&key);
                debug_assert!(!_is_equal);
                let val_p = if idx == cap {
                    // leaf is not change, in this condition, right_node is the leftmost child
                    // of its parent, key < right_node.get_keys()[0]
                    right_node.insert_no_split_with_idx(0, key, value)
                } else {
                    leaf.move_right::<false>(&mut right_node, cap - 1, 1);
                    leaf.insert_no_split(key, value)
                };
                self.get_cache().move_right();
                self.update_parent_key(right_node);
                return val_p;
            }
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
        while let Some((mut parent, _idx)) = cache.pop() {
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
        K: core::fmt::Debug,
        V: core::fmt::Debug,
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
        K: core::fmt::Debug,
        V: core::fmt::Debug,
    {
        use core::ptr::NonNull;
        match node {
            Node::Leaf(leaf) => {
                print!("{:indent$}", "", indent = depth * 2);
                println!("{}", leaf);
            }
            Node::Inter(inter) => {
                print!("{:indent$}", "", indent = depth * 2);
                println!("{}", inter);
                // Dump children
                let count = inter.key_count() as u32;
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
        //            let leaf_count = leaf.key_count();
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
        //                    let sibling_count = left_sibling.key_count();
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
        //            let parent_count = parent.key_count() as u32;
        //            if leaf_idx < parent_count {
        //                let right_sibling_ptr = *parent.child_ptr(leaf_idx + 1);
        //                if !right_sibling_ptr.is_null() {
        //                    let mut right_sibling =
        //                        LeafNode::<K, V>::from_header(NonNull::new_unchecked(right_sibling_ptr));
        //                    let sibling_count = right_sibling.key_count();
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
    //            let sibling_count = left_sibling.key_count() as u32;
    //
    //            // Move last element from left sibling to front of leaf
    //            let key_to_move = (*left_sibling.key_ptr(sibling_count - 1)).assume_init_read();
    //            let val_to_move = (*left_sibling.value_ptr(sibling_count - 1)).assume_init_read();
    //
    //            // Shift leaf elements right
    //            let leaf_count = leaf.key_count() as u32;
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
    //            let leaf_count = leaf.key_count() as u32;
    //            (*leaf.key_ptr(leaf_count)).write(key_to_move);
    //            (*leaf.value_ptr(leaf_count)).write(val_to_move);
    //
    //            // Shift right sibling elements left
    //            let sibling_count = right_sibling.key_count() as u32;
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
    //            let left_count = left_sibling.key_count() as u32;
    //            let leaf_count = leaf.key_count() as u32;
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
    //            let leaf_count = leaf.key_count() as u32;
    //            let right_count = right_sibling.key_count() as u32;
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
    //            let count = parent.key_count() as u32;
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

impl<K: Ord + Clone + Sized, V: Sized> BTreeMap<K, V> {
    /// Validate the entire tree structure
    /// Uses the same traversal logic as Drop to avoid recursion
    #[cfg(test)]
    pub fn validate(&self)
    where
        K: core::fmt::Debug + Clone,
        V: core::fmt::Debug,
    {
        if self.root.is_none() {
            assert_eq!(self.len, 0, "Empty tree should have len 0");
            return;
        }

        let mut total_keys = 0usize;
        let mut prev_leaf_max: Option<K> = None;

        match &self.root {
            Some(Node::Leaf(leaf)) => {
                total_keys += leaf.validate(None, None);
            }
            Some(Node::Inter(inter)) => {
                // Do not use btree internal PathCache (might distrupt test scenario)
                let mut cache = PathCache::new();
                let mut cur = inter.clone();
                loop {
                    cache.push(cur.clone(), 0);
                    cur.validate();
                    match cur.get_child(0) {
                        Node::Leaf(leaf) => {
                            // Validate first leaf with no min/max bounds from parent
                            let min_key: Option<K> = None;
                            let max_key = if inter.key_count() > 0 {
                                unsafe { Some((*inter.key_ptr(0)).assume_init_ref().clone()) }
                            } else {
                                None
                            };
                            total_keys += leaf.validate(min_key.as_ref(), max_key.as_ref());
                            if let Some(ref prev_max) = prev_leaf_max {
                                let first_key = unsafe { (*leaf.key_ptr(0)).assume_init_ref() };
                                assert!(
                                    prev_max < first_key,
                                    "Leaf keys not in order: prev max {:?} >= current min {:?}",
                                    prev_max,
                                    first_key
                                );
                            }
                            prev_leaf_max = unsafe {
                                Some(
                                    (*leaf.key_ptr(leaf.key_count() as u32 - 1))
                                        .assume_init_ref()
                                        .clone(),
                                )
                            };
                            break;
                        }
                        Node::Inter(child_inter) => {
                            cur = child_inter;
                        }
                    }
                }

                // Continue traversal like Drop does
                while let Some((parent, idx)) =
                    cache.move_right_and_pop_l1(|_node| { /* post-visit callback */ })
                {
                    cache.push(parent.clone(), idx);
                    if let Node::Leaf(leaf) = parent.get_child(idx) {
                        // Calculate bounds for this leaf
                        let min_key = if idx > 0 {
                            unsafe {
                                Some((*parent.key_ptr((idx - 1) as u32)).assume_init_ref().clone())
                            }
                        } else {
                            None
                        };
                        let max_key = if (idx as u32) < parent.key_count() {
                            unsafe { Some((*parent.key_ptr(idx as u32)).assume_init_ref().clone()) }
                        } else {
                            None
                        };
                        total_keys += leaf.validate(min_key.as_ref(), max_key.as_ref());

                        // Check ordering with previous leaf
                        if let Some(ref prev_max) = prev_leaf_max {
                            let first_key = unsafe { (*leaf.key_ptr(0)).assume_init_ref() };
                            assert!(
                                prev_max < first_key,
                                "Leaf keys not in order: prev max {:?} >= current min {:?}",
                                prev_max,
                                first_key
                            );
                        }
                        prev_leaf_max = unsafe {
                            Some(
                                (*leaf.key_ptr(leaf.key_count() as u32 - 1))
                                    .assume_init_ref()
                                    .clone(),
                            )
                        };
                    } else {
                        unreachable!();
                    }
                }
            }
            None => unreachable!(),
        }

        assert_eq!(
            total_keys, self.len,
            "Total keys in tree ({}) doesn't match len ({})",
            total_keys, self.len
        );
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Drop for BTreeMap<K, V> {
    fn drop(&mut self) {
        let root = match self.root.take() {
            None => return,
            Some(Node::Leaf(mut leaf)) => unsafe {
                leaf.dealloc();
                return;
            },
            Some(Node::Inter(inter)) => inter,
        };
        let cache = self.get_cache();
        cache.clear();
        let mut cur = root;
        loop {
            cache.push(cur.clone(), 0);
            match cur.get_child(0) {
                Node::Leaf(mut leaf) => {
                    unsafe { leaf.dealloc() };
                    break;
                }
                Node::Inter(inter) => {
                    cur = inter;
                }
            }
        }
        // To navigate to next leaf,
        // return None when reach the end
        while let Some((parent, idx)) =
            cache.move_right_and_pop_l1(|mut node| unsafe { node.dealloc() })
        {
            cache.push(parent.clone(), idx);
            if let Node::Leaf(mut leaf) = parent.get_child(idx) {
                unsafe { leaf.dealloc() };
            } else {
                unreachable!();
            }
        }
    }
}
