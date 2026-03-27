//! B+Tree Map - A cache-optimized B+Tree for single-threaded use.
//!
//! This B+Tree is designed for CPU cache efficiency:
//! - Nodes are aligned to 4 cache lines (256 bytes on x86_64)
//! - Keys stored in first 128B (with header), Values/pointers stored in last 128B
//! - No parent pointers (path stored during descent)
//! - Linear search within nodes, respecting cacheline boundaries
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::ptr::NonNull;
mod entry;
pub use entry::*;
mod node;
use node::*;
/// B+Tree Map for single-threaded use
pub struct BTreeMap<K, V> {
    /// Root node (may be null for empty tree)
    root: Option<Node<K, V>>,
    /// Number of elements in the tree
    len: usize,
    // use unsafe to avoid borrow problems
    cache: UnsafeCell<Vec<InterNode<K, V>>>,
}
unsafe impl<K: Send, V: Send> Send for BTreeMap<K, V> {}
unsafe impl<K: Send, V: Send> Sync for BTreeMap<K, V> {}
impl<K, V> BTreeMap<K, V> {
    /// Create a new empty BTreeMap
    pub const fn new() -> Self {
        Self { root: None, len: 0, cache: UnsafeCell::new(Vec::new()) }
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
    #[inline(always)]
    fn get_cache(&self) -> &mut Vec<InterNode<K, V>> {
        unsafe {
            let cache = &mut *self.cache.get();
            cache.set_len(0);
            cache
        }
    }
}
impl<K, V> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K, V> Drop for BTreeMap<K, V> {
    fn drop(&mut self) {
        if let Some(root) = &mut self.root {
            match root {
                Node::Inter(node) => {
                    // recursive drop
                    todo!();
                    //unsafe{node.dealloc()};
                }
                Node::Leaf(node) => unsafe { node.dealloc() },
            }
        }
    }
}
// Main operations
impl<K: Ord + Sized, V: Sized> BTreeMap<K, V> {
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
    /// Returns true if the map contains the key
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
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
    pub(crate) fn insert_with_split(
        &mut self, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
    ) -> &mut V {
        unsafe {
            let cache = self.get_cache();
            let leaf_count = leaf.count() as u32;
            let cap = LeafNode::<K, V>::cap() as u32;
            // Create new leaf
            let mut new_leaf = LeafNode::<K, V>::alloc();
            // Calculate split point
            let split_idx = (leaf_count + 1) / 2;
            // Determine where the new key should go
            let insert_into_left = idx <= split_idx;
            // Move keys and values from split_idx onwards to new leaf
            let new_count = leaf_count - split_idx;
            for i in 0..new_count {
                let src_key = leaf.key_ptr(split_idx + i);
                let dst_key = new_leaf.key_ptr(i);
                let k = (*src_key).assume_init_read();
                (*dst_key).write(k);
                let src_val = leaf.value_ptr(split_idx + i);
                let dst_val = new_leaf.value_ptr(i);
                let v = (*src_val).assume_init_read();
                (*dst_val).write(v);
            }
            // Update counts
            leaf.get_header_mut().count = split_idx;
            new_leaf.get_header_mut().count = new_count;
            // Update leaf links
            let old_next = (*leaf.brothers()).next;
            (*new_leaf.brothers()).prev = leaf.header().as_ptr();
            (*new_leaf.brothers()).next = old_next;
            (*leaf.brothers()).next = new_leaf.header().as_ptr();
            if !old_next.is_null() {
                (*LeafNode::<K, V>::from_header(NonNull::new_unchecked(old_next)).brothers())
                    .prev = new_leaf.header().as_ptr();
            }
            // Now insert the new key-value into the appropriate leaf
            let (target_leaf, target_idx) =
                if insert_into_left { (&mut leaf, idx) } else { (&mut new_leaf, idx - split_idx) };
            // Insert into target leaf
            let target_count = target_leaf.count() as u32;
            for i in (target_idx..target_count).rev() {
                let src_key = target_leaf.key_ptr(i);
                let dst_key = target_leaf.key_ptr(i + 1);
                let k = (*src_key).assume_init_read();
                (*dst_key).write(k);
                let src_val = target_leaf.value_ptr(i);
                let dst_val = target_leaf.value_ptr(i + 1);
                let v = (*src_val).assume_init_read();
                (*dst_val).write(v);
            }
            let key_ptr = target_leaf.key_ptr(target_idx);
            let val_ptr = target_leaf.value_ptr(target_idx);
            (*key_ptr).write(key);
            (*val_ptr).write(value);
            target_leaf.get_header_mut().count += 1;
            // Get first key of new leaf for parent
            let split_key_ptr = new_leaf.key_ptr(0);
            let split_key = (*split_key_ptr).assume_init_read();
            // Propagate split up the tree - need to clone cache first to avoid borrow issues
            let cache_clone: Vec<_> = cache.clone();
            self.propagate_split(&cache_clone, split_key, new_leaf, &leaf);
            self.len += 1;
            // Return reference to inserted value
            (*val_ptr).assume_init_mut()
        }
    }
    /// Propagate node split up the tree
    unsafe fn propagate_split(
        &mut self, cache: &[InterNode<K, V>], key: K, right_child: LeafNode<K, V>,
        left_child: &LeafNode<K, V>,
    ) {
        unsafe {
            // Check if we need to create a new root
            if cache.is_empty() {
                // Create new root
                let mut new_root = InterNode::<K, V>::alloc(1);
                let key_ptr = new_root.key_ptr(0);
                (*key_ptr).write(key);
                new_root.get_header_mut().count = 1;
                // Set children
                *new_root.child_ptr(0) = left_child.header().as_ptr();
                *new_root.child_ptr(1) = right_child.header().as_ptr();
                self.root = Some(Node::Inter(new_root));
                return;
            }
            // Get parent from cache
            let parent_idx = cache.len() - 1;
            let mut parent = cache[parent_idx].clone();
            // Find which child index corresponds to left_child
            let child_idx = self.find_child_index(&parent, left_child.header().as_ptr());
            let parent_count = parent.count() as u32;
            let parent_cap = InterNode::<K, V>::cap() as u32;
            // Check if parent has space
            if parent_count < parent_cap {
                // Shift and insert
                for i in (child_idx..parent_count).rev() {
                    let src_key = parent.key_ptr(i);
                    let dst_key = parent.key_ptr(i + 1);
                    let k = (*src_key).assume_init_read();
                    (*dst_key).write(k);
                    let child = *parent.child_ptr(i + 1);
                    *parent.child_ptr(i + 2) = child;
                }
                let key_ptr = parent.key_ptr(child_idx);
                (*key_ptr).write(key);
                *parent.child_ptr(child_idx + 1) = right_child.header().as_ptr();
                parent.get_header_mut().count += 1;
                return;
            }
            // Parent is full, need to split internal node
            self.split_internal_and_propagate(
                &cache[..parent_idx],
                parent,
                child_idx,
                key,
                right_child.header().as_ptr(),
            );
        }
    }
    /// Find child index in parent
    unsafe fn find_child_index(&self, parent: &InterNode<K, V>, child_ptr: *mut NodeHeader) -> u32 {
        unsafe {
            let count = parent.count() as u32;
            for i in 0..=count {
                if *parent.child_ptr(i) == child_ptr {
                    return i;
                }
            }
            panic!("Child not found in parent");
        }
    }
    /// Split internal node and propagate up
    unsafe fn split_internal_and_propagate(
        &mut self, parent_cache: &[InterNode<K, V>], mut parent: InterNode<K, V>, child_idx: u32,
        key: K, right_child_ptr: *mut NodeHeader,
    ) {
        unsafe {
            let parent_count = parent.count() as u32;
            let split_idx = parent_count / 2;
            // Create new internal node with same height
            let mut new_internal = InterNode::<K, V>::alloc(parent.height());
            // The key at split_idx goes up to parent
            let promote_key_ptr = parent.key_ptr(split_idx);
            let promote_key = (*promote_key_ptr).assume_init_read();
            // Move keys after split_idx to new node
            let new_count = parent_count - split_idx - 1;
            for i in 0..new_count {
                let src_key = parent.key_ptr(split_idx + 1 + i);
                let dst_key = new_internal.key_ptr(i);
                let k = (*src_key).assume_init_read();
                (*dst_key).write(k);
            }
            // Move children after split_idx to new node
            for i in 0..=new_count {
                let child = *parent.child_ptr(split_idx + 1 + i);
                *new_internal.child_ptr(i) = child;
            }
            // Update counts
            parent.get_header_mut().count = split_idx;
            new_internal.get_header_mut().count = new_count;
            // Now insert the new key and child into appropriate node
            let insert_into_left = child_idx <= split_idx;
            if insert_into_left {
                // Insert into left node
                for i in (child_idx..split_idx).rev() {
                    let src_key = parent.key_ptr(i);
                    let dst_key = parent.key_ptr(i + 1);
                    let k = (*src_key).assume_init_read();
                    (*dst_key).write(k);
                    let child = *parent.child_ptr(i + 1);
                    *parent.child_ptr(i + 2) = child;
                }
                let key_ptr = parent.key_ptr(child_idx);
                (*key_ptr).write(key);
                *parent.child_ptr(child_idx + 1) = right_child_ptr;
                parent.get_header_mut().count += 1;
            } else {
                // Insert into right node
                let right_insert_pos = child_idx - split_idx - 1;
                for i in (right_insert_pos..new_count).rev() {
                    let src_key = new_internal.key_ptr(i);
                    let dst_key = new_internal.key_ptr(i + 1);
                    let k = (*src_key).assume_init_read();
                    (*dst_key).write(k);
                    let child = *new_internal.child_ptr(i + 1);
                    *new_internal.child_ptr(i + 2) = child;
                }
                let key_ptr = new_internal.key_ptr(right_insert_pos);
                (*key_ptr).write(key);
                *new_internal.child_ptr(right_insert_pos + 1) = right_child_ptr;
                new_internal.get_header_mut().count += 1;
            }
            // Propagate the promoted key up
            if parent_cache.is_empty() {
                // Create new root
                let mut new_root = InterNode::<K, V>::alloc(parent.height() + 1);
                let key_ptr = new_root.key_ptr(0);
                (*key_ptr).write(promote_key);
                new_root.get_header_mut().count = 1;
                *new_root.child_ptr(0) = parent.header().as_ptr();
                *new_root.child_ptr(1) = new_internal.header().as_ptr();
                self.root = Some(Node::Inter(new_root));
            } else {
                // Recursively propagate up
                let grandparent_idx = parent_cache.len() - 1;
                let mut grandparent = parent_cache[grandparent_idx].clone();
                let parent_child_idx =
                    self.find_child_index(&grandparent, parent.header().as_ptr());
                let grandparent_count = grandparent.count() as u32;
                let grandparent_cap = InterNode::<K, V>::cap() as u32;
                if grandparent_count < grandparent_cap {
                    // Grandparent has space
                    for i in (parent_child_idx..grandparent_count).rev() {
                        let src_key = grandparent.key_ptr(i);
                        let dst_key = grandparent.key_ptr(i + 1);
                        let k = (*src_key).assume_init_read();
                        (*dst_key).write(k);
                        let child = *grandparent.child_ptr(i + 1);
                        *grandparent.child_ptr(i + 2) = child;
                    }
                    let key_ptr = grandparent.key_ptr(parent_child_idx);
                    (*key_ptr).write(promote_key);
                    *grandparent.child_ptr(parent_child_idx + 1) = new_internal.header().as_ptr();
                    grandparent.get_header_mut().count += 1;
                } else {
                    // Need to split further up
                    self.split_internal_and_propagate(
                        &parent_cache[..grandparent_idx],
                        grandparent,
                        parent_child_idx,
                        promote_key,
                        new_internal.header().as_ptr(),
                    );
                }
            }
        }
    }
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
}
