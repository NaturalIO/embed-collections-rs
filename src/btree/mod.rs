//! B+Tree Map - A cache-optimized B+Tree for single-threaded use.
//!
//! This B+Tree is designed for CPU cache efficiency:
//! - Nodes are aligned to 4 cache lines (256 bytes on x86_64)
//! - Keys stored in first 128B (with header), Values/pointers stored in last 128B
//! - No parent pointers (path stored during descent)
//! - Linear search within nodes, respecting cacheline boundaries

use alloc::vec::Vec;
use core::cell::UnsafeCell;
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
}
