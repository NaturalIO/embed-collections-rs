use super::*;

/// Entry for an existing key-value pair in the map
pub struct OccupiedEntry<'a, K: Ord + Clone + Sized, V: Sized> {
    pub(crate) map: &'a mut BTreeMap<K, V>,
    pub(crate) node: LeafNode<K, V>,
    pub(crate) idx: u32,
}

/// Entry for a vacant key position in the map
pub struct VacantEntry<'a, K: Ord + Clone + Sized, V: Sized> {
    pub(crate) map: &'a mut BTreeMap<K, V>,
    pub(crate) node: Option<LeafNode<K, V>>,
    pub(crate) key: K,
    pub(crate) idx: u32,
}

/// Entry into a BTreeMap for in-place manipulation
pub enum Entry<'a, K: Ord + Clone + Sized, V: Sized> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K: Ord + Clone + Sized, V: Sized> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K: Ord,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
        K: Ord,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => &entry.key,
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> OccupiedEntry<'a, K, V> {
    /// Get a reference to the key
    pub fn key(&self) -> &K {
        unsafe {
            let key_ptr = self.node.key_ptr(self.idx);
            (*key_ptr).assume_init_ref()
        }
    }

    /// Remove the key-value pair from the map and return the value
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Remove the key-value pair from the map and return the key and value
    pub fn remove_entry(mut self) -> (K, V) {
        unsafe {
            let key_ptr = self.node.key_ptr(self.idx);
            let val_ptr = self.node.value_ptr(self.idx);

            let key = (*key_ptr).assume_init_read();
            let val = (*val_ptr).assume_init_read();

            // Shift remaining elements
            let count = self.node.count() as u32;
            for i in self.idx..count - 1 {
                let src_key = self.node.key_ptr(i + 1);
                let dst_key = self.node.key_ptr(i);
                let k = (*src_key).assume_init_read();
                (*dst_key).write(k);

                let src_val = self.node.value_ptr(i + 1);
                let dst_val = self.node.value_ptr(i);
                let v = (*src_val).assume_init_read();
                (*dst_val).write(v);
            }

            // Update count
            self.node.get_header_mut().count -= 1;
            self.map.len -= 1;

            // Check for underflow and handle merge/borrow
            let new_count = self.node.count();
            let min_count = (LeafNode::<K, V>::cap() + 1) / 2;
            if new_count < min_count && self.map.root.is_some() {
                // Get cache from map to find parent
                let cache = self.map.get_cache();
                // Re-find the path to get fresh cache
                if let Some(root) = &self.map.root {
                    let _leaf = root.find_leaf_with_cache(cache, &key);
                    if !cache.is_empty() {
                        let parent = cache[cache.len() - 1].clone();
                        self.map.handle_leaf_underflow(parent, &mut self.node);
                    }
                }
            }

            (key, val)
        }
    }

    /// Get a reference to the value
    pub fn get(&self) -> &V {
        unsafe {
            let val_ptr = self.node.value_ptr(self.idx);
            (*val_ptr).assume_init_ref()
        }
    }

    /// Get a mutable reference to the value
    pub fn get_mut(&mut self) -> &mut V {
        unsafe {
            let val_ptr = self.node.value_ptr(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// Convert the OccupiedEntry into a mutable reference bounded by
    /// the map's lifetime
    pub fn into_mut(self) -> &'a mut V {
        unsafe {
            let val_ptr = self.node.value_ptr(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// replace a value into the map and return the old value
    pub fn insert(&mut self, value: V) -> V {
        unsafe {
            let val_ptr = self.node.value_ptr(self.idx);
            let old = (*val_ptr).assume_init_read();
            (*val_ptr).write(value);
            old
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> VacantEntry<'a, K, V> {
    /// Get a reference to the key
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key
    pub fn into_key(self) -> K {
        self.key
    }

    /// Insert a value into the map
    pub fn insert(self, value: V) -> &'a mut V {
        let (key, map, idx) = (self.key, self.map, self.idx);
        if map.root.is_none() {
            unsafe {
                // empty tree
                let mut leaf = LeafNode::<K, V>::alloc();
                map.root = Some(Node::Leaf(leaf.clone()));
                map.len = 1;
                return &mut *leaf.insert_no_split_with_idx(0, key, value);
            }
        }
        // Get the leaf node where we should insert
        let mut leaf = self.node.expect("VacantEntry should have a node when root is not None");
        let count = leaf.count() as u32;
        // Check if leaf has space
        let value_p = if count < LeafNode::<K, V>::cap() as u32 {
            map.len += 1;
            leaf.insert_no_split_with_idx(idx, key, value)
        } else {
            // Leaf is full, need to split
            map.insert_with_split(key, value, leaf, idx)
        };
        unsafe { &mut *value_p }
    }
}
