use super::iter::{IterBackward, IterForward};
use super::*;
use core::fmt;

/// Entry for an existing key-value pair in the tree
pub struct OccupiedEntry<'a, K: Ord + Clone + Sized, V: Sized> {
    pub(super) tree: &'a mut BTreeMap<K, V>,
    pub(super) leaf: LeafNode<K, V>,
    pub(super) idx: u32,
}

/// Entry for a vacant key position in the tree
pub struct VacantEntry<'a, K: Ord + Clone + Sized, V: Sized> {
    pub(super) tree: &'a mut BTreeMap<K, V>,
    pub(super) leaf: Option<LeafNode<K, V>>,
    pub(super) key: K,
    pub(super) idx: u32,
}

/// Entry into a BTreeMap for in-place manipulation
pub enum Entry<'a, K: Ord + Clone + Sized, V: Sized> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K: Ord + Clone + Sized, V: Sized> Entry<'a, K, V> {
    #[inline]
    pub fn exists(&self) -> bool {
        matches!(self, Entry::Occupied(_))
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => &entry.key,
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the tree.
    #[inline]
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

    // NOTE: Since rust does not alloc multiple mutable borrow, the moving api should assume ownership

    /// Move to previous OccupiedEntry
    ///
    /// When reaching the front, return the original entry in Err()
    #[inline]
    pub fn move_backward(self) -> Result<OccupiedEntry<'a, K, V>, Self> {
        match self {
            Entry::Occupied(ent) => match ent.move_backward() {
                Ok(_ent) => Ok(_ent),
                Err(_ent) => Err(Entry::Occupied(_ent)),
            },
            Entry::Vacant(ent) => match ent.move_backward() {
                Ok(_ent) => Ok(_ent),
                Err(_ent) => Err(Entry::Vacant(_ent)),
            },
        }
    }

    /// Move to next OccupiedEntry
    ///
    /// When reaching the end, return the original entry in Err()
    #[inline]
    pub fn move_forward(self) -> Result<OccupiedEntry<'a, K, V>, Self> {
        match self {
            Entry::Occupied(ent) => match ent.move_forward() {
                Ok(_ent) => Ok(_ent),
                Err(_ent) => Err(Entry::Occupied(_ent)),
            },
            Entry::Vacant(ent) => match ent.move_forward() {
                Ok(_ent) => Ok(_ent),
                Err(_ent) => Err(Entry::Vacant(_ent)),
            },
        }
    }

    /// Peak previous OccupiedEntry
    #[inline(always)]
    pub fn peak_backward(&self) -> Option<(&'a K, &'a V)> {
        match self {
            Entry::Occupied(ent) => ent.peak_backward(),
            Entry::Vacant(ent) => ent.peak_backward(),
        }
    }

    /// Peak the next OccupiedEntry
    #[inline(always)]
    pub fn peak_forward(&self) -> Option<(&'a K, &'a V)> {
        match self {
            Entry::Occupied(ent) => ent.peak_forward(),
            Entry::Vacant(ent) => ent.peak_forward(),
        }
    }
}

impl<'a, K: Ord + Clone + Sized + fmt::Debug, V: Sized + fmt::Debug> fmt::Debug
    for OccupiedEntry<'a, K, V>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry").field("key", self.key()).field("value", self.get()).finish()
    }
}

impl<'a, K: Ord + Clone + Sized + fmt::Debug, V: Sized + fmt::Debug> fmt::Debug
    for VacantEntry<'a, K, V>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry").field("key", &self.key).finish()
    }
}

impl<'a, K: Ord + Clone + Sized + fmt::Debug, V: Sized + fmt::Debug> fmt::Debug
    for Entry<'a, K, V>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Occupied(ent) => f.debug_tuple("Occupied").field(ent).finish(),
            Entry::Vacant(ent) => f.debug_tuple("Vacant").field(ent).finish(),
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> OccupiedEntry<'a, K, V> {
    /// Get a reference to the key
    #[inline]
    pub fn key(&self) -> &K {
        unsafe {
            let key_ptr = self.leaf.key_ptr(self.idx);
            (*key_ptr).assume_init_ref()
        }
    }

    /// Remove the key-value pair from the tree and return the value
    #[inline(always)]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Remove the key-value pair from the tree and return the key and value
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        self._remove_entry(true)
    }

    /// Remove the key-value pair from the tree and return the key and value
    #[inline(always)]
    pub(crate) fn _remove_entry(mut self, merge: bool) -> (K, V) {
        let (key, val) = self.leaf.remove_pair_no_borrow(self.idx);
        self.tree.len -= 1;
        // Check for underflow and handle merge
        let new_count = self.leaf.key_count();
        let min_count = LeafNode::<K, V>::cap() >> 1;
        if new_count < min_count && !self.tree.get_root_unwrap().is_leaf() {
            // The cache should already contain the path from the entry lookup
            self.tree.handle_leaf_underflow(self.leaf, merge);
        }
        (key, val)
    }

    /// Get a reference to the value
    #[inline]
    pub fn get(&self) -> &V {
        unsafe {
            let val_ptr = self.leaf.value_ptr(self.idx);
            (*val_ptr).assume_init_ref()
        }
    }

    /// Get a mutable reference to the value
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe {
            let val_ptr = self.leaf.value_ptr(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// Convert the OccupiedEntry into a mutable reference bounded by
    /// the tree's lifetime
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        unsafe {
            let val_ptr = self.leaf.value_ptr(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// replace a value into the tree and return the old value
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        unsafe {
            let val_ptr = self.leaf.value_ptr(self.idx);
            let old = (*val_ptr).assume_init_read();
            (*val_ptr).write(value);
            old
        }
    }

    /// Peak previous OccupiedEntry
    #[inline(always)]
    pub fn peak_backward(&self) -> Option<(&'a K, &'a V)> {
        let mut cursor = IterBackward { back_leaf: self.leaf.clone(), back_idx: self.idx };
        unsafe {
            if let Some((k, v)) = cursor.prev_pair() {
                return Some((&*k, &*v));
            }
        }
        None
    }

    /// Peak the next OccupiedEntry
    #[inline(always)]
    pub fn peak_forward(&self) -> Option<(&'a K, &'a V)> {
        let mut cursor = IterForward { front_leaf: self.leaf.clone(), idx: self.idx + 1 };
        unsafe {
            if let Some((k, v)) = cursor.next_pair() {
                return Some((&*k, &*v));
            }
        }
        None
    }

    /// Move to previous OccupiedEntry
    ///
    /// When reaching the front, return the original entry in Err()
    #[inline]
    pub fn move_backward(self) -> Result<Self, Self> {
        let mut cursor = IterBackward { back_leaf: self.leaf.clone(), back_idx: self.idx };
        if let Some((prev_leaf, idx)) = cursor.prev() {
            self.tree.get_cache().move_left();
            return Ok(Self { tree: self.tree, leaf: prev_leaf.clone(), idx });
        }
        Err(self)
    }

    /// Move to next OccupiedEntry
    ///
    /// When reaching the end, return the original entry in Err()
    #[inline]
    pub fn move_forward(self) -> Result<Self, Self> {
        let mut cursor = IterForward { front_leaf: self.leaf.clone(), idx: self.idx + 1 };
        if let Some((next_leaf, idx)) = cursor.next() {
            self.tree.get_cache().move_right();
            return Ok(Self { tree: self.tree, leaf: next_leaf.clone(), idx });
        }
        Err(self)
    }

    /// Try to alter the key of this entry
    ///
    /// On successful returns  Ok() ;
    /// If key is not in strict order among the neighbors, return  Err() .
    #[inline]
    pub fn alter_key(&mut self, k: K) -> Result<(), ()> {
        if let Some((_k, _v)) = self.peak_backward() {
            if _k >= &k {
                return Err(());
            }
        }
        if let Some((_k, _v)) = self.peak_forward() {
            if _k <= &k {
                return Err(());
            }
        }
        unsafe {
            let k_ref = (*self.leaf.key_ptr(self.idx)).assume_init_mut();
            if self.idx == 0 {
                self.tree.update_ancestor_sep_key::<false>(k.clone());
            }
            *k_ref = k;
            Ok(())
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> VacantEntry<'a, K, V> {
    /// Get a reference to the key
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key
    #[inline]
    pub fn into_key(self) -> K {
        self.key
    }

    /// Insert a value into the tree
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let (key, tree, idx) = (self.key, self.tree, self.idx);
        if tree.root.is_none() {
            unsafe {
                // empty tree
                let mut leaf = LeafNode::<K, V>::alloc();
                tree.root = Some(Node::Leaf(leaf.clone()));
                tree.len = 1;
                tree.leaf_count += 1;
                return &mut *leaf.insert_no_split_with_idx(0, key, value);
            }
        }
        tree.len += 1;
        // Get the leaf node where we should insert
        let mut leaf = self.leaf.expect("VacantEntry should have a node when root is not None");
        let count = leaf.key_count();
        // Check if leaf has space
        let value_p = if count < LeafNode::<K, V>::cap() {
            leaf.insert_no_split_with_idx(idx, key, value)
        } else {
            // Leaf is full, need to split
            tree.insert_with_split(key, value, leaf, idx)
            // NOTE: the PathCache might be a different path with the one inserted,
            // because borrowing on inter node might happen, and the cache is consumed during
            // propagate_split moves upwards.
            // It's too complex to provide returning OccupiedEntry because the subsequence operation
            // relies on a correct PathCache
        };
        unsafe { &mut *value_p }
    }

    /// Peak previous OccupiedEntry
    #[inline(always)]
    pub fn peak_backward(&self) -> Option<(&'a K, &'a V)> {
        if let Some(leaf) = self.leaf.as_ref() {
            // The key of previous pos is always smaller than self.key ;
            // the key at current idx (if exists) must larger than self.key.
            let mut cursor = IterBackward { back_leaf: leaf.clone(), back_idx: self.idx };
            unsafe {
                if let Some((k, v)) = cursor.prev_pair() {
                    return Some((&*k, &*v));
                }
            }
        }
        None
    }

    /// Peak the next OccupiedEntry
    #[inline(always)]
    pub fn peak_forward(&self) -> Option<(&'a K, &'a V)> {
        if let Some(leaf) = self.leaf.as_ref() {
            unsafe {
                if let Some((k, v)) = leaf.get_raw_pair(self.idx) {
                    return Some((&*k, &*v));
                }
                if let Some(right) = leaf.get_right_node() {
                    if let Some((k, v)) = right.get_raw_pair(0) {
                        return Some((&*k, &*v));
                    }
                }
            }
        }
        None
    }

    /// Move to previous OccupiedEntry
    ///
    /// When reaching the front return the original entry in Err()
    #[inline]
    pub fn move_backward(self) -> Result<OccupiedEntry<'a, K, V>, Self> {
        if let Some(leaf) = self.leaf.as_ref() {
            let mut cursor = IterBackward { back_leaf: leaf.clone(), back_idx: self.idx };
            // The key of previous pos is always smaller than self.key ;
            // the key at current idx (if exists) must larger than self.key.
            // Be aware the leaf.idx may be larger than leaf.key_count(), but IterBackward
            // does not care.
            if cursor.prev().is_some() {
                self.tree.get_cache().move_left();
                return Ok(OccupiedEntry {
                    tree: self.tree,
                    leaf: cursor.back_leaf.clone(),
                    idx: cursor.back_idx,
                });
            }
        }
        Err(self)
    }

    /// Move to next OccupiedEntry
    ///
    /// When reaching the end, return the original entry in Err()
    #[inline]
    pub fn move_forward(self) -> Result<OccupiedEntry<'a, K, V>, Self> {
        if let Some(leaf) = self.leaf.as_ref() {
            if leaf.key_count() > self.idx {
                return Ok(OccupiedEntry { tree: self.tree, leaf: leaf.clone(), idx: self.idx });
            } else if let Some(right) = leaf.get_right_node() {
                debug_assert!(right.key_count() > 0);
                self.tree.get_cache().move_right();
                return Ok(OccupiedEntry { tree: self.tree, leaf: right, idx: 0 });
            }
        }
        Err(self)
    }
}
