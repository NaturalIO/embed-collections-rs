use super::iter::{IterBackward, IterForward};
use super::{stats::Stats, *};
use core::fmt::{self, Debug};

/// Entry for an existing key-value pair in the tree
pub struct OccupiedEntry<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> {
    pub(super) inner: &'a mut S::EntryInner<V>,
    pub(super) leaf: LeafNode<K, V>,
    pub(super) idx: u8,
}

/// Entry for a vacant key position in the tree
pub struct VacantEntry<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> {
    pub(super) inner: &'a mut S::EntryInner<V>,
    pub(super) leaf: Option<LeafNode<K, V>>,
    pub(super) key: K,
    pub(super) idx: u8,
}

/// Entry into a BTreeMap for in-place manipulation
pub enum Entry<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> {
    Occupied(OccupiedEntry<'a, K, V, S>),
    Vacant(VacantEntry<'a, K, V, S>),
}

impl<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> Entry<'a, K, V, S> {
    #[inline]
    pub fn exists(&self) -> bool {
        matches!(self, Entry::Occupied(_))
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K: Ord + 'a,
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
        K: Ord + 'a,
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
    pub fn move_backward(self) -> Result<OccupiedEntry<'a, K, V, S>, Self> {
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
    pub fn move_forward(self) -> Result<OccupiedEntry<'a, K, V, S>, Self> {
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
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_backward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
        match self {
            Entry::Occupied(ent) => ent.peek_backward(),
            Entry::Vacant(ent) => ent.peek_backward(),
        }
    }

    /// Peak the next OccupiedEntry
    #[inline(always)]
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_forward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
        match self {
            Entry::Occupied(ent) => ent.peek_forward(),
            Entry::Vacant(ent) => ent.peek_forward(),
        }
    }
}

impl<'a, K: Ord + Clone + Sized + Debug, V: Sized + Debug, S: Stats<K>> Debug
    for OccupiedEntry<'a, K, V, S>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry").field("key", self.key()).field("value", self.get()).finish()
    }
}

impl<'a, K: Ord + Clone + Sized + Debug, V: Sized + Debug, S: Stats<K>> Debug
    for VacantEntry<'a, K, V, S>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry").field("key", &self.key).finish()
    }
}

impl<'a, K: Ord + Clone + Sized + Debug, V: Sized + Debug, S: Stats<K>> Debug
    for Entry<'a, K, V, S>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Occupied(ent) => f.debug_tuple("Occupied").field(ent).finish(),
            Entry::Vacant(ent) => f.debug_tuple("Vacant").field(ent).finish(),
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> OccupiedEntry<'a, K, V, S> {
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
        let (tree, cache) = self.inner.get_tree_cache();
        tree.len -= 1;
        // Check for underflow and handle merge
        let new_count = self.leaf.key_count();
        let min_count = LeafNode::<K, V>::cap() >> 1;
        if new_count < min_count && tree.root_is_inter() {
            // The cache should already contain the path from the entry lookup
            tree.handle_leaf_underflow(cache, self.leaf, merge);
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
            let val_ptr = self.leaf.value_ptr_mut(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// Convert the OccupiedEntry into a mutable reference bounded by
    /// the tree's lifetime
    #[inline]
    pub fn into_mut(mut self) -> &'a mut V {
        unsafe {
            let val_ptr = self.leaf.value_ptr_mut(self.idx);
            (*val_ptr).assume_init_mut()
        }
    }

    /// replace a value into the tree and return the old value
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        self.leaf.replace(self.idx, value)
    }

    /// Peak previous OccupiedEntry
    #[inline(always)]
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_backward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
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
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_forward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
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
        if self.idx > 0 {
            Ok(Self { inner: self.inner, leaf: self.leaf, idx: self.idx - 1 })
        } else if let Some(leaf) = self.leaf.get_left_node() {
            self.inner.get_cache().move_path_left();
            let count = leaf.key_count();
            debug_assert!(count > 0);
            Ok(Self { inner: self.inner, leaf, idx: count - 1 })
        } else {
            Err(self)
        }
    }

    /// Move to next OccupiedEntry
    ///
    /// When reaching the end, return the original entry in Err()
    #[inline]
    pub fn move_forward(self) -> Result<Self, Self> {
        let next_idx = self.idx + 1;
        if self.leaf.key_count() > next_idx {
            Ok(Self { inner: self.inner, leaf: self.leaf, idx: next_idx })
        } else if let Some(right) = self.leaf.get_right_node() {
            self.inner.get_cache().move_path_right();
            debug_assert!(right.key_count() > 0);
            Ok(Self { inner: self.inner, leaf: right, idx: 0 })
        } else {
            Err(self)
        }
    }

    /// Try to alter the key of this entry
    ///
    /// On successful returns  Ok() ;
    /// If key is not in strict order among the neighbors, return  Err() .
    #[inline]
    pub fn alter_key(&mut self, k: K) -> Result<(), ()> {
        if let Some((_k, _v)) = self.peek_backward()
            && _k >= &k
        {
            return Err(());
        }
        if let Some((_k, _v)) = self.peek_forward()
            && _k <= &k
        {
            return Err(());
        }
        unsafe {
            let k_ref = (*self.leaf.key_ptr_mut(self.idx)).assume_init_mut();
            let (tree, cache) = self.inner.get_tree_cache();
            if self.idx == 0 && tree.root_is_inter() {
                // We need to keep the PathBuffer intact, use peek rather than move_to_ancestor
                // it's allowed to move the entry or remove afterwards
                tree.update_ancestor_sep_key::<false, _>(cache, k.clone());
            }
            *k_ref = k;
            Ok(())
        }
    }

    #[cfg(test)]
    pub(crate) fn validate_cache_path(&self) {
        let k = self.leaf.get_keys()[self.idx as usize].clone();
        if let Some(root) = self.inner.get_tree().get_root() {
            self.inner.get_cache().fix_path_center();
            let backup = self.inner.get_cache().to_vec();
            let mut _stats = S::default();
            let cache = _stats.get_cache(root.height() as u8);
            let _leaf = self
                .inner
                .get_tree()
                .search_leaf_with(|inter| inter.find_leaf_with_cache::<V, _, _>(&cache, &k))
                .unwrap();
            assert_eq!(self.leaf, _leaf);
            assert_eq!(backup, cache.to_vec());
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized, S: Stats<K>> VacantEntry<'a, K, V, S> {
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
    pub fn insert(self, value: V) -> &'a mut V
    where
        K: 'a,
    {
        let (key, inner, idx) = (self.key, self.inner, self.idx);
        let (tree, cache) = inner.get_tree_cache();
        if tree.root.is_none() {
            return inner.get_tree_mut().init_empty(key, value);
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
            tree.insert_with_split(cache, key, value, leaf, idx)
            // NOTE: the PathBuffer might be a different path with the one inserted,
            // because borrowing on inter node might happen, and the cache is consumed during
            // propagate_split moves upwards.
            // It's too complex to provide returning OccupiedEntry because the subsequence operation
            // relies on a correct PathBuffer
        };
        unsafe { &mut *value_p }
    }

    /// Peak previous OccupiedEntry
    #[inline(always)]
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_backward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
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
    #[allow(clippy::needless_lifetimes)]
    pub fn peek_forward<'b>(&'b self) -> Option<(&'b K, &'b V)> {
        if let Some(leaf) = self.leaf.as_ref() {
            unsafe {
                if let Some((k, v)) = leaf.get_raw_pair(self.idx) {
                    // get_raw_pair will validate idx
                    return Some((&*k, &*v));
                }
                if let Some(right) = leaf.get_right_node()
                    && let Some((k, v)) = right.get_raw_pair(0)
                {
                    return Some((&*k, &*v));
                }
            }
        }
        None
    }

    /// Move to previous OccupiedEntry
    ///
    /// When reaching the front return the original entry in Err()
    #[inline]
    pub fn move_backward(self) -> Result<OccupiedEntry<'a, K, V, S>, Self> {
        if let Some(leaf) = self.leaf.as_ref() {
            // The key of previous pos is always smaller than self.key ;
            // the key at current idx (if exists) must larger than self.key.
            // It's possible the leaf.idx may be == leaf.key_count(), but it's the same.
            if self.idx > 0 {
                return Ok(OccupiedEntry {
                    inner: self.inner,
                    leaf: leaf.clone(),
                    idx: self.idx - 1,
                });
            }
            if let Some(left) = leaf.get_left_node() {
                let count = left.key_count();
                debug_assert!(count > 0);
                self.inner.get_cache().move_path_left();
                return Ok(OccupiedEntry { inner: self.inner, leaf: left, idx: count - 1 });
            }
        }
        Err(self)
    }

    /// Move to next OccupiedEntry
    ///
    /// When reaching the end, return the original entry in Err()
    #[inline]
    pub fn move_forward(self) -> Result<OccupiedEntry<'a, K, V, S>, Self> {
        if let Some(leaf) = self.leaf.as_ref() {
            if leaf.key_count() > self.idx {
                // the key at current idx (if exists) must larger than self.key, no need to move
                return Ok(OccupiedEntry { inner: self.inner, leaf: leaf.clone(), idx: self.idx });
            } else if let Some(right) = leaf.get_right_node() {
                debug_assert!(right.key_count() > 0);
                self.inner.get_cache().move_path_right();
                return Ok(OccupiedEntry { inner: self.inner, leaf: right, idx: 0 });
            }
        }
        Err(self)
    }
}
