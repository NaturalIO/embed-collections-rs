use super::iter::{IterBackward, IterForward};
use super::*;
use core::marker::PhantomData;

/// A read-only cursor for navigating through entries in a BTreeMap.
///
/// The cursor provides bidirectional navigation using leaf node sibling pointers,
/// you can change where the direction goes at any time.
///
/// `Cursor` is lighter than [Iter] (without the cost of DoubleEndedIterator trait) and more customizable.
///
/// # Example
///
/// ```
/// use embed_collections::BTreeMap;
///
/// let mut map = BTreeMap::new();
/// map.insert(1, "a");
/// map.insert(3, "b");
/// map.insert(5, "c");
///
/// // Create cursor at key 2
/// let mut cursor = map.cursor(&1);
/// assert_eq!(cursor.next(), Some((&1, &"a")));
/// assert_eq!(cursor.next(), Some((&3, &"b")));
/// assert_eq!(cursor.next(), Some((&5, &"c")));
/// assert_eq!(cursor.next(), None);
///
/// let mut cursor = map.cursor(&2);
/// // return next existing key
/// assert_eq!(cursor.next(), Some((&3, &"b")));
/// assert_eq!(cursor.next(), Some((&5, &"c")));
///
/// // Peek without moving
/// assert_eq!(cursor.peek_forward(), None);
/// assert_eq!(cursor.peek_backward(), Some((&5, &"c")));
/// assert_eq!(cursor.next(), None);
///
/// // Rewind
/// assert_eq!(cursor.previous(), Some((&5, &"c")));
///
/// // Iterate from the back
/// let mut cursor = map.last_cursor();
/// assert_eq!(cursor.previous(), Some((&5, &"c")));
/// assert_eq!(cursor.previous(), Some((&3, &"b")));
/// assert_eq!(cursor.previous(), Some((&1, &"a")));
/// assert_eq!(cursor.previous(), None);
/// ```
pub struct Cursor<'a, K: Ord + Clone + Sized, V: Sized> {
    pub(super) leaf: Option<LeafNode<K, V>>,
    pub(super) idx: u32,
    pub(super) is_exist: bool,
    pub(super) _marker: PhantomData<&'a ()>,
}

impl<'a, K: Ord + Clone + Sized + 'a, V: Sized + 'a> Iterator for Cursor<'a, K, V> {
    type Item = (&'a K, &'a V);

    /// Returns the key-value pair at current position, then move the cursor forward.
    ///
    /// # Example
    ///
    /// ```
    /// use embed_collections::btree::BTreeMap;
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "b");
    /// map.insert(5, "c");
    ///
    /// let mut cursor = map.first_cursor();
    /// assert_eq!(cursor.next(), Some((&1, &"a")));
    /// assert_eq!(cursor.next(), Some((&3, &"b")));
    /// assert_eq!(cursor.next(), Some((&5, &"c")));
    /// assert_eq!(cursor.next(), None);

    ///
    /// // existing key
    /// let mut cursor = map.cursor(&3);
    /// assert_eq!(cursor.next(), Some((&3, &"b")));
    /// assert_eq!(cursor.next(), Some((&5, &"c")));
    /// assert_eq!(cursor.next(), None);
    ///
    /// // non existing key
    /// let mut cursor = map.cursor(&2);
    /// assert_eq!(cursor.next(), Some((&3, &"b")));
    /// assert_eq!(cursor.next(), Some((&5, &"c")));
    /// assert_eq!(cursor.next(), None);
    /// ```
    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        unsafe {
            loop {
                let leaf = self.leaf.as_ref()?;
                let idx = self.idx;
                if self.is_exist {
                    let (_k, _v) = leaf.get_raw_pair_unchecked(idx);
                    let res = Some((&*_k, &*_v));
                    if idx + 1 < leaf.key_count() {
                        self.idx = idx + 1;
                    } else {
                        if let Some(right) = leaf.get_right_node() {
                            self.leaf.replace(right);
                            self.idx = 0;
                        } else {
                            self.is_exist = false;
                            self.idx = idx + 1;
                        }
                    }
                    return res;
                } else {
                    if self.idx < leaf.key_count() {
                        self.is_exist = true;
                    } else if let Some(right) = leaf.get_right_node() {
                        _ = leaf;
                        self.leaf.replace(right);
                        self.idx = 0;
                        self.is_exist = true;
                    } else {
                        return None;
                    }
                }
            }
        }
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> Cursor<'a, K, V> {
    #[inline(always)]
    pub fn is_exist(&self) -> bool {
        self.is_exist
    }

    /// returns the key-value pair and move the cursor to previous position
    /// Returns `None` if already at the beginning.
    ///
    /// # Example
    ///
    /// ```
    /// use embed_collections::btree::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "b");
    /// map.insert(5, "c");
    ///
    /// // Iterate from the back
    /// let mut cursor = map.last_cursor();
    /// assert_eq!(cursor.previous(), Some((&5, &"c")));
    /// assert_eq!(cursor.previous(), Some((&3, &"b")));
    /// assert_eq!(cursor.previous(), Some((&1, &"a")));
    ///
    /// // non-existing key
    /// let mut cursor = map.cursor(&4);
    /// assert_eq!(cursor.previous(), Some((&3, &"b")));
    /// assert_eq!(cursor.previous(), Some((&1, &"a")));
    ///
    /// // existing key
    ///
    /// let mut cursor = map.cursor(&3);
    /// assert_eq!(cursor.previous(), Some((&3, &"b")));
    /// assert_eq!(cursor.previous(), Some((&1, &"a")));
    /// ```
    #[inline]
    pub fn previous(&mut self) -> Option<(&K, &V)> {
        let leaf = self.leaf.as_ref()?;
        let idx = self.idx;
        unsafe {
            if self.idx > 0 {
                self.idx -= 1;
                if self.is_exist && idx < leaf.key_count() {
                    let (_k, _v) = leaf.get_raw_pair_unchecked(idx);
                    return Some((&*_k, &*_v));
                } else {
                    let (_k, _v) = leaf.get_raw_pair_unchecked(self.idx);
                    return Some((&*_k, &*_v));
                }
            }
            if self.is_exist {
                let (_k, _v) = leaf.get_raw_pair_unchecked(0);
                let res = Some((&*_k, &*_v));
                if let Some(prev) = leaf.get_left_node() {
                    let count = prev.key_count();
                    debug_assert!(count > 0);
                    self.idx = count - 1;
                    self.leaf.replace(prev);
                } else {
                    self.is_exist = false;
                }
                return res;
            }
            if let Some(prev) = leaf.get_left_node() {
                let count = prev.key_count();
                debug_assert!(count > 0);
                self.leaf.replace(prev.clone());
                if count > 1 {
                    self.idx = count - 2;
                    self.is_exist = true;
                } else {
                    self.idx = 0;
                    self.is_exist = false;
                }
                let (_k, _v) = prev.get_raw_pair_unchecked(count - 1);
                Some((&*_k, &*_v))
            } else {
                None
            }
        }
    }

    /// Peeks at the previous entry without moving the cursor.
    /// Returns `None` if there is no previous entry.
    ///
    /// # Example
    ///
    /// ```
    /// use embed_collections::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "b");
    /// map.insert(5, "c");
    ///
    /// // non-existing key
    /// let mut cursor = map.cursor(&2);
    /// assert_eq!(cursor.peek_backward(), Some((&1, &"a")));
    ///
    /// // existing key
    /// let mut cursor = map.cursor(&3);
    /// assert_eq!(cursor.peek_backward(), Some((&1, &"a")));
    #[inline]
    pub fn peek_backward(&self) -> Option<(&K, &V)> {
        let leaf = self.leaf.as_ref()?;
        let mut cursor = IterBackward { back_leaf: leaf.clone(), back_idx: self.idx };
        unsafe {
            if let Some((k, v)) = cursor.prev_pair() {
                return Some((&*k, &*v));
            }
        }
        None
    }

    /// Peeks at the next entry without moving the cursor.
    /// Returns `None` if there is no next entry.
    ///
    /// # Example
    ///
    /// ```
    /// use embed_collections::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "b");
    /// map.insert(5, "c");
    /// // non-existing key
    /// let cursor = map.cursor(&2);
    /// assert_eq!(cursor.peek_forward(), Some((&3, &"b")));
    ///
    /// // existing key
    /// let cursor = map.cursor(&1);
    /// assert_eq!(cursor.peek_forward(), Some((&3, &"b")));
    ///
    ///    #[inline]
    pub fn peek_forward(&self) -> Option<(&K, &V)> {
        let leaf = self.leaf.as_ref()?;
        unsafe {
            if self.is_exist {
                let mut cursor = IterForward { front_leaf: leaf.clone(), idx: self.idx + 1 };
                if let Some((k, v)) = cursor.next_pair() {
                    return Some((&*k, &*v));
                }
            } else {
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
}

/*
impl<'a, K: Ord + Clone + Sized + fmt::Debug, V: Sized + fmt::Debug> fmt::Debug
    for Cursor<'a, K, V>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((k, v)) = self.peek_forward() {
            f.debug_struct("Cursor").field("key", k).field("value", v).finish()
        } else {
            f.debug_struct("Cursor").field("key", &"<end>").field("value", &"<end>").finish()
        }
    }
}
*/
