use super::BTreeMap;
use super::inter::*;
use super::leaf::*;
use super::node::*;
use core::marker::PhantomData;
use core::mem::needs_drop;

/// Internal base iterator structure that handles the common logic
/// for iterating over leaf nodes in both forward and backward directions.
struct IterBase<K, V> {
    /// Current leaf node for forward iteration
    front_leaf: LeafNode<K, V>,
    /// Current index within the leaf for forward iteration
    idx: u32,
    /// Current leaf node for backward iteration
    back_leaf: LeafNode<K, V>,
    /// back_idx - 1 is the next index within the back leaf, initial to key_count
    /// When back_idx == 0, should go to previous leaf
    back_idx: u32,
    /// Remaining elements to iterate
    remaining: usize,
}

impl<K, V> IterBase<K, V> {
    /// Create a new IterBase
    /// leaves: (front_leaf, back_leaf) - both Some or both None
    /// remaining: total remaining elements
    #[inline]
    fn new(front_leaf: LeafNode<K, V>, back_leaf: LeafNode<K, V>, remaining: usize) -> Self {
        Self { front_leaf, idx: 0, back_idx: back_leaf.key_count(), back_leaf, remaining }
    }

    /// Advance the forward iterator and return the current leaf and index
    /// Returns None if we've moved past the end
    #[inline]
    fn advance_forward(&mut self) -> Option<(&LeafNode<K, V>, u32)> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        if self.idx >= self.front_leaf.key_count() {
            let next = self.front_leaf.get_right_node().unwrap();
            debug_assert!(next.key_count() > 0);
            self.front_leaf = next;
            self.idx = 0;
        }
        let current_idx = self.idx;
        self.idx = current_idx + 1;
        Some((&self.front_leaf, current_idx))
    }

    /// Advance the backward iterator and return the current leaf and index
    /// Returns None if we've moved past the beginning
    #[inline]
    fn advance_backward(&mut self) -> Option<(&LeafNode<K, V>, u32)> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        if self.back_idx == 0 {
            let prev = self.back_leaf.get_left_node().unwrap();
            self.back_idx = prev.key_count();
            self.back_leaf = prev;
            debug_assert!(self.back_idx > 0);
        }
        self.back_idx -= 1;
        Some((&self.back_leaf, self.back_idx))
    }

    /// Get remaining count
    #[inline]
    fn remaining(&self) -> usize {
        self.remaining
    }
}

/// An iterator over the entries of a BTreeMap
pub struct Iter<'a, K: 'a, V: 'a> {
    base: Option<IterBase<K, V>>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    #[inline]
    pub(super) fn new(leaves: Option<(LeafNode<K, V>, LeafNode<K, V>)>, remaining: usize) -> Self {
        if let Some((front, back)) = leaves {
            Self { base: Some(IterBase::new(front, back, remaining)), _marker: Default::default() }
        } else {
            Self { base: None, _marker: Default::default() }
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        let (leaf, idx) = base.advance_forward()?;
        unsafe {
            let key = (*leaf.key_ptr(idx)).assume_init_ref();
            let value = (*leaf.value_ptr(idx)).assume_init_ref();
            Some((key, value))
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Iter<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.as_ref().map(|x| x.remaining()).unwrap_or(0)
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        let (leaf, idx) = base.advance_backward()?;
        unsafe {
            let key = (*leaf.key_ptr(idx)).assume_init_ref();
            let value = (*leaf.value_ptr(idx)).assume_init_ref();
            Some((key, value))
        }
    }
}

/// A mutable iterator over the entries of a BTreeMap
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: Option<IterBase<K, V>>,
    _marker: PhantomData<&'a mut ()>,
}

impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    #[inline]
    pub(super) fn new(leaves: Option<(LeafNode<K, V>, LeafNode<K, V>)>, remaining: usize) -> Self {
        if let Some((front, back)) = leaves {
            Self { base: Some(IterBase::new(front, back, remaining)), _marker: Default::default() }
        } else {
            Self { base: None, _marker: Default::default() }
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        let (leaf, idx) = base.advance_forward()?;
        unsafe {
            let key = (*leaf.key_ptr(idx)).assume_init_ref();
            let value = (*leaf.value_ptr(idx)).assume_init_mut();
            Some((key, value))
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for IterMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.as_ref().map(|x| x.remaining()).unwrap_or(0)
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        let (leaf, idx) = base.advance_backward()?;
        unsafe {
            let key = (*leaf.key_ptr(idx)).assume_init_ref();
            let value = (*leaf.value_ptr(idx)).assume_init_mut();
            Some((key, value))
        }
    }
}

/// An iterator over the keys of a BTreeMap
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Keys<'a, K, V> {
    #[inline]
    pub(super) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Keys<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

/// An iterator over the values of a BTreeMap
pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> Values<'a, K, V> {
    #[inline]
    pub(super) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Values<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Values<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

/// A mutable iterator over the values of a BTreeMap
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K: 'a, V: 'a> ValuesMut<'a, K, V> {
    #[inline]
    pub(super) fn new(inner: IterMut<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for ValuesMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for ValuesMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(_, v)| v)
    }
}

// Range and RangeMut implementations with DoubleEndedIterator support

/// Internal base structure for range iteration
/// Manages forward and backward iteration over a range of entries
/// When the range is exhausted, the entire struct should be set to None
pub(super) struct RangeBase<'a, K: 'a, V: 'a> {
    front_leaf: LeafNode<K, V>,
    back_leaf: LeafNode<K, V>,
    front_idx: u32,
    // back_idx -1 is the next pos, initial to be key_count
    back_idx: u32,
    _marker: PhantomData<&'a ()>,
}

impl<'a, K: 'a, V: 'a> RangeBase<'a, K, V> {
    #[inline]
    pub fn new(
        front_leaf: LeafNode<K, V>, front_idx: u32, back_leaf: LeafNode<K, V>, back_idx: u32,
    ) -> Self {
        Self { front_leaf, front_idx, back_leaf, back_idx, _marker: PhantomData }
    }

    /// Advance forward and return the current leaf and index
    /// Returns None when range is exhausted, caller should set RangeBase to None
    #[inline]
    fn advance_forward(&mut self) -> Option<(&LeafNode<K, V>, u32)> {
        loop {
            let idx = self.front_idx;
            if self.front_leaf == self.back_leaf {
                if idx < self.back_idx {
                    self.front_idx = idx + 1;
                    return Some((&self.front_leaf, idx));
                } else {
                    return None;
                }
            } else {
                if idx < self.front_leaf.key_count() {
                    self.front_idx = idx + 1;
                    return Some((&self.front_leaf, idx));
                } else {
                    self.front_leaf = self.front_leaf.get_right_node().unwrap();
                    self.front_idx = 0;
                }
            }
        }
    }

    /// Advance backward and return the current leaf and index
    /// Returns None when range is exhausted, caller should set RangeBase to None
    #[inline]
    fn advance_backward(&mut self) -> Option<(&LeafNode<K, V>, u32)> {
        loop {
            if self.back_leaf == self.front_leaf {
                if self.back_idx == 0 {
                    return None;
                }
                self.back_idx -= 1;
                if self.back_idx >= self.front_idx {
                    return Some((&self.back_leaf, self.back_idx));
                } else {
                    return None;
                }
            } else {
                if self.back_idx == 0 {
                    self.back_leaf = self.back_leaf.get_left_node().unwrap();
                    self.back_idx = self.back_leaf.key_count();
                } else {
                    self.back_idx -= 1;
                    return Some((&self.back_leaf, self.back_idx));
                }
            }
        }
    }
}

/// An iterator over a sub-range of entries in a BTreeMap
/// RangeBase is wrapped in Option - when exhausted, it becomes None
pub struct Range<'a, K: 'a, V: 'a> {
    base: Option<RangeBase<'a, K, V>>,
}

impl<'a, K: 'a, V: 'a> Range<'a, K, V> {
    #[inline]
    pub(super) fn new(base: Option<RangeBase<'a, K, V>>) -> Self {
        Self { base }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        if let Some((leaf, idx)) = base.advance_forward() {
            unsafe {
                let key = (*leaf.key_ptr(idx)).assume_init_ref();
                let value = (*leaf.value_ptr(idx)).assume_init_ref();
                Some((key, value))
            }
        } else {
            self.base = None;
            None
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Range<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        if let Some((leaf, idx)) = base.advance_backward() {
            unsafe {
                let key = (*leaf.key_ptr(idx)).assume_init_ref();
                let value = (*leaf.value_ptr(idx)).assume_init_ref();
                Some((key, value))
            }
        } else {
            self.base = None;
            None
        }
    }
}

/// A mutable iterator over a sub-range of entries in a BTreeMap
/// RangeBase is wrapped in Option - when exhausted, it becomes None
pub struct RangeMut<'a, K: 'a, V: 'a> {
    base: Option<RangeBase<'a, K, V>>,
}

impl<'a, K: 'a, V: 'a> RangeMut<'a, K, V> {
    #[inline]
    pub(super) fn new(base: Option<RangeBase<'a, K, V>>) -> Self {
        Self { base }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        if let Some((leaf, idx)) = base.advance_forward() {
            unsafe {
                let key = (*leaf.key_ptr(idx)).assume_init_ref();
                let value = (*leaf.value_ptr(idx)).assume_init_mut();
                Some((key, value))
            }
        } else {
            self.base = None;
            None
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for RangeMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let base = self.base.as_mut()?;
        if let Some((leaf, idx)) = base.advance_backward() {
            unsafe {
                let key = (*leaf.key_ptr(idx)).assume_init_ref();
                let value = (*leaf.value_ptr(idx)).assume_init_mut();
                Some((key, value))
            }
        } else {
            self.base = None;
            None
        }
    }
}

/// An owning iterator over the entries of a BTreeMap
/// Uses PathCache to manage tree traversal and safe deallocation
///
/// NOTE: In order to keep the logic simple, we does not implement `DoubleEndedIterator` here
pub struct IntoIter<K: Ord + Clone + Sized, V: Sized> {
    /// Path cache for deallocating internal nodes after iteration
    cache: PathCache<K, V>,
    /// Current leaf being iterated
    leaf: Option<LeafNode<K, V>>,
    /// Current index within the leaf
    idx: u32,
    /// Remaining elements to iterate
    remaining: usize,
    /// If true, iterate in reverse order
    is_forward: bool,
}

impl<K: Ord + Clone + Sized, V: Sized> IntoIter<K, V> {
    #[inline]
    pub(super) fn new(mut tree: BTreeMap<K, V>, is_forward: bool) -> Self {
        if let Some(root) = tree.root.take() {
            let mut cache = tree.get_cache().take();
            let leaf = if is_forward {
                root.find_first_leaf(Some(&mut cache))
            } else {
                root.find_last_leaf(Some(&mut cache))
            };
            Self {
                cache,
                idx: if is_forward { 0 } else { leaf.key_count() },
                leaf: Some(leaf),
                remaining: tree.len,
                is_forward,
            }
        } else {
            Self { cache: PathCache::new(), leaf: None, idx: 0, remaining: 0, is_forward }
        }
    }

    #[inline(always)]
    fn advance_forward(&mut self) -> LeafNode<K, V> {
        let _leaf = self.leaf.take().unwrap();
        _leaf.dealloc::<false>();
        let (parent, idx) = self.cache.move_right_and_pop_l1(InterNode::dealloc::<true>).unwrap();
        self.cache.push(parent.clone(), idx);
        let new_leaf = parent.get_child(idx).into_leaf();
        self.idx = 0;
        new_leaf
    }

    #[inline(always)]
    fn advance_backward(&mut self) -> LeafNode<K, V> {
        let _leaf = self.leaf.take().unwrap();
        _leaf.dealloc::<false>();
        let (parent, idx) = self.cache.move_left_and_pop_l1(InterNode::dealloc::<true>).unwrap();
        self.cache.push(parent.clone(), idx);
        let new_leaf = parent.get_child(idx).into_leaf();
        self.idx = new_leaf.key_count();
        new_leaf
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;

        // Check if we need to advance to next/prev leaf
        if self.is_forward {
            if let Some(ref leaf) = self.leaf {
                if self.idx >= leaf.key_count() {
                    let new_leaf = self.advance_forward();
                    self.leaf = Some(new_leaf);
                }
            } else {
                return None;
            }
            let idx = self.idx;
            self.idx += 1;
            if let Some(ref leaf) = self.leaf {
                unsafe {
                    let key = (*leaf.key_ptr(idx)).assume_init_read();
                    let value = (*leaf.value_ptr(idx)).assume_init_read();
                    return Some((key, value));
                }
            }
        } else {
            if self.idx == 0 {
                if let Some(ref leaf) = self.leaf {
                    if leaf.get_left_node().is_none() {
                        // At the beginning
                        return None;
                    }
                }
                let new_leaf = self.advance_backward();
                self.leaf = Some(new_leaf);
            }
            if let Some(ref leaf) = self.leaf {
                self.idx -= 1;
                let idx = self.idx;
                unsafe {
                    let key = (*leaf.key_ptr(idx)).assume_init_read();
                    let value = (*leaf.value_ptr(idx)).assume_init_read();
                    return Some((key, value));
                }
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<K: Ord + Clone + Sized, V: Sized> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.remaining
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        // NOTE: if the original tree has root, then self.leaf always exists after iteration done
        if let Some(leaf) = self.leaf.take() {
            if self.is_forward {
                if needs_drop::<K>() {
                    for idx in self.idx..leaf.key_count() {
                        unsafe { (*leaf.key_ptr(idx)).assume_init_drop() };
                    }
                }
                if needs_drop::<V>() {
                    for idx in self.idx..leaf.key_count() {
                        unsafe { (*leaf.value_ptr(idx)).assume_init_drop() };
                    }
                }
            } else {
                if needs_drop::<K>() {
                    for idx in 0..self.idx {
                        unsafe { (*leaf.key_ptr(idx)).assume_init_drop() };
                    }
                }
                if needs_drop::<V>() {
                    for idx in 0..self.idx {
                        unsafe { (*leaf.value_ptr(idx)).assume_init_drop() };
                    }
                }
            }
            leaf.dealloc::<false>();
            // We should free the rest internal nodes even after leaf iteraction done
            if self.is_forward {
                while let Some((parent, idx)) =
                    self.cache.move_right_and_pop_l1(InterNode::dealloc::<true>)
                {
                    self.cache.push(parent.clone(), idx);
                    if let Node::Leaf(leaf) = parent.get_child(idx) {
                        leaf.dealloc::<true>();
                    } else {
                        unreachable!();
                    }
                }
            } else {
                while let Some((parent, idx)) =
                    self.cache.move_left_and_pop_l1(InterNode::dealloc::<true>)
                {
                    self.cache.push(parent.clone(), idx);
                    if let Node::Leaf(leaf) = parent.get_child(idx) {
                        leaf.dealloc::<true>();
                    } else {
                        unreachable!();
                    }
                }
            }
        }
    }
}
