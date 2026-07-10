use super::{BTreeMap, helper::*, leaf::*, node::*};
use crate::trace_log;
use core::marker::PhantomData;
use core::mem::needs_drop;

pub(super) struct IterForward<K, V> {
    /// Current leaf node for forward iteration
    pub front_leaf: LeafNode<K, V>,
    /// Current index within the leaf for forward iteration
    pub idx: u32,
}

impl<K, V> IterForward<K, V> {
    #[inline]
    pub fn next(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        if self.idx >= self.front_leaf.key_count() {
            if let Some(next) = self.front_leaf.get_right_node() {
                debug_assert!(next.key_count() > 0);
                self.front_leaf = next;
                self.idx = 0;
            } else {
                return None;
            }
        }
        let current_idx = self.idx;
        self.idx = current_idx + 1;
        Some((&mut self.front_leaf, current_idx))
    }

    #[inline]
    pub unsafe fn next_pair(&mut self) -> Option<(*mut K, *mut V)> {
        let (leaf, idx) = self.next()?;
        leaf.get_raw_pair(idx)
    }
}

pub(super) struct IterBackward<K, V> {
    /// Current leaf node for backward iteration
    pub back_leaf: LeafNode<K, V>,
    /// back_idx - 1 is the next index within the back leaf, initial to key_count
    /// When back_idx == 0, should go to previous leaf
    pub back_idx: u32,
}

impl<K, V> IterBackward<K, V> {
    #[inline]
    pub fn prev(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        if self.back_idx == 0 {
            if let Some(prev) = self.back_leaf.get_left_node() {
                self.back_idx = prev.key_count();
                self.back_leaf = prev;
                debug_assert!(self.back_idx > 0);
            } else {
                return None;
            }
        }
        self.back_idx -= 1;
        Some((&mut self.back_leaf, self.back_idx))
    }

    #[inline]
    pub unsafe fn prev_pair(&mut self) -> Option<(*mut K, *mut V)> {
        let (leaf, idx) = self.prev()?;
        leaf.get_raw_pair(idx)
    }
}

/// Internal base iterator structure that handles the common logic
/// for iterating over leaf nodes in both forward and backward directions.
struct IterBase<K, V> {
    /// Remaining elements to iterate, it serve as a guard in case forward and backward rendezvous
    remaining: usize,
    forward: IterForward<K, V>,
    backward: IterBackward<K, V>,
}

impl<K, V> IterBase<K, V> {
    /// Create a new IterBase
    /// leaves: (front_leaf, back_leaf) - both Some or both None
    /// remaining: total remaining elements
    #[inline]
    fn new(front_leaf: LeafNode<K, V>, back_leaf: LeafNode<K, V>, remaining: usize) -> Self {
        Self {
            forward: IterForward { front_leaf, idx: 0 },
            backward: IterBackward { back_idx: back_leaf.key_count(), back_leaf },
            remaining,
        }
    }

    /// Advance the forward iterator and return the current leaf and index
    /// Returns None if we've moved past the end
    #[inline]
    fn advance_forward(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        self.forward.next()
    }

    /// Advance the backward iterator and return the current leaf and index
    /// Returns None if we've moved past the beginning
    #[inline]
    fn advance_backward(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        self.backward.prev()
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
            let value = (*leaf.value_ptr_mut(idx)).assume_init_mut();
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
            let value = (*leaf.value_ptr_mut(idx)).assume_init_mut();
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
    fn advance_forward(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        loop {
            let idx = self.front_idx;
            if self.front_leaf == self.back_leaf {
                if idx < self.back_idx {
                    self.front_idx = idx + 1;
                    return Some((&mut self.front_leaf, idx));
                } else {
                    return None;
                }
            } else {
                if idx < self.front_leaf.key_count() {
                    self.front_idx = idx + 1;
                    return Some((&mut self.front_leaf, idx));
                } else {
                    self.front_leaf = self.front_leaf.get_right_node().unwrap();
                    self.front_idx = 0;
                    // Because we always need to compare front_leaf and back_leaf after cursor
                    // moves, cannot use IterForward & IterBackward here.
                }
            }
        }
    }

    /// Advance backward and return the current leaf and index
    /// Returns None when range is exhausted, caller should set RangeBase to None
    #[inline]
    fn advance_backward(&mut self) -> Option<(&mut LeafNode<K, V>, u32)> {
        loop {
            if self.back_leaf == self.front_leaf {
                if self.back_idx == 0 {
                    return None;
                }
                self.back_idx -= 1;
                if self.back_idx >= self.front_idx {
                    return Some((&mut self.back_leaf, self.back_idx));
                } else {
                    return None;
                }
            } else {
                if self.back_idx == 0 {
                    self.back_leaf = self.back_leaf.get_left_node().unwrap();
                    self.back_idx = self.back_leaf.key_count();
                    // Because we always need to compare front_leaf and back_leaf after cursor
                    // moves, cannot use IterForward & IterBackward here.
                } else {
                    self.back_idx -= 1;
                    return Some((&mut self.back_leaf, self.back_idx));
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
                let value = (*leaf.value_ptr_mut(idx)).assume_init_mut();
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
                let value = (*leaf.value_ptr_mut(idx)).assume_init_mut();
                Some((key, value))
            }
        } else {
            self.base = None;
            None
        }
    }
}

struct IntoIterBase<K: Ord + Clone + Sized, V: Sized> {
    /// Path cache for deallocating internal nodes after iteration
    _cache: Option<TreeInfo<K, V>>,
    /// Current leaf being iterated
    leaf: Option<LeafNode<K, V>>,
    /// Current index within the leaf
    idx: u32,
    /// Remaining elements to iterate
    remaining: usize,
    is_forward: bool,
}

impl<K: Ord + Clone + Sized, V: Sized> IntoIterBase<K, V> {
    #[inline]
    fn new(tree: &mut BTreeMap<K, V>, is_forward: bool) -> Self {
        if let Some(root_p) = tree.root.take() {
            let mut cache = tree.take_cache();
            // Move TreeInfo out of BTreeMap, leave a fresh empty one as placeholder.
            let leaf = match Node::from_root_ptr(root_p) {
                Node::Leaf(leaf) => leaf,
                Node::Inter(inter) => {
                    if is_forward {
                        inter.find_first_leaf(cache.as_mut())
                    } else {
                        inter.find_last_leaf(cache.as_mut())
                    }
                }
            };
            Self {
                _cache: cache,
                idx: if is_forward { 0 } else { leaf.key_count() },
                leaf: Some(leaf),
                remaining: tree.len,
                is_forward,
            }
        } else {
            Self { _cache: None, leaf: None, idx: 0, remaining: 0, is_forward }
        }
    }

    #[inline(always)]
    fn get_cache(&mut self) -> Option<&mut TreeInfo<K, V>> {
        self._cache.as_mut()
    }

    #[inline(always)]
    fn advance_forward(&mut self) -> LeafNode<K, V> {
        let _leaf = self.leaf.take().unwrap();
        _leaf.dealloc::<false>();
        let cache = self.get_cache().unwrap();
        let (parent, idx) = cache
            .move_right_and_pop_l1(|_info, _node| {
                _node.dealloc::<true>();
            })
            .unwrap();
        cache.push(parent.clone(), idx);
        let new_leaf = parent.get_child_as_leaf(idx);
        self.idx = 0;
        new_leaf
    }

    #[inline(always)]
    fn advance_backward(&mut self) -> LeafNode<K, V> {
        let _leaf = self.leaf.take().unwrap();
        _leaf.dealloc::<false>();
        let cache = self.get_cache().unwrap();
        let (parent, idx) =
            cache.move_left_and_pop_l1(|_info, _node| _node.dealloc::<true>()).unwrap();
        cache.push(parent.clone(), idx);
        let new_leaf = parent.get_child_as_leaf(idx);
        self.idx = new_leaf.key_count();
        new_leaf
    }

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
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
                trace_log!("into_iter forward: {leaf:?}:{idx}");
                unsafe {
                    let key = (*leaf.key_ptr(idx)).assume_init_read();
                    let value = (*leaf.value_ptr(idx)).assume_init_read();
                    return Some((key, value));
                }
            }
        } else {
            if self.idx == 0 {
                if let Some(ref leaf) = self.leaf {
                    leaf.get_left_node()?;
                }
                let new_leaf = self.advance_backward();
                self.leaf = Some(new_leaf);
            }
            if let Some(ref leaf) = self.leaf {
                self.idx -= 1;
                let idx = self.idx;
                trace_log!("into_iter backward: {leaf:?}:{idx}");
                unsafe {
                    let key = (*leaf.key_ptr(idx)).assume_init_read();
                    let value = (*leaf.value_ptr(idx)).assume_init_read();
                    return Some((key, value));
                }
            }
        }
        None
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Drop for IntoIterBase<K, V> {
    fn drop(&mut self) {
        let is_forward = self.is_forward;
        // NOTE: if the original tree has root, then self.leaf always exists after iteration done
        if let Some(mut leaf) = self.leaf.take() {
            if needs_drop::<K>() {
                if is_forward {
                    trace_log!("into_iter drop forward {leaf:?} [{}..]", self.idx);
                    for idx in self.idx..leaf.key_count() {
                        unsafe { (*leaf.key_ptr_mut(idx)).assume_init_drop() };
                    }
                } else {
                    trace_log!("into_iter drop backward {leaf:?} [..{}]", self.idx);
                    for idx in 0..self.idx {
                        unsafe { (*leaf.key_ptr_mut(idx)).assume_init_drop() };
                    }
                }
            }
            if needs_drop::<V>() {
                if is_forward {
                    for idx in self.idx..leaf.key_count() {
                        unsafe { (*leaf.value_ptr_mut(idx)).assume_init_drop() };
                    }
                } else {
                    for idx in 0..self.idx {
                        unsafe { (*leaf.value_ptr_mut(idx)).assume_init_drop() };
                    }
                }
            }
            leaf.dealloc::<false>();
            if let Some(cache) = self.get_cache() {
                // We should free the rest internal nodes even after leaf iteration done
                if is_forward {
                    while let Some((parent, idx)) = cache.move_right_and_pop_l1(|_info, _node| {
                        _node.dealloc::<true>();
                    }) {
                        trace_log!("into_iter drop forward parent {parent:?}:{idx}");
                        cache.push(parent.clone(), idx);
                        let leaf = parent.get_child_as_leaf(idx);
                        leaf.dealloc::<true>();
                    }
                } else {
                    while let Some((parent, idx)) = cache.move_left_and_pop_l1(|_info, _node| {
                        _node.dealloc::<true>();
                    }) {
                        trace_log!("into_iter drop forward parent {parent:?}:{idx}");
                        cache.push(parent.clone(), idx);
                        let leaf = parent.get_child_as_leaf(idx);
                        leaf.dealloc::<true>();
                    }
                }
            }
        }
    }
}

/// An owning iterator over the entries of a BTreeMap
/// Uses PathCache to manage tree traversal and safe deallocation
///
/// NOTE: In order to keep the logic simple, we does not implement `DoubleEndedIterator` here
pub struct IntoIter<K: Ord + Clone + Sized, V: Sized> {
    /// If true, iterate in reverse order
    base: Result<IntoIterBase<K, V>, (BTreeMap<K, V>, bool)>,
}

impl<K: Ord + Clone + Sized, V: Sized> IntoIter<K, V> {
    #[inline]
    pub(super) fn new(tree: BTreeMap<K, V>, is_forward: bool) -> Self {
        Self { base: Err((tree, is_forward)) }
    }

    /// Return a iterator in reversed direction
    ///
    /// IntoIter only implement one way iteration (either forward or backward).
    /// this will mock Iterator::rev for DoubleEndedIterator trait
    ///
    /// # Panic
    ///
    /// If iteration already started, cannot change the direction
    #[inline]
    pub fn rev(self) -> Self {
        if let Err((tree, _is_forward)) = self.base {
            Self { base: Err((tree, false)) }
        } else {
            panic!("cannot change direction after iteration start");
        }
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.base {
            Ok(base) => base.next(),
            Err((tree, is_forward)) => {
                self.base = Ok(IntoIterBase::new(tree, *is_forward));
                if let Ok(base) = &mut self.base {
                    base.next()
                } else {
                    unreachable!();
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = match &self.base {
            Ok(base) => base.remaining,
            Err((tree, _)) => tree.len(),
        };
        (remaining, Some(remaining))
    }
}

impl<K: Ord + Clone + Sized, V: Sized> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        match &self.base {
            Ok(base) => base.remaining,
            Err((tree, _)) => tree.len(),
        }
    }
}
