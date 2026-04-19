use super::{inter::*, leaf::*};
use crate::{CACHE_LINE_SIZE, Various, trace_log};
use alloc::alloc::{Layout, alloc, handle_alloc_error};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Bound;
use core::ptr::{self, NonNull};

/// Key area size: first 128 bytes (2 cache lines)
pub(super) const AREA_SIZE: usize = 2 * CACHE_LINE_SIZE; // 128 bytes

/// Total node size: 4 cache lines (256 bytes on x86_64)
pub(super) const NODE_SIZE: usize = 2 * AREA_SIZE; // 256 bytes

pub(super) const PTR_SIZE: usize = size_of::<*mut NodeHeader>();
pub(super) const PTR_ALIGN: usize = align_of::<*mut NodeHeader>();

/*
The Layout:
- InterNode: CACHELINE( 8B NodeHeader | Keys | alignment ),  CACHELINE(Values)
- LeafNode: CACHELINE(8B NodeHeader | 8B padding | Keys | alignment), CACHELINE( 16B LeafPtrs, values )
*/

/// Node header (8 bytes at start of key area)
/// height: 0 = leaf node, >0 = internal node (height of subtree)
#[repr(C)]
pub(super) struct NodeHeader {
    /// Height of the node (0 = leaf, >0 = internal)
    pub height: u32,
    /// Count of items in the node
    pub count: u32,
}

impl NodeHeader {
    pub const LEAF_MASK: usize = 1;

    #[inline]
    pub unsafe fn get_field<T>(p: NonNull<Self>, offset: usize) -> *mut T {
        unsafe { (p.as_ptr() as *const u8).add(offset) as *mut T }
    }

    /// Check if this is a leaf node (height == 0)
    #[inline(always)]
    pub fn is_leaf(&self) -> bool {
        self.height == 0
    }
}

/// Generic node wrapper
#[derive(Clone)]
pub(super) struct NodeBase {
    pub header: NonNull<NodeHeader>,
}

impl NodeBase {
    #[inline(always)]
    pub fn _alloc(layout: Layout) -> Self {
        unsafe {
            let p: *mut u8 = alloc(layout);
            if p.is_null() {
                handle_alloc_error(layout);
            }
            let header = NonNull::new_unchecked(p as *mut NodeHeader);
            Self { header }
        }
    }

    #[inline(always)]
    pub fn get_header(&self) -> &NodeHeader {
        unsafe { self.header.as_ref() }
    }

    #[inline(always)]
    pub fn get_header_mut(&mut self) -> &mut NodeHeader {
        unsafe { self.header.as_mut() }
    }

    #[inline(always)]
    pub fn get_ptr(&self) -> *mut NodeHeader {
        self.header.as_ptr()
    }

    #[cfg(test)]
    #[inline(always)]
    pub fn get_array<T>(&self, header_size: usize, delta: usize) -> &[T] {
        let header = self.get_header();
        let items_ptr = unsafe { NodeHeader::get_field::<T>(self.header, header_size) };
        unsafe { core::slice::from_raw_parts::<T>(items_ptr, header.count as usize + delta) }
    }

    /// Get pointer to key at index with given header offset
    ///
    /// # Safety
    ///
    /// we should enough item_size has a minminum value aligned to PTR_ALIGN during cal_layout
    #[inline(always)]
    pub unsafe fn item_ptr<T>(&self, start_offset: usize, idx: u32) -> *mut T {
        let mut v_size = size_of::<T>();
        if v_size == 0 {
            v_size = 1;
        }
        unsafe { NodeHeader::get_field::<T>(self.header, start_offset + idx as usize * v_size) }
    }

    /// Get count of items in the node
    #[inline(always)]
    pub fn key_count(&self) -> u32 {
        self.get_header().count
    }

    /// Get height of the node
    #[inline(always)]
    pub fn height(&self) -> u32 {
        self.get_header().height
    }

    /// search the position to insert (need to move old items from idx to the right)
    /// returns the idx, is_equal
    #[inline]
    pub fn _search<K, Q>(&self, header_offset: usize, key: &Q) -> (u32, bool)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        macro_rules! _search {
            ($start: expr, $end: expr) => {
                let mut idx = $start as u32;
                if $start < $end {
                    let mut k = self.item_ptr::<K>(header_offset, $start as u32);
                    loop {
                        let k_ref: &Q = (&*k).borrow();
                        let r = k_ref.cmp(key);
                        // For linear search, always put the most frequent case first,
                        // there might be huge penalty on cpu branch prediction failure.
                        if r == Ordering::Less {
                            idx += 1;
                            if idx < $end {
                                k = k.add(1);
                                continue;
                            }
                            break;
                        } else {
                            return (idx, r == Ordering::Equal);
                        }
                    }
                    // NOTE: be aware to check idx == cap
                }
                // insert on an empty node just return (0, false)
                return (idx, false);
            };
        }
        unsafe {
            let count = self.key_count();
            let first_line_bytes = CACHE_LINE_SIZE - header_offset;
            let first_line_limit = (first_line_bytes / size_of::<K>()) as u32;
            if count > first_line_limit {
                let first_line_last = &*self.item_ptr::<K>(header_offset, first_line_limit - 1);
                if key > first_line_last.borrow() {
                    _search!(first_line_limit, count);
                } else {
                    // using constant here might hint compiler generate SIMD code
                    _search!(0, first_line_limit);
                }
            } else {
                _search!(0, count);
            }
        }
    }

    /// Insert key value at position and return value pointer (entry insert needs to return reference)
    ///
    /// # Safety
    /// it does not check is_full
    #[inline(always)]
    pub unsafe fn _insert<K, V>(
        &mut self, key_header_offset: usize, value_header_offset: usize, idx: u32, key: K, value: V,
    ) -> *mut V {
        let count = self.key_count();
        unsafe {
            let key_p = self.item_ptr::<K>(key_header_offset, idx);
            if idx < count {
                ptr::copy(key_p, key_p.add(1), (count - idx) as usize);
            }
            key_p.write(key);
            let value_p = self.item_ptr::<V>(value_header_offset, idx);
            if idx < count {
                ptr::copy(value_p, value_p.add(1), (count - idx) as usize);
            }
            value_p.write(value);
            self.get_header_mut().count = count + 1;
            value_p
        }
    }
}

pub(crate) enum Node<K, V> {
    Inter(InterNode<K, V>),
    Leaf(LeafNode<K, V>),
}

impl<K, V> fmt::Debug for Node<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Inter(node) => node.fmt(f),
            Self::Leaf(node) => node.fmt(f),
        }
    }
}

impl<K: Ord, V> Clone for Node<K, V> {
    #[inline(always)]
    fn clone(&self) -> Self {
        match self {
            Self::Inter(node) => Self::Inter(node.clone()),
            Self::Leaf(node) => Self::Leaf(node.clone()),
        }
    }
}

impl<K: Ord, V> Node<K, V> {
    pub fn from_root_ptr(mut p: NonNull<NodeHeader>) -> Self {
        let _p = p.as_ptr() as usize;
        if _p & NodeHeader::LEAF_MASK > 0 {
            p = unsafe { NonNull::new_unchecked((_p ^ NodeHeader::LEAF_MASK) as *mut NodeHeader) };
            Self::Leaf(LeafNode::<K, V>::from(p))
        } else {
            Self::Inter(InterNode::<K, V>::from(p))
        }
    }

    #[inline(always)]
    pub fn is_leaf(&self) -> bool {
        match self {
            Self::Inter(_) => false,
            Self::Leaf(_) => true,
        }
    }

    #[inline(always)]
    pub fn height(&self) -> u32 {
        match self {
            Self::Inter(node) => node.height(),
            Self::Leaf(_) => 0,
        }
    }

    #[cfg(test)]
    pub fn into_inter(self) -> InterNode<K, V> {
        if let Self::Inter(node) = self {
            node
        } else {
            unreachable!();
        }
    }

    #[inline]
    pub fn into_leaf(self) -> LeafNode<K, V> {
        if let Self::Leaf(node) = self {
            node
        } else {
            unreachable!();
        }
    }

    #[inline]
    pub fn find_leaf<Q>(&self, key: &Q) -> LeafNode<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self {
            Self::Leaf(node) => node.clone(),
            Self::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let idx = cur.search_child(key);
                    trace_log!("find_leaf {cur:?} {idx}");
                    match cur.get_child(idx) {
                        Node::Leaf(leaf) => return leaf,
                        Node::Inter(inter) => {
                            cur = inter;
                        }
                    }
                }
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache<Q>(&self, cache: &mut PathCache<K, V>, key: &Q) -> LeafNode<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match &self {
            Self::Leaf(node) => node.clone(),
            Self::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let idx = cur.search_child(key);
                    trace_log!("find_leaf_with_cache {cur:?} {idx}");
                    cache.push(cur.clone(), idx);
                    match cur.get_child(idx) {
                        Node::Leaf(leaf) => {
                            trace_log!("find_leaf_with_cache got {leaf:?}");
                            return leaf;
                        }
                        Node::Inter(inter) => {
                            cur = inter;
                        }
                    }
                }
            }
        }
    }

    /// is_start: true for start_bound, false for end_bound
    ///
    /// return value:
    /// - leaf node contains the bound
    /// - idx: regardless include or exclude, idx always return idx|0 for start_bound,
    ///   return (idx + 1) | key_count() for end_bound
    #[inline]
    pub fn find_leaf_with_bound<Q>(&self, bound: Bound<&Q>, is_start: bool) -> (LeafNode<K, V>, u32)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let key = borrow_key_from_bound::<Q>(bound);
        let mut cur = self.clone();
        loop {
            match cur {
                Self::Leaf(node) => {
                    let idx = if let Some(k) = key.as_ref() {
                        let (idx, is_equal) = node.search(k);
                        if is_start {
                            if let Bound::Excluded(_) = bound {
                                if is_equal { idx + 1 } else { idx }
                            } else {
                                idx
                            }
                        } else {
                            if let Bound::Excluded(_) = bound {
                                idx
                            } else {
                                if is_equal { idx + 1 } else { idx }
                            }
                        }
                    } else {
                        if is_start { 0 } else { node.key_count() }
                    };
                    return (node, idx);
                }
                Self::Inter(node) => {
                    let idx = if let Some(k) = key.as_ref() {
                        node.search_child(k)
                    } else {
                        if is_start { 0 } else { node.key_count() - 1 }
                    };
                    cur = node.get_child(idx);
                }
            }
        }
    }

    /// Find the first leaf node
    #[inline]
    pub fn find_first_leaf(&self, mut cache: Option<&mut PathCache<K, V>>) -> LeafNode<K, V> {
        let mut cur: Self = self.clone();
        loop {
            match cur {
                Self::Leaf(leaf) => return leaf,
                Self::Inter(inter) => {
                    if let Some(_cache) = cache.as_mut() {
                        _cache.push(inter.clone(), 0);
                    }
                    cur = inter.get_child(0);
                }
            }
        }
    }

    /// Find the last leaf node
    #[inline]
    pub fn find_last_leaf(&self, mut cache: Option<&mut PathCache<K, V>>) -> LeafNode<K, V> {
        let mut cur: Self = self.clone();
        loop {
            match cur {
                Self::Leaf(leaf) => return leaf,
                Self::Inter(inter) => {
                    let idx = inter.key_count();
                    if let Some(_cache) = cache.as_mut() {
                        _cache.push(inter.clone(), idx);
                    }
                    cur = inter.get_child(idx);
                }
            }
        }
    }

    /*
    /// If depth == 0, return the root itself
    #[inline]
    pub fn find_child_with_cache(
        &self, cache: &mut PathCache<K, V>, key: &K, mut depth: u32,
    ) -> InterNode<K, V> {
        let mut cur = self.as_inter().clone();
        while depth > 0 {
            depth -= 1;
            let idx = cur.search_child(key);
            cache.push(cur.clone(), idx);
            cur = cur.get_child_as_inter(idx);
        }
        cur
    }
    */
}

macro_rules! _move_to_ancenstor {
    ($queue: expr, $cond: expr, $post: expr) => {{
        let mut res = None;
        // For dropping scenario, cannot move further, reach the end at root
        while let Some((grand_parent, idx)) = $queue.pop() {
            if $cond(&grand_parent, idx) {
                res.replace((grand_parent, idx));
                break;
            } else {
                ($post)(grand_parent);
            }
        }
        // grand_parent idx reach the end, will not visit again
        res
    }};
}

pub(super) struct PathCache<K, V> {
    /// < 0 means the cursor move left N times, > 0 means the cursor move right N times
    pos: isize,
    // Various<ptr> has 13 cap, which is quite enough for btree
    inner: Various<(InterNode<K, V>, u32)>,
}

impl<K: Ord, V> PathCache<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self { inner: Various::new(), pos: 0 }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.pos = 0;
    }

    /// Take the cache out, and make sure it's clear
    #[inline(always)]
    pub fn take(&mut self) -> Self {
        let mut inner = self.inner.take();
        inner.clear();
        Self { inner, pos: 0 }
    }

    #[inline(always)]
    pub fn assert_center(&self) {
        debug_assert_eq!(self.pos, 0);
    }

    #[inline]
    fn _move_left_and_pop<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(InterNode<K, V>),
    {
        while let Some((parent, idx)) = self.inner.pop() {
            debug_assert!(self.pos < 0);
            let move_step = (-self.pos) as u32;
            if idx > 0 {
                if move_step > idx {
                    self.pos += idx as isize;
                } else {
                    self.pos = 0;
                    return Some((parent, idx - move_step)); // have common parent
                }
            }
            let pre_height = parent.height();
            post_callback(parent);
            // only move 1 since we change the branch, leave the rest to the loop
            self.pos += 1;
            let cond = |_node: &InterNode<K, V>, idx: u32| -> bool { idx > 0 };
            // this is for entry API, we already know there is a previous node
            if let Some((grand_parent, grand_idx)) =
                _move_to_ancenstor!(self.inner, cond, post_callback)
            {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx - 1, false, Some(self));
                if self.pos == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move left
                    self.inner.push((parent, idx));
                }
            } else {
                return None;
            }
        }
        None
    }

    /// Return the last parent
    #[inline]
    fn _move_right_and_pop<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(InterNode<K, V>),
    {
        // move of the time move_step is just 1
        while let Some((parent, idx)) = self.inner.pop() {
            debug_assert!(self.pos > 0);
            let move_step = self.pos as u32;
            let right_count = parent.key_count() - idx;
            if right_count > 0 {
                if right_count < move_step {
                    self.pos -= right_count as isize;
                } else {
                    self.pos -= move_step as isize;
                    debug_assert_eq!(self.pos, 0);
                    return Some((parent, idx + move_step)); // have common parent
                }
            }
            let pre_height = parent.height();
            // parent idx reach the end, will not visit again
            post_callback(parent);
            // only move 1 since we change the branch, leave the rest to the loop
            self.pos -= 1;
            if let Some((grand_parent, grand_idx)) = _move_to_ancenstor!(
                self.inner,
                |node: &InterNode<K, V>, idx: u32| -> bool { node.key_count() > idx },
                post_callback
            ) {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx + 1, true, Some(self));
                if self.pos == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move right
                    self.inner.push((parent, idx));
                }
            } else {
                return None;
            }
        }
        None
    }

    #[inline(always)]
    pub fn peak_next(&self) -> Option<(InterNode<K, V>, u32)> {
        debug_assert_eq!(self.pos, 0);
        let (parent, idx) = self.inner.last()?;
        Some((parent.clone(), *idx))
    }

    /// iter backward through cache internal stack, without changing the cache,
    /// return None if reaches root
    #[inline(always)]
    pub fn peak_ancenstor<FC>(&mut self, cond: FC) -> Option<(InterNode<K, V>, u32)>
    where
        FC: Fn(&InterNode<K, V>, u32) -> bool,
    {
        let iter = self.inner.iter_rev();
        // For dropping scenario, cannot move further, reach the end at root
        for (grand_parent, idx) in iter {
            if cond(grand_parent, *idx) {
                return Some((grand_parent.clone(), *idx));
            }
        }
        // grand_parent idx reach the end, will not visit again
        None
    }

    /// pop cache until `cond` condition is met.
    /// return None if reaches root
    #[inline(always)]
    pub fn move_to_ancenstor<FC, FP>(
        &mut self, cond: FC, post_callback: FP,
    ) -> Option<(InterNode<K, V>, u32)>
    where
        FC: Fn(&InterNode<K, V>, u32) -> bool,
        FP: Fn(InterNode<K, V>),
    {
        _move_to_ancenstor!(self, cond, post_callback)
    }

    /// For moving the Entry position
    #[inline(always)]
    pub fn move_left(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        self.pos -= 1;
    }

    /// For moving the Entry position
    #[inline(always)]
    pub fn move_right(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        self.pos += 1;
    }

    #[inline(always)]
    pub fn push(&mut self, inter: InterNode<K, V>, idx: u32) {
        self.inner.push((inter, idx));
    }

    /// pop parent and its idx from cache, if we need new_root, return None
    #[inline(always)]
    pub fn pop(&mut self) -> Option<(InterNode<K, V>, u32)> {
        if self.pos < 0 {
            self._move_left_and_pop(dummy_post_callback::<K, V>)
        } else if self.pos > 0 {
            self._move_right_and_pop(dummy_post_callback::<K, V>)
        } else {
            self.inner.pop()
        }
    }

    // for dropping the tree, post order visit, `post_callback` should dealloc on the node
    #[inline(always)]
    pub fn move_right_and_pop_l1<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(InterNode<K, V>) + Clone,
    {
        self.pos += 1;
        self._move_right_and_pop(post_callback)
    }

    // for dropping the tree, post order visit in reversed order, `post_callback` should dealloc on the node
    #[inline(always)]
    pub fn move_left_and_pop_l1<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(InterNode<K, V>) + Clone,
    {
        self.pos -= 1;
        self._move_left_and_pop(post_callback)
    }
}

pub(super) fn dummy_post_callback<K, V>(_node: InterNode<K, V>) {}

#[inline(always)]
pub(super) fn borrow_key_from_bound<Q: ?Sized>(bound: Bound<&Q>) -> Option<&Q> {
    match bound {
        Bound::Unbounded => None,
        Bound::Included(key) => Some(key),
        Bound::Excluded(key) => Some(key),
    }
}
