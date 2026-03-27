use super::{inter::*, leaf::*};
use crate::{CACHE_LINE_SIZE, Various};
use alloc::alloc::{Layout, alloc, handle_alloc_error};
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
        unsafe {
            NodeHeader::get_field::<T>(self.header, start_offset + idx as usize * size_of::<T>())
        }
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
    pub fn _search<K>(&self, header_offset: usize, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
        // TODO review this
        macro_rules! _search {
            ($start: expr, $end: expr) => {
                let mut idx = $start as u32;
                if $start < $end {
                    let mut k = self.item_ptr::<K>(header_offset, $start as u32);
                    loop {
                        if *k == *key {
                            return (idx, true);
                        } else if (*k) > *key {
                            // insert to this pos, idx should move right
                            return (idx, false);
                        }
                        idx += 1;
                        k = k.add(1);
                        if idx == $end as u32 {
                            break;
                        }
                    }
                    // NOTE: be aware to check idx == cap
                }
                return (idx, false);
            };
        }

        unsafe {
            let count = self.key_count();
            let first_line_bytes = CACHE_LINE_SIZE - header_offset;
            let first_line_limit = (first_line_bytes / size_of::<K>()) as u32;
            if count > first_line_limit
                && *key > (*self.item_ptr::<K>(header_offset, first_line_limit - 1))
            {
                _search!(first_line_limit, count);
            } else {
                _search!(0, count);
            }
        }
    }

    /// Insert key value at position and return value pointer (entry insert needs to return reference)
    ///
    /// # Safety
    /// it does not check is_full
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

impl<K: Ord, V> Node<K, V> {
    #[inline(always)]
    pub unsafe fn from_header(header: *mut NodeHeader) -> Self {
        unsafe {
            if (*header).is_leaf() {
                Node::Leaf(LeafNode::<K, V>::from_header(header))
            } else {
                Node::Inter(InterNode::<K, V>::from_header(header))
            }
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

    #[inline]
    pub fn as_inter(&self) -> &InterNode<K, V> {
        if let Node::Inter(node) = &self {
            node
        } else {
            unreachable!();
        }
    }

    #[inline]
    pub fn into_inter(self) -> InterNode<K, V> {
        if let Node::Inter(node) = self {
            node
        } else {
            unreachable!();
        }
    }

    #[inline]
    pub fn find_leaf(&self, key: &K) -> LeafNode<K, V> {
        match self {
            Node::Leaf(node) => node.clone(),
            Node::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let idx = cur.search_child(key);
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
    pub fn clone_first_key(&self) -> K
    where
        K: Clone,
    {
        match self {
            Node::Inter(node) => node.clone_first_key(),
            Node::Leaf(node) => node.clone_first_key(),
        }
    }

    #[inline]
    pub fn find_leaf_with_cache(&self, cache: &mut PathCache<K, V>, key: &K) -> LeafNode<K, V> {
        match &self {
            Node::Leaf(node) => node.clone(),
            Node::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let idx = cur.search_child(key);
                    cache.push(cur.clone(), idx);
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

    #[inline(always)]
    pub fn assert_center(&self) {
        debug_assert_eq!(self.pos, 0);
    }

    #[inline]
    fn _move_left_and_pop(&mut self) -> Option<(InterNode<K, V>, u32)> {
        while let Some((parent, idx)) = self.inner.pop() {
            debug_assert!(self.pos < 0);
            let move_step = (-self.pos) as u32;
            if idx > 0 {
                if move_step > idx {
                    self.pos += idx as isize;
                } else {
                    debug_assert_eq!(self.pos, 0);
                    self.pos += move_step as isize;
                    return Some((parent, idx - move_step)); // have common parent
                }
            }
            let pre_height = parent.height();
            // only move 1 since we change the branch, leave the rest to the loop
            self.pos += 1;
            let cond = |_node: &InterNode<K, V>, idx: u32| -> bool { idx > 0 };
            // this is for entry API, we already know there is a previous node
            let (grand_parent, grand_idx) =
                _move_to_ancenstor!(self.inner, cond, dummy_post_callback::<K, V>).unwrap();
            let (parent, idx) =
                grand_parent.find_child_branch(pre_height, grand_idx - 1, false, Some(self));
            if self.pos == 0 {
                return Some((parent, idx));
            } else {
                // continue to move left
                self.inner.push((parent, idx));
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

    /// iter backward through cache internal stack, without changing the cache,
    /// return None if reaches root
    #[inline(always)]
    pub fn peak_ancenstor<FC>(&mut self, cond: FC) -> Option<(&InterNode<K, V>, u32)>
    where
        FC: Fn(&InterNode<K, V>, u32) -> bool,
    {
        let iter = self.inner.iter_rev();
        // For dropping scenario, cannot move further, reach the end at root
        for (grand_parent, idx) in iter {
            if cond(grand_parent, *idx) {
                return Some((grand_parent, *idx));
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
            self._move_left_and_pop()
        } else if self.pos > 0 {
            self._move_right_and_pop(|_node| {})
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
}

pub(super) const MERGE_LEFT: u8 = 1;
pub(super) const MERGE_RIGHT: u8 = 2;

pub(super) fn dummy_post_callback<K, V>(_node: InterNode<K, V>) {}
