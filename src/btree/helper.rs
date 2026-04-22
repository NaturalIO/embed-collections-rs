use super::inter::*;
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::marker::PhantomData;
use core::mem::{align_of, size_of};
use core::ptr::NonNull;

pub(super) fn dummy_post_callback<K: Ord, V>(_info: &mut TreeInfo<K, V>, _node: InterNode<K, V>) {}

macro_rules! _move_to_ancenstor {
    ($queue: expr, $pop: ident, $cond: expr, $post: expr) => {{
        let mut res = None;
        // For dropping scenario, cannot move further, reach the end at root
        while let Some((grand_parent, idx)) = $queue.$pop() {
            if $cond(&grand_parent, idx) {
                res.replace((grand_parent, idx));
                break;
            } else {
                ($post)($queue, grand_parent);
            }
        }
        // grand_parent idx reach the end, will not visit again
        res
    }};
}

/// Header stored at the start of the `TreeInfo` heap buffer.
///
/// Immediately followed by `[(InterNode<K,V>, u32); cap]` items.
#[repr(C)]
pub(super) struct TreeInfoHeader {
    pub leaf_count: usize,
    pub inter_count: u32,
    pub cap: u8,
    // the current heap, in the unit of CACHE_LINE_SIZE
    pub size: u8,
    pub cache_idx: u8,
    pub cache_pos: i8,
}

/// Compact heap-allocated metadata for `BTreeMap`.
///
/// Holds `leaf_count`, `inter_count`, and a growable path-cache stack in one
/// contiguous allocation, decoupled from the `BTreeMap` struct itself.
///
/// # Memory layout
/// `[TreeInfoHeader | (InterNode<K,V>, u32) × cap]`
///
/// Initial buffer = one `CACHE_LINE_SIZE` block; grows by one block per overflow.
pub(super) struct TreeInfo<K: Ord, V> {
    ptr: NonNull<TreeInfoHeader>,
    _marker: PhantomData<(K, V)>,
}

/// Reverse (top-of-stack → bottom) iterator produced by [`TreeInfo::_iter`].
pub(super) struct TreeInfoIter<'a, K: Ord, V> {
    info: &'a TreeInfo<K, V>,
    idx: u8,
}

impl<'a, K: Ord, V> Iterator for TreeInfoIter<'a, K, V> {
    type Item = (&'a InterNode<K, V>, u32);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == 0 {
            return None;
        }
        self.idx -= 1;
        Some(unsafe { self.info._get(self.idx) })
    }
}

impl<K: Ord, V> TreeInfo<K, V> {
    // Size/align of one stack entry.
    const ITEM_SIZE: usize = size_of::<(InterNode<K, V>, u32)>();
    // Offset at which items start (header size rounded up to item alignment).
    const ITEMS_OFFSET: usize = {
        let hs = size_of::<TreeInfoHeader>();
        let ia = align_of::<(InterNode<K, V>, u32)>();
        (hs + ia - 1) & !(ia - 1)
    };
    // Buffer alignment: max of header and item alignments.
    const BUF_ALIGN: usize = {
        let ha = align_of::<TreeInfoHeader>();
        let ia = align_of::<(InterNode<K, V>, u32)>();
        if ha > ia { ha } else { ia }
    };

    #[inline(always)]
    const fn cal_cap(buf_size: usize) -> u8 {
        ((buf_size - Self::ITEMS_OFFSET) / Self::ITEM_SIZE) as u8
    }

    #[inline(always)]
    const fn buf_size(size: u8) -> usize {
        size as usize * CACHE_LINE_SIZE
    }

    #[inline(always)]
    const fn get_layout(buf_size: usize) -> Layout {
        unsafe { Layout::from_size_align_unchecked(buf_size, Self::BUF_ALIGN) }
    }

    #[inline]
    pub fn new(leaf_count: usize, inter_count: u32) -> Self {
        let init_size = 1u8;
        let buf_size = Self::buf_size(init_size);
        unsafe {
            let layout = Self::get_layout(buf_size);
            let p = alloc(layout);
            if p.is_null() {
                handle_alloc_error(layout);
            }
            let ptr = NonNull::new_unchecked(p as *mut TreeInfoHeader);
            ptr.as_ptr().write(TreeInfoHeader {
                leaf_count,
                inter_count,
                size: init_size,
                cap: Self::cal_cap(buf_size),
                cache_idx: 0,
                cache_pos: 0,
            });
            Self { ptr, _marker: PhantomData }
        }
    }

    #[inline]
    fn header(&self) -> &TreeInfoHeader {
        unsafe { self.ptr.as_ref() }
    }

    #[inline]
    fn header_mut(&mut self) -> &mut TreeInfoHeader {
        unsafe { self.ptr.as_mut() }
    }

    #[inline]
    unsafe fn item_ptr(&self, idx: u8) -> *mut (InterNode<K, V>, u32) {
        unsafe {
            (self.ptr.as_ptr() as *mut u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE)
                as *mut _
        }
    }

    #[inline]
    unsafe fn _get(&self, idx: u8) -> (&InterNode<K, V>, u32) {
        unsafe {
            let p = &*self.item_ptr(idx);
            (&p.0, p.1)
        }
    }

    #[inline]
    pub fn ensure_cap(&mut self, height: u32) {
        let header = self.header_mut();
        if height <= header.cap as u32 {
            return;
        }
        // grow one CACHE_LINE_SIZE each time
        let old_layout = Self::get_layout(Self::buf_size(header.size));
        let new_size = Self::buf_size(header.size + 1);
        unsafe {
            let p = realloc(self.ptr.as_ptr() as *mut u8, old_layout, new_size);
            if p.is_null() {
                handle_alloc_error(Self::get_layout(new_size));
            }
            self.ptr = NonNull::new_unchecked(p as *mut TreeInfoHeader);
        }
        let header = self.header_mut();
        header.cap = Self::cal_cap(new_size);
        header.size += 1;
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    pub fn _push(&mut self, inter: InterNode<K, V>, idx: u32) {
        let header = self.header_mut();
        let wi = header.cache_idx;
        debug_assert!(wi < header.cap);
        header.cache_idx = wi + 1;
        unsafe { self.item_ptr(wi).write((inter, idx)) };
    }

    /// Pop the top entry from the cache stack.
    #[inline]
    pub fn _pop(&mut self) -> Option<(InterNode<K, V>, u32)> {
        unsafe {
            let header = self.ptr.as_mut();
            if header.cache_idx == 0 {
                return None;
            }
            header.cache_idx -= 1;
            Some(self.item_ptr(header.cache_idx).read())
        }
    }

    /// Reverse (top → bottom) iterator over the stack without consuming it.
    #[inline]
    pub fn _iter(&self) -> TreeInfoIter<'_, K, V> {
        TreeInfoIter { info: self, idx: self.header().cache_idx }
    }

    /// Peek at the top of the stack (equivalent to `Various::last`).
    #[inline]
    pub fn _last(&self) -> Option<(&InterNode<K, V>, u32)> {
        let idx = self.header().cache_idx;
        if idx == 0 { None } else { Some(unsafe { self._get(idx - 1) }) }
    }

    #[inline]
    pub fn leaf_count(&self) -> usize {
        self.header().leaf_count
    }

    #[inline(always)]
    pub fn inc_leaf_count(&mut self) {
        self.header_mut().leaf_count += 1;
    }

    #[inline(always)]
    pub fn dec_leaf_count(&mut self) {
        self.header_mut().leaf_count -= 1;
    }

    #[inline(always)]
    pub fn inc_inter_count(&mut self) {
        self.header_mut().inter_count += 1;
    }

    #[inline(always)]
    pub fn dec_inter_count(&mut self) {
        self.header_mut().inter_count -= 1;
    }

    /// Reset the stack without freeing the buffer.
    #[inline]
    pub fn clear(&mut self) {
        let header = self.header_mut();
        header.cache_idx = 0;
        header.cache_pos = 0;
    }

    #[inline(always)]
    pub fn assert_center(&self) {
        debug_assert_eq!(self.header().cache_pos, 0);
    }

    #[inline]
    fn _move_left_and_pop<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(&mut Self, InterNode<K, V>),
    {
        while let Some((parent, idx)) = self._pop() {
            let header = self.header_mut();
            debug_assert!(header.cache_pos < 0);
            let move_step = (-header.cache_pos) as u32;
            if idx > 0 {
                if move_step > idx {
                    header.cache_pos += idx as i8;
                } else {
                    header.cache_pos = 0;
                    return Some((parent, idx - move_step)); // have common parent
                }
            }
            // only move 1 since we change the branch, leave the rest to the loop
            header.cache_pos += 1;
            let pre_height = parent.height();
            post_callback(self, parent);
            let cond = |_node: &InterNode<K, V>, idx: u32| -> bool { idx > 0 };
            // this is for entry API, we already know there is a previous node
            if let Some((grand_parent, grand_idx)) =
                _move_to_ancenstor!(self, _pop, cond, post_callback)
            {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx - 1, false, Some(self));
                if self.header().cache_pos == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move left
                    self._push(parent, idx);
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
        F: Fn(&mut Self, InterNode<K, V>),
    {
        // move of the time move_step is just 1
        while let Some((parent, idx)) = self._pop() {
            let header = self.header_mut();
            debug_assert!(header.cache_pos > 0);
            let move_step = header.cache_pos as u32;
            let right_count = parent.key_count() - idx;
            if right_count > 0 {
                if right_count < move_step {
                    header.cache_pos -= right_count as i8;
                } else {
                    header.cache_pos -= move_step as i8;
                    debug_assert_eq!(self.header().cache_pos, 0);
                    return Some((parent, idx + move_step)); // have common parent
                }
            }
            // parent idx reach the end, will not visit again
            let pre_height = parent.height();
            header.cache_pos -= 1;
            post_callback(self, parent);
            // only move 1 since we change the branch, leave the rest to the loop
            if let Some((grand_parent, grand_idx)) = _move_to_ancenstor!(
                self,
                _pop,
                |node: &InterNode<K, V>, idx: u32| -> bool { node.key_count() > idx },
                post_callback
            ) {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx + 1, true, Some(self));
                if self.header().cache_pos == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move right
                    self._push(parent, idx);
                }
            } else {
                return None;
            }
        }
        None
    }

    #[inline(always)]
    pub fn peak_next(&self) -> Option<(InterNode<K, V>, u32)> {
        debug_assert_eq!(self.header().cache_pos, 0);
        let (parent, idx) = self._last()?;
        Some((parent.clone(), idx))
    }

    /// iter backward through cache internal stack, without changing the cache,
    /// return None if reaches root
    #[inline(always)]
    pub fn peak_ancenstor<FC>(&self, cond: FC) -> Option<(InterNode<K, V>, u32)>
    where
        FC: Fn(&InterNode<K, V>, u32) -> bool,
    {
        self.assert_center();
        let iter = self._iter();
        // For dropping scenario, cannot move further, reach the end at root
        for (grand_parent, idx) in iter {
            if cond(grand_parent, idx) {
                return Some((grand_parent.clone(), idx));
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
        FP: Fn(&mut Self, InterNode<K, V>),
    {
        // Self::pop() will detect pos and fix position
        _move_to_ancenstor!(self, pop, cond, post_callback)
    }

    /// For moving the Entry position
    #[inline(always)]
    pub fn move_left(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        let mut header = self.header_mut();
        if header.cache_pos > i8::MIN {
            header.cache_pos -= 1;
            return;
        }
        self._fix_center_from_left();
        header = self.header_mut();
        header.cache_pos -= 1;
    }

    /// For moving the Entry position
    #[inline(always)]
    pub fn move_right(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        let mut header = self.header_mut();
        if header.cache_pos < i8::MAX {
            header.cache_pos += 1;
            return;
        }
        self._fix_center_from_right();
        header = self.header_mut();
        header.cache_pos += 1;
    }

    #[inline(always)]
    pub fn _fix_center_from_left(&mut self) {
        debug_assert!(self.header().cache_pos < 0);
        if let Some((parent, idx)) = self._move_left_and_pop(dummy_post_callback::<K, V>) {
            self._push(parent, idx);
        }
    }

    #[inline(always)]
    pub fn _fix_center_from_right(&mut self) {
        debug_assert!(self.header().cache_pos > 0);
        if let Some((parent, idx)) = self._move_right_and_pop(dummy_post_callback::<K, V>) {
            self._push(parent, idx);
        }
    }

    #[inline(always)]
    pub fn push(&mut self, inter: InterNode<K, V>, idx: u32) {
        self.assert_center();
        self._push(inter, idx);
    }

    /// pop parent and its idx from cache, if we need new_root, return None
    #[inline(always)]
    pub fn pop(&mut self) -> Option<(InterNode<K, V>, u32)> {
        let pos = self.header().cache_pos;
        if pos == 0 {
            self._pop()
        } else if pos > 0 {
            crate::trace_log!("pop: {pos}");
            self._move_right_and_pop(dummy_post_callback::<K, V>)
        } else {
            debug_assert!(pos < 0);
            self._move_left_and_pop(dummy_post_callback::<K, V>)
        }
    }

    // for dropping the tree, post order visit, `post_callback` should dealloc on the node
    #[inline(always)]
    pub fn move_right_and_pop_l1<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(&mut Self, InterNode<K, V>) + Clone,
    {
        let header = self.header_mut();
        if header.cache_pos < i8::MAX {
            header.cache_pos += 1;
            return self._move_right_and_pop(post_callback);
        }
        self._fix_center_from_right();
        let header = self.header_mut();
        header.cache_pos += 1;
        self._move_right_and_pop(post_callback)
    }

    // for dropping the tree, post order visit in reversed order, `post_callback` should dealloc on the node
    #[inline(always)]
    pub fn move_left_and_pop_l1<F>(&mut self, post_callback: F) -> Option<(InterNode<K, V>, u32)>
    where
        F: Fn(&mut Self, InterNode<K, V>) + Clone,
    {
        let header = self.header_mut();
        if header.cache_pos > i8::MIN {
            header.cache_pos -= 1;
            return self._move_left_and_pop(post_callback);
        }
        self._fix_center_from_left();
        let header = self.header_mut();
        header.cache_pos -= 1;
        self._move_left_and_pop(post_callback)
    }
}

impl<K: Ord, V> Drop for TreeInfo<K, V> {
    #[inline]
    fn drop(&mut self) {
        let header = self.header();
        let size = Self::buf_size(header.size);
        unsafe {
            // InterNode does not have drop
            dealloc(self.ptr.as_ptr() as *mut u8, Self::get_layout(size));
        }
    }
}
