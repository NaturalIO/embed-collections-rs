use super::{BTree, entry::*, helper::PathBuffer, inter::*, tree::BTreeInner, *};
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::fmt::{self, Debug};
use core::marker::PhantomData;
use core::mem::{align_of, size_of};
use core::ptr::null_mut;
use core::sync::atomic::{
    AtomicPtr,
    Ordering::{Acquire, Relaxed, Release},
};

#[allow(private_bounds)]
pub(super) trait Stats<K: Key>: Default + Send + Debug + 'static {
    #[allow(private_bounds)]
    type EntryInner<'a, V>: EntryInner<K, V>
    where
        V: Value + 'a;

    #[allow(private_bounds)]
    type PathBufferRef<'a>: PathBuffer<K>
    where
        K: 'a,
        Self: 'a;

    // owned for IntoIter and drop
    #[allow(private_bounds)]
    type PathBuffer: PathBuffer<K>;

    fn get_cache<'a>(&'a self, height: u8) -> Self::PathBufferRef<'a>;

    fn take_cache(self, height: u8) -> Self::PathBuffer;

    /// Reset the stack without freeing the buffer.
    fn clear_cache(&self);

    #[cfg(test)]
    fn init_count(&self, leaf_count: usize, inter_count: u32);

    #[allow(private_bounds)]
    fn make_entry<'a, V: Value>(
        tree: &'a mut BTree<K, V, Self>, idx: u8,
    ) -> Self::EntryInner<'a, V>;

    #[cfg(test)]
    fn assert_leaf_count(&self, _leaf_count: usize) {}

    #[cfg(test)]
    fn assert_inter_count(&self, _inter_count: usize) {}
}

/// Header stored at the start of the `TreeInfo` heap buffer.
///
/// Immediately followed by `[(InterNode<K,V>, u8); cap]` items.
#[repr(C)]
struct TreeInfoHeader {
    leaf_count: usize,
    inter_count: u32,
    cap: u8,
    // the current heap, in the unit of CACHE_LINE_SIZE
    size: u8,
    // array items count
    buffer_idx: u8,
    // left / right
    buffer_pos: i8,
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
pub struct TreeInfo<K> {
    // because PathBuffer should support mut during query tree, we need inner muttabilty
    ptr: AtomicPtr<TreeInfoHeader>,
    _phan: PhantomData<fn(&K)>,
}

impl<K> Default for TreeInfo<K> {
    fn default() -> Self {
        Self { ptr: AtomicPtr::new(null_mut()), _phan: Default::default() }
    }
}

pub(crate) struct TreeInfoEntry<'a, K, V>
where
    K: Key,
    V: Value,
{
    tree: &'a mut BTree<K, V, TreeInfo<K>>,
    idx: u8,
}

impl<'a, K: Key, V: Value> EntryInner<K, V> for TreeInfoEntry<'a, K, V> {
    type PathBuffer = TreeInfo<K>;

    #[inline(always)]
    fn get_cache(&self) -> &TreeInfo<K> {
        &self.tree.stats
    }

    #[cfg(test)]
    #[inline(always)]
    fn get_tree(&self) -> &BTreeInner<K, V> {
        &self.tree.inner
    }

    #[inline(always)]
    fn get_tree_cache(&mut self) -> (&mut BTreeInner<K, V>, &TreeInfo<K>) {
        (&mut self.tree.inner, &self.tree.stats)
    }

    #[inline(always)]
    fn set_idx(&mut self, idx: u8) {
        self.idx = idx;
    }

    #[inline(always)]
    fn get_idx(&self) -> u8 {
        self.idx
    }
}

unsafe impl<K> Send for TreeInfo<K> {}
unsafe impl<K> Sync for TreeInfo<K> {}

// for log
impl<K> Debug for TreeInfo<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TreeInfo")
    }
}

impl<K: Key> Stats<K> for TreeInfo<K> {
    type EntryInner<'a, V>
        = TreeInfoEntry<'a, K, V>
    where
        V: Value + 'a;

    type PathBufferRef<'a>
        = &'a TreeInfo<K>
    where
        K: 'a,
        Self: 'a;
    type PathBuffer = TreeInfo<K>;

    #[inline]
    fn get_cache(&self, height: u8) -> &Self {
        self.ensure_cap(height);
        self.clear_cache();
        self
    }

    #[inline]
    fn take_cache(self, height: u8) -> Self {
        self.ensure_cap(height);
        self.clear_cache();
        self
    }

    /// Reset the stack without freeing the buffer.
    #[inline]
    fn clear_cache(&self) {
        if let Some(header) = self.header_mut() {
            header.buffer_idx = 0;
            header.buffer_pos = 0;
        }
    }

    #[cfg(test)]
    fn init_count(&self, leaf_count: usize, inter_count: u32) {
        if let Some(header) = self.header_mut() {
            header.leaf_count = leaf_count;
            header.inter_count = inter_count;
        } else {
            self._alloc(leaf_count, inter_count);
        }
    }

    #[inline]
    fn make_entry<'a, V: Value + 'static>(
        tree: &'a mut BTree<K, V, Self>, idx: u8,
    ) -> Self::EntryInner<'a, V> {
        TreeInfoEntry { tree, idx }
    }

    #[cfg(test)]
    fn assert_leaf_count(&self, leaf_count: usize) {
        assert_eq!(self.leaf_count(), leaf_count);
    }

    #[cfg(test)]
    fn assert_inter_count(&self, inter_count: usize) {
        assert_eq!(self.inter_count() as usize, inter_count);
    }
}

impl<K: Ord> PathBuffer<K> for TreeInfo<K> {
    type Iter<'a>
        = TreeInfoIter<'a, K>
    where
        Self: 'a,
        K: 'a;

    // --- stats method begins ---

    #[inline(always)]
    fn inc_leaf_count(&self) {
        if let Some(header) = self.header_mut() {
            header.leaf_count += 1;
        } else {
            self._alloc(2, 1);
        }
    }

    #[inline(always)]
    fn dec_leaf_count(&self) {
        self.header_mut_unwrap().leaf_count -= 1;
    }
    #[inline(always)]
    fn inc_inter_count(&self) {
        if let Some(header) = self.header_mut() {
            header.inter_count += 1;
        } else {
            self._alloc(2, 1);
        }
    }

    #[inline(always)]
    fn dec_inter_count(&self) {
        self.header_mut_unwrap().inter_count -= 1;
    }

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        if let Some(header) = self.header() { header.buffer_idx } else { 0 }
    }

    #[inline]
    fn ensure_cap(&self, height: u8) {
        assert!(height < u8::MAX);
        if height == 0 {
            return;
        }
        let header = self.ptr.load(Acquire);
        if !header.is_null() {
            unsafe {
                if height <= (*header).cap {
                    return;
                } else {
                    // grow one CACHE_LINE_SIZE each time
                    let old_layout = Self::get_layout(Self::buf_size((*header).size));
                    let new_size = Self::buf_size((*header).size + 1);
                    let p = realloc(header as *mut u8, old_layout, new_size);
                    if p.is_null() {
                        handle_alloc_error(Self::get_layout(new_size));
                    }
                    let header = p as *mut TreeInfoHeader;
                    (*header).cap = Self::cal_cap(new_size);
                    (*header).size += 1;
                    self.ptr.store(header, Release);
                }
            }
        } else {
            self._alloc(2, 1);
        }
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    #[inline]
    fn buffer_pos(&self) -> i8 {
        if let Some(header) = self.header() { header.buffer_pos } else { 0 }
    }

    #[inline]
    fn move_pos(&self, delta: i8) {
        if let Some(header) = self.header_mut() {
            header.buffer_pos += delta;
        }
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    fn _push(&self, inter: InterNode<K>, idx: u8) {
        if let Some(header) = self.header_mut() {
            let wi = header.buffer_idx;
            debug_assert!(wi < header.cap, "{wi} {}", header.cap);
            header.buffer_idx = wi + 1;
            unsafe { self.item_ptr_mut(wi).write((inter, idx)) };
        }
    }

    /// Pop the top entry from the cache stack.
    #[inline]
    fn _pop(&self) -> Option<(InterNode<K>, u8)> {
        let header = self.header_mut()?;
        if header.buffer_idx == 0 {
            return None;
        }
        header.buffer_idx -= 1;
        unsafe { Some(self.item_ptr(header.buffer_idx).read()) }
    }

    /// Reverse (top → bottom) iterator over the stack without consuming it.
    #[inline]
    fn iter<'a>(&'a self) -> TreeInfoIter<'a, K> {
        if let Some(header) = self.header() {
            TreeInfoIter { info: self, idx: header.buffer_idx }
        } else {
            TreeInfoIter { info: self, idx: 0 }
        }
    }

    /// Peek at the top of the stack (equivalent to `Various::last`).
    #[inline]
    fn last(&self) -> Option<(&InterNode<K>, u8)> {
        let idx = self.buffer_len();
        if idx == 0 { None } else { Some(unsafe { self._get(idx - 1) }) }
    }
}

impl<K> TreeInfo<K> {
    // Size/align of one stack entry.
    const ITEM_SIZE: usize = size_of::<(InterNode<K>, u8)>();
    // Offset at which items start (header size rounded up to item alignment).
    const ITEMS_OFFSET: usize = {
        let hs = size_of::<TreeInfoHeader>();
        let ia = align_of::<(InterNode<K>, u8)>();
        (hs + ia - 1) & !(ia - 1)
    };
    // Buffer alignment: max of header and item alignments.
    const BUF_ALIGN: usize = {
        let ha = align_of::<TreeInfoHeader>();
        let ia = align_of::<(InterNode<K>, u8)>();
        if ha > ia { ha } else { ia }
    };

    #[inline]
    pub fn leaf_count(&self) -> usize {
        if let Some(header) = self.header() { header.leaf_count } else { 1 }
    }

    #[inline(always)]
    pub fn inter_count(&self) -> u32 {
        if let Some(header) = self.header() { header.inter_count } else { 0 }
    }

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
    fn _alloc(&self, leaf_count: usize, inter_count: u32) {
        let init_size = 1u8;
        let buf_size = Self::buf_size(init_size);
        unsafe {
            let layout = Self::get_layout(buf_size);
            let p = alloc(layout);
            if p.is_null() {
                handle_alloc_error(layout);
            }
            let header = p as *mut TreeInfoHeader;
            header.write(TreeInfoHeader {
                leaf_count,
                inter_count,
                size: init_size,
                cap: Self::cal_cap(buf_size),
                buffer_idx: 0,
                buffer_pos: 0,
            });
            debug_assert!(self.ptr.load(Relaxed).is_null());
            self.ptr.store(header, Relaxed);
        }
    }

    #[inline]
    fn header(&self) -> Option<&TreeInfoHeader> {
        let p = self.ptr.load(Relaxed);
        if !p.is_null() { Some(unsafe { &*p }) } else { None }
    }

    #[inline]
    fn header_mut(&self) -> Option<&mut TreeInfoHeader> {
        let p = self.ptr.load(Relaxed);
        if !p.is_null() { Some(unsafe { &mut *p }) } else { None }
    }

    #[inline]
    fn header_mut_unwrap(&self) -> &mut TreeInfoHeader {
        let p = self.ptr.load(Relaxed);
        debug_assert!(!p.is_null());
        unsafe { &mut *p }
    }

    #[inline]
    unsafe fn item_ptr(&self, idx: u8) -> *const (InterNode<K>, u8) {
        let p = self.ptr.load(Relaxed);
        unsafe {
            (p as *const u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE) as *const _
        }
    }

    #[inline]
    unsafe fn item_ptr_mut(&self, idx: u8) -> *mut (InterNode<K>, u8) {
        let p = self.ptr.load(Relaxed);
        unsafe { (p as *mut u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE) as *mut _ }
    }

    #[inline]
    unsafe fn _get(&self, idx: u8) -> (&InterNode<K>, u8) {
        unsafe {
            let p = &*self.item_ptr(idx);
            (&p.0, p.1)
        }
    }
}

impl<K> Drop for TreeInfo<K> {
    #[inline]
    fn drop(&mut self) {
        let p = *self.ptr.get_mut();
        if !p.is_null() {
            unsafe {
                let size = Self::buf_size((*p).size);
                // InterNode does not have drop
                dealloc(p as *mut u8, Self::get_layout(size));
            }
        }
    }
}

/// Reverse (top-of-stack → bottom) iterator produced by [`TreeInfo::_iter`].
pub(super) struct TreeInfoIter<'a, K: 'a> {
    info: &'a TreeInfo<K>,
    idx: u8,
}

impl<'a, K: 'a> Iterator for TreeInfoIter<'a, K> {
    type Item = (&'a InterNode<K>, u8);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx > 0 {
            self.idx -= 1;
            Some(unsafe { self.info._get(self.idx) })
        } else {
            None
        }
    }
}
