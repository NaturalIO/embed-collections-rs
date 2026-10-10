use crate::CACHE_LINE_SIZE;
use crate::btree::{
    self, BTree, entry::*, helper::PathBuffer, inter::*, leaf::*, node::*, tree::BTreeInner, *,
};
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::fmt::{self, Debug};
use core::mem::{align_of, size_of};
use core::num::NonZeroUsize;

pub type BTreeMap<K, V> = btree::BTree<K, V, TreeInfo>;
pub use btree::cursor::Cursor;
pub use btree::iter::{Iter, IterMut, Keys, Range, RangeMut, Values, ValuesMut};
pub type IntoIter<K, V> = btree::iter::IntoIter<K, V, TreeInfo>;
pub type Entry<'a, K, V> = btree::entry::Entry<'a, K, V, TreeInfo>;
pub type OccupiedEntry<'a, K, V> = btree::entry::OccupiedEntry<'a, K, V, TreeInfo>;
pub type VacantEntry<'a, K, V> = btree::entry::VacantEntry<'a, K, V, TreeInfo>;

/// Header stored at the start of the `TreeInfo` heap buffer.
///
/// Immediately followed by `[(InterNode<K,V>, u8); cap]` items.
#[repr(C)]
struct TreeInfoHeader {
    leaf_count: usize,
    inter_count: u32,
    /// Capacity of items can be stored except root
    cap: u8,
    entry_idx: u8,
    /// len=1 means root is pushed (as root idx),
    /// len-1 is the items stored in the heap.
    len: u8,
    /// left < 0, or right > 0, or center = 0
    buffer_pos: i8,
}

/// Compact heap-allocated metadata for `BTreeMap`.
///
/// Holds `leaf_count`, `inter_count`, and a growable path-cache stack in one
/// contiguous allocation, decoupled from the `BTreeMap` struct itself.
///
/// # Heap memory layout
///
/// `[TreeInfoHeader | (InterNode<K,V>, u32) × cap]`
///
/// Initial buffer = one `CACHE_LINE_SIZE` block; grows by one block per overflow.
///
/// # Stack memory layout
///
/// TreeInfo store either point, or ((entry_idx) << 8) | EMPTY_FLAG.
///
/// Because in our scenario iteration with `Entry` is hot path, to reduce moving cost, we pack
/// entry_idx inside TreeInfo stack or Heap (`TreeInfoHeader`)
///
/// NOTE: we tried enum u8 and NonNull, but rustc does not pack it to usize.
///
/// Using NonZeroUsize will optimize `Option<BTreeMap>`
pub struct TreeInfo(NonZeroUsize);

const EMPTY_FLAG: usize = 1;

unsafe impl Send for TreeInfo {}
unsafe impl Sync for TreeInfo {}

impl Default for TreeInfo {
    #[inline]
    fn default() -> Self {
        Self(unsafe { NonZeroUsize::new_unchecked(EMPTY_FLAG) })
    }
}

// for log
impl Debug for TreeInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TreeInfo")
    }
}

impl Stats for TreeInfo {}

impl StatsPriv for TreeInfo {
    type EntryInner<'a, K, V>
        = TreeInfoEntry<'a, K, V>
    where
        K: Key + 'a,
        V: Value + 'a;

    type PathBufferRef<'a> = &'a mut Self;

    type PathBuffer = Self;

    type BufferStack = ();

    #[inline]
    fn get_cache<'a, K>(&'a mut self, _stack: &mut (), root: Option<InterNode<K>>) -> &'a mut Self {
        self.clear_cache();
        if let Some(root) = root.as_ref() {
            self.ensure_cap(root.height());
        }
        self
    }

    #[inline]
    fn take_cache<K>(mut self, root: Option<InterNode<K>>) -> Self {
        self.clear_cache();
        if let Some(root) = root.as_ref() {
            self.ensure_cap(root.height());
        }
        self
    }

    #[cfg(test)]
    fn init_count(&mut self, leaf_count: usize, inter_count: u32) {
        if let Ok(header) = self.header_mut() {
            header.leaf_count = leaf_count;
            header.inter_count = inter_count;
        } else {
            self._alloc(leaf_count, inter_count, 0);
        }
    }

    #[inline]
    fn search_entry<'a, K: Key, V: Value>(
        tree: &'a mut BTree<K, V, Self>, key: K,
    ) -> Entry<'a, K, V> {
        if let Some(root) = tree.inner.get_root() {
            let mut is_seq = true;
            let leaf = match root {
                Node::Inter(inter) => {
                    let mut stack = ();
                    let mut cache = tree.stats.get_cache(&mut stack, Some(inter.clone()));
                    inter.find_leaf_with_cache_smart::<K, V, _>(&mut cache, &key, &mut is_seq)
                }
                Node::Leaf(leaf) => {
                    tree.stats.clear_cache();
                    leaf
                }
            };
            let (idx, is_equal) = leaf.search_smart(&key, is_seq);
            let mut inner = TreeInfoEntry { tree };
            inner.set_idx(idx);
            if is_equal {
                Entry::Occupied(OccupiedEntry { inner, leaf })
            } else {
                Entry::Vacant(VacantEntry { inner, key, leaf: Some(leaf) })
            }
        } else {
            let mut inner = TreeInfoEntry { tree };
            inner.set_idx(0);
            Entry::Vacant(VacantEntry { inner, key, leaf: None })
        }
    }

    /// seek first or last entry
    #[inline]
    fn seek_entry<'a, K: Key, V: Value, const FIRST: bool>(
        tree: &'a mut BTree<K, V, Self>,
    ) -> Option<OccupiedEntry<'a, K, V>> {
        if let Some(root) = tree.inner.get_root() {
            let leaf = match root {
                Node::Inter(inter) => {
                    let mut stack = ();
                    let mut cache = tree.stats.get_cache(&mut stack, Some(inter.clone()));
                    if FIRST {
                        inter.find_first_leaf_with_cache::<V, _>(&mut cache)
                    } else {
                        inter.find_last_leaf_with_cache::<V, _>(&mut cache)
                    }
                }
                Node::Leaf(leaf) => {
                    // make sure buffer_pos is clear
                    tree.stats.clear_cache();
                    leaf
                }
            };
            let count = leaf.key_count();
            if count > 0 {
                let mut inner = TreeInfoEntry { tree };
                if FIRST {
                    inner.set_idx(0);
                } else {
                    inner.set_idx(count - 1);
                };
                return Some(OccupiedEntry { inner, leaf });
            }
        }
        None
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

pub(crate) struct TreeInfoEntry<'a, K, V>
where
    K: Key,
    V: Value,
{
    tree: &'a mut BTree<K, V, TreeInfo>,
}

impl<'a, K: Key, V: Value> EntryInner<K, V> for TreeInfoEntry<'a, K, V> {
    #[inline(always)]
    fn get_cache(&mut self) -> impl PathBuffer {
        &mut self.tree.stats
    }

    #[cfg(test)]
    #[inline(always)]
    fn get_tree(&self) -> &BTreeInner<K, V> {
        &self.tree.inner
    }

    #[inline(always)]
    fn get_tree_cache(&mut self) -> (&mut BTreeInner<K, V>, impl PathBuffer) {
        let (tree, stats) = (&mut self.tree.inner, &mut self.tree.stats);
        (tree, stats)
    }

    #[inline(always)]
    fn set_idx(&mut self, idx: u8) {
        self.tree.stats.set_entry_idx(idx);
    }

    #[inline(always)]
    fn get_idx(&self) -> u8 {
        match self.tree.stats.header() {
            Ok(header) => header.entry_idx,
            Err(entry_idx) => entry_idx,
        }
    }
}

impl TreeInfo {
    const ITEM_SIZE: usize = size_of::<(*mut u8, u8)>();

    // Offset at which items start (header size rounded up to item alignment).
    const ITEMS_OFFSET: usize = {
        let hs = size_of::<TreeInfoHeader>();
        let ia = align_of::<(*mut u8, u8)>();
        let offset = (hs + ia - 1) & !(ia - 1);
        if offset != hs {
            panic!("TreeInfoHeader is not aligned");
        }
        offset
    };

    /// Reset the stack without freeing the buffer.
    #[inline]
    fn clear_cache(&mut self) {
        if self.0.get() & EMPTY_FLAG == 0 {
            let header = self.header_mut_unwrap();
            header.len = 0;
            header.buffer_pos = 0;
            header.entry_idx = 0;
        } else {
            *self = Self::default();
        }
    }

    #[inline]
    fn set_entry_idx(&mut self, entry_idx: u8) {
        if self.0.get() & EMPTY_FLAG == 0 {
            self.header_mut_unwrap().entry_idx = entry_idx;
        } else {
            self.0 = unsafe { NonZeroUsize::new_unchecked((entry_idx as usize) << 8 | EMPTY_FLAG) };
        }
    }

    /// height is the root.height (tree height - 1)
    #[inline]
    fn ensure_cap(&mut self, height: u8) {
        assert!(height < u8::MAX);
        match self.header() {
            Ok(header) => {
                if height <= header.cap {
                } else {
                    let old_cap = header.cap;
                    // grow one CACHE_LINE_SIZE each time
                    let old_size = Self::buf_size_from_cap(old_cap);
                    // because the tree only insert with PathBuffer, it should grow one height at a time
                    let new_size = old_size + CACHE_LINE_SIZE;
                    let new_cap = Self::cal_cap(new_size);
                    let old_layout = Self::get_layout(old_size);
                    unsafe {
                        let p = realloc(self.0.get() as *mut u8, old_layout, new_size);
                        if !p.is_null() {
                            crate::trace_log!("grow pathbuf cap {old_cap}->{new_cap}");
                            let header = p as *mut TreeInfoHeader;
                            (*header).cap = new_cap;
                            self.0 = NonZeroUsize::new_unchecked(p as usize);
                        } else {
                            handle_alloc_error(Self::get_layout(new_size));
                        }
                    }
                }
            }
            Err(entry_idx) => {
                if height > 0 {
                    // assume current height = 1 and previously root=leaf
                    self._alloc(2, 1, entry_idx);
                }
            }
        }
    }

    #[inline]
    fn leaf_count(&self) -> usize {
        if let Ok(header) = self.header() { header.leaf_count } else { 1 }
    }

    #[inline(always)]
    fn inter_count(&self) -> u32 {
        if let Ok(header) = self.header() { header.inter_count } else { 0 }
    }

    #[inline(always)]
    const fn cal_cap(buf_size: usize) -> u8 {
        ((buf_size - Self::ITEMS_OFFSET) / Self::ITEM_SIZE) as u8
    }

    #[inline(always)]
    const fn buf_size_from_cap(cap: u8) -> usize {
        let size = cap as usize * Self::ITEM_SIZE + Self::ITEMS_OFFSET;
        #[cfg(debug_assertions)]
        {
            if !size.is_multiple_of(CACHE_LINE_SIZE) {
                panic!("not aligned");
            }
        }
        size
    }

    #[inline(always)]
    const fn get_layout(buf_size: usize) -> Layout {
        let align = align_of::<usize>();
        #[cfg(debug_assertions)]
        {
            if align_of::<(*mut u8, u8)>() != align {
                panic!("TreeInfoHeader is not aligned");
            }
        }
        unsafe { Layout::from_size_align_unchecked(buf_size, align) }
    }

    #[inline]
    fn _alloc(&mut self, leaf_count: usize, inter_count: u32, entry_idx: u8) {
        debug_assert!(self.header().is_err());
        unsafe {
            let layout = Self::get_layout(CACHE_LINE_SIZE);
            let cap = Self::cal_cap(CACHE_LINE_SIZE);
            let p = alloc(layout);
            if !p.is_null() {
                crate::trace_log!("alloc pathbuf cap {cap}");
                let header = p as *mut TreeInfoHeader;
                header.write(TreeInfoHeader {
                    leaf_count,
                    inter_count,
                    entry_idx,
                    cap,
                    len: 0,
                    buffer_pos: 0,
                });
                self.0 = NonZeroUsize::new_unchecked(p as usize);
            } else {
                handle_alloc_error(layout);
            }
        }
    }

    #[inline]
    fn header(&self) -> Result<&TreeInfoHeader, u8> {
        if self.0.get() & EMPTY_FLAG == 0 {
            let p = self.0.get() as *mut TreeInfoHeader;
            Ok(unsafe { &*p })
        } else {
            Err((self.0.get() >> 8) as u8)
        }
    }

    #[inline]
    fn header_mut(&mut self) -> Result<&mut TreeInfoHeader, u8> {
        if self.0.get() & EMPTY_FLAG == 0 {
            let p = self.0.get() as *mut TreeInfoHeader;
            Ok(unsafe { &mut *p })
        } else {
            Err((self.0.get() >> 8) as u8)
        }
    }

    #[inline]
    fn header_mut_unwrap(&mut self) -> &mut TreeInfoHeader {
        debug_assert_eq!(self.0.get() & EMPTY_FLAG, 0);
        let p = self.0.get() as *mut TreeInfoHeader;
        unsafe { &mut *p }
    }

    #[inline]
    unsafe fn item_ptr(&self, idx: u8) -> *const (NodeBase, u8) {
        debug_assert_eq!(self.0.get() & EMPTY_FLAG, 0);
        unsafe {
            (self.0.get() as *const u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE)
                as *const _
        }
    }

    #[inline]
    unsafe fn item_ptr_mut(&self, idx: u8) -> *mut (NodeBase, u8) {
        debug_assert_eq!(self.0.get() & EMPTY_FLAG, 0);
        unsafe {
            (self.0.get() as *mut u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE)
                as *mut _
        }
    }
}

impl Drop for TreeInfo {
    #[inline]
    fn drop(&mut self) {
        if self.0.get() & EMPTY_FLAG == 0 {
            let p = self.0.get() as *mut TreeInfoHeader;
            unsafe {
                let size = Self::buf_size_from_cap((*p).cap);
                dealloc(p as *mut u8, Self::get_layout(size));
            }
        }
    }
}

impl PathBuffer for TreeInfo {
    // --- stats method begins ---

    #[inline(always)]
    fn inc_leaf_count(&mut self) {
        match self.header_mut() {
            Ok(header) => {
                header.leaf_count += 1;
                crate::trace_log!("inc_leaf_count {}", header.leaf_count);
            }
            Err(entry_idx) => {
                self._alloc(2, 1, entry_idx);
            }
        }
    }

    #[inline(always)]
    fn dec_leaf_count(&mut self) {
        self.header_mut_unwrap().leaf_count -= 1;
    }

    /// # Safety
    ///
    /// on (height=1) root creation, caller should not call this function (inter_count init within
    /// inc_leaf_count)
    #[inline(always)]
    fn inc_inter_count(&mut self) {
        match self.header_mut() {
            Ok(header) => {
                header.inter_count += 1;
                crate::trace_log!("inc inter_count {}", header.inter_count);
            }
            Err(_entry_idx) => {
                unreachable!();
            }
        }
    }

    #[inline(always)]
    fn dec_inter_count(&mut self) {
        self.header_mut_unwrap().inter_count -= 1;
        crate::trace_log!("dec inter_count {}", self.header_mut_unwrap().inter_count);
    }

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        if let Ok(header) = self.header() { header.len } else { 0 }
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    #[inline]
    fn buffer_pos(&self) -> i8 {
        if let Ok(header) = self.header() { header.buffer_pos } else { 0 }
    }

    #[inline]
    fn move_pos(&mut self, delta: i8) {
        // XXX should we keep the pos pack when heap is not alloced?
        if let Ok(header) = self.header_mut() {
            header.buffer_pos += delta;
        }
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    fn _push(&mut self, inter: NodeBase, idx: u8) {
        if let Ok(header) = self.header_mut() {
            let wi = header.len;
            header.len = wi + 1;
            debug_assert!(wi < header.cap, "{wi} {}", header.cap);
            unsafe { self.item_ptr_mut(wi).write((inter, idx)) };
        } else {
            unreachable!();
        }
    }

    #[inline]
    unsafe fn _get_unchecked(&self, idx: u8) -> (NodeBase, u8) {
        unsafe {
            let p = &*self.item_ptr(idx);
            (p.0.clone(), p.1)
        }
    }

    /// Pop the top entry from the cache stack.
    #[inline]
    fn _pop(&mut self) -> Option<(NodeBase, u8)> {
        if let Ok(header) = self.header_mut() {
            let mut wi = header.len;
            if wi > 0 {
                wi -= 1;
                header.len = wi;
                return unsafe { Some(self.item_ptr(wi).read()) };
            }
        }
        None
    }
}

impl<K: Key, V: Value> BTree<K, V, TreeInfo> {
    /// Return the number of leaf nodes
    #[inline(always)]
    pub fn leaf_count(&self) -> usize {
        if self.inner.root.is_some() { self.stats.leaf_count() } else { 0 }
    }

    /// Return the number of inter nodes
    #[inline(always)]
    pub fn inter_count(&self) -> usize {
        self.stats.inter_count() as usize
    }

    #[inline]
    pub fn memory_used(&self) -> usize {
        (self.leaf_count() + self.inter_count()) * NODE_SIZE
    }

    /// Return the average fill ratio of leaf nodes
    ///
    /// The range is [0.0, 100]
    #[inline]
    pub fn get_fill_ratio(&self) -> f32 {
        if self.inner.len == 0 {
            0.0
        } else {
            let cap = LeafNode::<K, V>::cap() as usize * self.leaf_count();
            self.inner.len as f32 / cap as f32 * 100.0
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::btree::tests::*;
    use captains_log::logfn;
    use rstest::*;

    #[logfn]
    #[rstest]
    fn test_tree_info_path_buffer(setup_log: ()) {
        let mut info = TreeInfo::default();
        assert!(info.header().is_err());
        info.ensure_cap(3);
        assert!(info.header().ok().unwrap().cap >= 3);
        info.ensure_cap(3);
    }
}
