use crate::CACHE_LINE_SIZE;
use crate::btree::{
    self, BTree, entry::*, helper::PathBuffer, inter::*, leaf::*, node::*, tree::BTreeInner, *,
};
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::fmt::{self, Debug};
use core::mem::{align_of, size_of};
use core::ptr::null_mut;

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
    _padding: u8,
    /// len=1 means root is pushed (as root idx),
    /// len-1 is the items stored in the heap.
    len: u8,
    /// left / right
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
pub struct TreeInfo {
    // because PathBuffer should support mut during query tree, we need inner muttabilty
    ptr: *mut TreeInfoHeader,
}

unsafe impl Send for TreeInfo {}
unsafe impl Sync for TreeInfo {}

impl Default for TreeInfo {
    fn default() -> Self {
        Self { ptr: null_mut() }
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
        if let Some(header) = self.header_mut() {
            header.leaf_count = leaf_count;
            header.inter_count = inter_count;
        } else {
            self._alloc(leaf_count, inter_count);
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
            let inner = TreeInfoEntry { tree, entry_idx: idx };
            if is_equal {
                Entry::Occupied(OccupiedEntry { inner, leaf })
            } else {
                Entry::Vacant(VacantEntry { inner, key, leaf: Some(leaf) })
            }
        } else {
            Entry::Vacant(VacantEntry {
                inner: TreeInfoEntry { tree, entry_idx: 0 },
                key,
                leaf: None,
            })
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
                let inner = if FIRST {
                    TreeInfoEntry { tree, entry_idx: 0 }
                } else {
                    TreeInfoEntry { tree, entry_idx: count - 1 }
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
    entry_idx: u8,
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
        self.entry_idx = idx;
    }

    #[inline(always)]
    fn get_idx(&self) -> u8 {
        self.entry_idx
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
        if let Some(header) = self.header_mut() {
            header.len = 0;
            header.buffer_pos = 0;
        }
    }

    /// height is the root.height (tree height - 1)
    #[inline]
    fn ensure_cap(&mut self, height: u8) {
        assert!(height < u8::MAX);
        if height == 0 {
            return;
        }
        let header = self.ptr;
        if !header.is_null() {
            unsafe {
                if height <= (*header).cap {
                    return;
                } else {
                    let old_cap = (*header).cap;
                    // grow one CACHE_LINE_SIZE each time
                    let old_size = Self::buf_size_from_cap(old_cap);
                    // because the tree only insert with PathBuffer, it should grow one height at a time
                    let new_size = old_size + CACHE_LINE_SIZE;
                    let new_cap = Self::cal_cap(new_size);
                    let old_layout = Self::get_layout(old_size);
                    let p = realloc(header as *mut u8, old_layout, new_size);
                    if !p.is_null() {
                        crate::trace_log!("grow pathbuf cap {old_cap}->{new_cap}");
                        let header = p as *mut TreeInfoHeader;
                        (*header).cap = new_cap;
                        self.ptr = header;
                    } else {
                        handle_alloc_error(Self::get_layout(new_size));
                    }
                }
            }
        } else {
            // assume current height = 1 and previously root=leaf
            self._alloc(2, 1);
        }
    }

    #[inline]
    fn leaf_count(&self) -> usize {
        if let Some(header) = self.header() { header.leaf_count } else { 1 }
    }

    #[inline(always)]
    fn inter_count(&self) -> u32 {
        if let Some(header) = self.header() { header.inter_count } else { 0 }
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
            if size % CACHE_LINE_SIZE != 0 {
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
    fn _alloc(&mut self, leaf_count: usize, inter_count: u32) {
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
                    _padding: 0,
                    cap,
                    len: 0,
                    buffer_pos: 0,
                });
                debug_assert!(self.ptr.is_null());
                self.ptr = header;
            } else {
                handle_alloc_error(layout);
            }
        }
    }

    #[inline]
    fn header(&self) -> Option<&TreeInfoHeader> {
        let p = self.ptr;
        if !p.is_null() { Some(unsafe { &*p }) } else { None }
    }

    #[inline]
    fn header_mut(&mut self) -> Option<&mut TreeInfoHeader> {
        let p = self.ptr;
        if !p.is_null() { Some(unsafe { &mut *p }) } else { None }
    }

    #[inline]
    fn header_mut_unwrap(&self) -> &mut TreeInfoHeader {
        let p = self.ptr;
        debug_assert!(!p.is_null());
        unsafe { &mut *p }
    }

    #[inline]
    unsafe fn item_ptr(&self, idx: u8) -> *const (NodeBase, u8) {
        let p = self.ptr;
        unsafe {
            (p as *const u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE) as *const _
        }
    }

    #[inline]
    unsafe fn item_ptr_mut(&self, idx: u8) -> *mut (NodeBase, u8) {
        let p = self.ptr;
        unsafe { (p as *mut u8).add(Self::ITEMS_OFFSET + idx as usize * Self::ITEM_SIZE) as *mut _ }
    }
}

impl Drop for TreeInfo {
    #[inline]
    fn drop(&mut self) {
        let p = self.ptr;
        if !p.is_null() {
            unsafe {
                let size = Self::buf_size_from_cap((*p).cap);
                // InterNode does not have drop
                dealloc(p as *mut u8, Self::get_layout(size));
            }
        }
    }
}

impl PathBuffer for TreeInfo {
    // --- stats method begins ---

    #[inline(always)]
    fn inc_leaf_count(&mut self) {
        if let Some(header) = self.header_mut() {
            header.leaf_count += 1;
        } else {
            self._alloc(2, 1);
        }
    }

    #[inline(always)]
    fn dec_leaf_count(&mut self) {
        self.header_mut_unwrap().leaf_count -= 1;
    }
    #[inline(always)]
    fn inc_inter_count(&mut self) {
        if let Some(header) = self.header_mut() {
            header.inter_count += 1;
        } else {
            self._alloc(2, 1);
        }
    }

    #[inline(always)]
    fn dec_inter_count(&mut self) {
        self.header_mut_unwrap().inter_count -= 1;
    }

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        if let Some(header) = self.header() { header.len } else { 0 }
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    #[inline]
    fn buffer_pos(&self) -> i8 {
        if let Some(header) = self.header() { header.buffer_pos } else { 0 }
    }

    #[inline]
    fn move_pos(&mut self, delta: i8) {
        if let Some(header) = self.header_mut() {
            header.buffer_pos += delta;
        }
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    fn _push(&mut self, inter: NodeBase, idx: u8) {
        if let Some(header) = self.header_mut() {
            let wi = header.len;
            header.len = wi + 1;
            debug_assert!(wi < header.cap, "{wi} {}", header.cap);
            unsafe { self.item_ptr_mut(wi).write((inter, idx)) };
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
        let header = self.header_mut()?;
        let mut wi = header.len;
        if wi > 0 {
            wi -= 1;
            header.len = wi;
            unsafe { Some(self.item_ptr(wi).read()) }
        } else {
            None
        }
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
