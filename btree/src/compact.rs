use crate::CACHE_LINE_SIZE;
use crate::btree::{
    self, BTree, entry::EntryInner, helper::PathBuffer, inter::*, node::*, tree::BTreeInner, *,
};
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::borrow::BorrowMut;
use core::fmt::{self, Debug};
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, size_of, transmute};
use core::num::{NonZeroU8, NonZeroU64};
use core::ptr::null_mut;

pub type BTreeMap<K, V> = btree::BTree<K, V, Compact>;
pub use btree::cursor::Cursor;
pub use btree::iter::{Iter, IterMut, Keys, Range, RangeMut, Values, ValuesMut};
pub type IntoIter<K, V> = btree::iter::IntoIter<K, V, Compact>;
pub type Entry<'a, K, V> = btree::entry::Entry<'a, K, V, Compact>;
pub type OccupiedEntry<'a, K, V> = btree::entry::OccupiedEntry<'a, K, V, Compact>;
pub type VacantEntry<'a, K, V> = btree::entry::VacantEntry<'a, K, V, Compact>;

/// Compact metadata for `BTreeMap`.
///
/// It's either CompactBufHeader cast as u64, or ptr for meta on heap.
///
/// NOTE: use NonZeroU64 to optimize `Option<BTreeMap>`
pub struct Compact(NonZeroU64);

const STACK_CAP: usize = 3;
const ENTRY_CAP: usize = 1;

unsafe impl Send for Compact {}
unsafe impl Sync for Compact {}

impl Default for Compact {
    fn default() -> Self {
        Self(unsafe { NonZeroU64::new_unchecked(transmute(CompactBufHeader::default())) })
    }
}

impl Drop for Compact {
    #[inline]
    fn drop(&mut self) {
        let p = self.try_heap_ptr();
        if !p.is_null() {
            unsafe {
                let header = p as *mut CompactBufHeader;
                let size = Self::buf_size_from_cap((*header).cap.get());
                // InterNode does not have drop
                dealloc(p, Self::get_layout(size));
            }
        }
    }
}

// for log
impl Debug for Compact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Compact")
    }
}

impl Compact {
    const ITEM_SIZE: usize = size_of::<(*mut u8, u8)>();

    // Offset at which items start (header size rounded up to item alignment).
    const ITEMS_OFFSET: usize = {
        let hs = size_of::<CompactBufHeader>();
        let ia = align_of::<(*mut u8, u8)>();
        let offset = (hs + ia - 1) & !(ia - 1);
        if offset != hs {
            panic!("TreeInfoHeader is not aligned");
        }
        offset
    };

    #[inline(always)]
    fn try_heap_ptr(&self) -> *mut u8 {
        let this = self.0.get();
        // the cap field
        if this & (STACK_FLAG as u64) == 0 { this as *mut u8 } else { null_mut() }
    }

    #[inline(always)]
    fn header_ptr(&self) -> *const CompactBufHeader {
        let this = self.0.get();
        // the cap field
        if this & (STACK_FLAG as u64) > 0 {
            &self.0 as *const NonZeroU64 as *const CompactBufHeader
        } else {
            this as *const CompactBufHeader
        }
    }

    #[inline(always)]
    fn header_ptr_mut(&mut self) -> *mut CompactBufHeader {
        let this = self.0.get();
        // the cap field
        if this & (STACK_FLAG as u64) > 0 {
            &mut self.0 as *mut NonZeroU64 as *mut CompactBufHeader
        } else {
            this as *mut CompactBufHeader
        }
    }

    #[inline(always)]
    fn get_header(&self) -> &CompactBufHeader {
        unsafe { &*self.header_ptr() }
    }

    #[inline(always)]
    fn get_header_mut(&mut self) -> &mut CompactBufHeader {
        unsafe { &mut *self.header_ptr_mut() }
    }

    /// the input cap is not including root, but for actual items need to store on heap.
    ///
    /// return (new_buf_size, cap_field)
    ///
    /// cap_field = actual heap cap + 1 (root)
    #[inline(always)]
    const fn cal_new_buf_size(cap: u8) -> (usize, u8) {
        let need = cap as usize * Self::ITEM_SIZE + Self::ITEMS_OFFSET;
        // aligned multiple of CACHE_LINE_SIZE
        let new_size = (need + CACHE_LINE_SIZE - 1) & !(CACHE_LINE_SIZE - 1);
        let aligned_cap = ((new_size - Self::ITEMS_OFFSET) / Self::ITEM_SIZE) as u8;
        // one cap for root not stored on the heap
        (new_size, aligned_cap + 1)
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

    /// the input cap is not including root, but for actual items can store on heap.
    #[inline(always)]
    fn buf_size_from_cap(aligned_cap: u8) -> usize {
        // one cap for root not stored on the heap
        let size = (aligned_cap - 1) as usize * Self::ITEM_SIZE + Self::ITEMS_OFFSET;
        (size + CACHE_LINE_SIZE - 1) & !(CACHE_LINE_SIZE - 1)
    }

    /// height is the root.height (tree height - 1)
    #[inline]
    fn ensure_cap<const N: usize>(&mut self, root_height: u8) -> *mut CompactBufHeader {
        assert!(root_height < u8::MAX);
        let mut header = self.header_ptr_mut();
        // cap include root although it's not stored
        let cur_cap = unsafe { (*header).cap.get() };
        let new_size: usize;
        let new_cap: u8;
        let new_p;
        // STACK_FLAG == 1 can represent root, and on heap is 1 + real number
        if root_height < (N as u8) + cur_cap {
            return header;
        }
        let need_cap = root_height - 1 - N as u8;
        if cur_cap == STACK_FLAG {
            (new_size, new_cap) = Self::cal_new_buf_size(need_cap);
            crate::trace_log!("alloc pathbuf cap {need_cap} actual {new_cap} cap");
            let layout = Self::get_layout(new_size);
            new_p = unsafe { alloc(layout) };
            if !new_p.is_null() {
                header = new_p as *mut CompactBufHeader;
                unsafe {
                    (*header).entry_idx = 0;
                    (*header).len = 0;
                    (*header).buffer_pos = 0;
                    (*header).cap = NonZeroU8::new_unchecked(new_cap);
                }
            } else {
                handle_alloc_error(Self::get_layout(new_size));
            }
        } else {
            (new_size, new_cap) = Self::cal_new_buf_size(need_cap);
            crate::trace_log!("grow pathbuf cap {cur_cap}->{need_cap}");
            let old_layout = Self::get_layout(Self::buf_size_from_cap(cur_cap));
            new_p = unsafe { realloc(self.0.get() as *mut u8, old_layout, new_size) };
            if !new_p.is_null() {
                header = new_p as *mut CompactBufHeader;
                unsafe {
                    (*header).cap = NonZeroU8::new_unchecked(new_cap);
                }
            } else {
                handle_alloc_error(Self::get_layout(new_size));
            }
        }
        self.0 = unsafe { NonZeroU64::new_unchecked(new_p as u64) };
        unsafe { debug_assert!((*header).cap.get() != STACK_FLAG, "{}", (*header).cap) };
        header
    }
}

impl Stats for Compact {}

impl StatsPriv for Compact {
    type EntryInner<'a, K, V>
        = CompactEntry<'a, K, V>
    where
        K: Key + 'a,
        V: Value + 'a;

    type PathBufferRef<'a>
        = CompactBufRef<'a, STACK_CAP, &'a mut CompactBufStack<STACK_CAP>>
    where
        Self: 'a;

    type PathBuffer = CompactBufIntoIter<STACK_CAP>;

    type BufferStack = CompactBufStack<STACK_CAP>;

    #[inline]
    fn get_cache<'a, K>(
        &'a mut self, stack: &'a mut Self::BufferStack, root: Option<InterNode<K>>,
    ) -> Self::PathBufferRef<'a> {
        let _header = if let Some(root) = root.as_ref() {
            self.ensure_cap::<STACK_CAP>(root.height())
        } else {
            self.header_ptr_mut()
        };
        unsafe { (*_header).clear() };
        CompactBufRef { root: root.map(|n| n.into()), _header, stack, _phan: Default::default() }
    }

    #[inline]
    fn take_cache<K>(self, root: Option<InterNode<K>>) -> Self::PathBuffer {
        let heap_ptr: *mut CompactBufHeader;
        let mut header: CompactBufHeader;
        // take_cache will not increase height, it's always enough
        unsafe {
            let this = self.0.get();
            // the cap field
            if this & (STACK_FLAG as u64) > 0 {
                heap_ptr = null_mut();
                let _header: &CompactBufHeader = transmute(&self.0);
                header = _header.clone();
            } else {
                heap_ptr = this as *mut CompactBufHeader;
                header = (*heap_ptr).clone();
            }
        }
        header.clear();
        core::mem::forget(self);
        CompactBufIntoIter {
            root: root.map(|n| n.into()),
            // because it's moving, getting the address now is unsafe
            header,
            _heap: heap_ptr as *mut u8,
            stack: CompactBufStack::default(),
        }
    }

    #[inline]
    fn search_entry<'a, K: Key, V: Value>(
        tree: &'a mut BTree<K, V, Self>, key: K,
    ) -> Entry<'a, K, V> {
        let mut inner = CompactEntry { tree, stack: Default::default() };
        let (_tree, mut cache) = inner.init_cache();
        if let Some(root) = _tree.get_root() {
            let mut is_seq = true;
            let leaf = match root {
                Node::Inter(inter) => {
                    inter.find_leaf_with_cache_smart::<K, V, _>(&mut cache, &key, &mut is_seq)
                }
                Node::Leaf(leaf) => leaf,
            };
            let (idx, is_equal) = leaf.search_smart(&key, is_seq);
            // use cache' header ptr to accelerate
            cache.set_entry_idx(idx);
            if is_equal {
                Entry::Occupied(OccupiedEntry { inner, leaf })
            } else {
                Entry::Vacant(VacantEntry { inner, key, leaf: Some(leaf) })
            }
        } else {
            // Safety: entry_idx already reset 0 when init_cache
            Entry::Vacant(VacantEntry { inner, key, leaf: None })
        }
    }

    /// seek first or last entry
    #[inline]
    fn seek_entry<'a, K: Key, V: Value, const FIRST: bool>(
        tree: &'a mut BTree<K, V, Self>,
    ) -> Option<OccupiedEntry<'a, K, V>> {
        let mut inner = CompactEntry { tree, stack: Default::default() };
        let (_tree, mut cache) = inner.init_cache();
        if let Some(root) = _tree.get_root() {
            let leaf = match root {
                Node::Inter(inter) => {
                    if FIRST {
                        inter.find_first_leaf_with_cache::<V, _>(&mut cache)
                    } else {
                        inter.find_last_leaf_with_cache::<V, _>(&mut cache)
                    }
                }
                Node::Leaf(leaf) => leaf,
            };
            let count = leaf.key_count();
            if count > 0 {
                let idx = if FIRST { 0 } else { count - 1 };
                // use cache' header ptr to accelerate
                cache.set_entry_idx(idx);
                return Some(OccupiedEntry { inner, leaf });
            }
        }
        None
    }

    #[cfg(test)]
    fn init_count(&mut self, _leaf_count: usize, _inter_count: u32) {}

    #[cfg(test)]
    fn assert_leaf_count(&self, _leaf_count: usize) {}

    #[cfg(test)]
    fn assert_inter_count(&self, _inter_count: usize) {}
}

#[cfg(target_endian = "little")]
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct CompactBufHeader {
    /// when on stack, we mark cap == 1, the lowest bit on u64 (we convert CompactBufHeader as u64,
    /// we can determine it's not a pointer
    pub cap: NonZeroU8,
    /// left < 0, or right > 0, or center = 0
    pub buffer_pos: i8,
    /// the items stored in PathBuffer (not including the root)
    pub len: u8,
    /// tempoary storage for Entry.idx
    pub entry_idx: u8,
    pub idxs: MaybeUninit<[u8; STACK_CAP + 1]>,
}

#[cfg(target_endian = "big")]
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct CompactBufHeader {
    pub idxs: MaybeUninit<[u8; STACK_CAP + 1]>,
    /// tempoary storage for Entry.idx
    pub entry_idx: u8,
    /// the items stored in PathBuffer (not including the root)
    pub len: u8,
    /// left < 0, or right > 0, or center = 0
    pub buffer_pos: i8,
    /// when on stack, we mark cap == 1, the lowest bit on u64 (we convert CompactBufHeader as u64,
    /// we can determine it's not a pointer
    pub cap: NonZeroU8,
}

const STACK_FLAG: u8 = 1;

impl Default for CompactBufHeader {
    #[inline]
    fn default() -> Self {
        Self {
            buffer_pos: 0,
            len: 0,
            entry_idx: 0,
            cap: unsafe { NonZeroU8::new_unchecked(STACK_FLAG) },
            idxs: MaybeUninit::zeroed(),
        }
    }
}

impl CompactBufHeader {
    #[inline(always)]
    fn get_idxs(&self, i: u8) -> u8 {
        unsafe { self.idxs.assume_init_ref()[i as usize] }
    }

    fn put_idxs(&mut self, i: u8, value: u8) {
        unsafe { self.idxs.assume_init_mut()[i as usize] = value };
    }

    /// Reset the stack without freeing the buffer.
    #[inline]
    fn clear(&mut self) {
        self.len = 0;
        self.buffer_pos = 0;
        self.entry_idx = 0;
    }
}

pub(crate) struct CompactBufStack<const N: usize>(MaybeUninit<[NodeBase; N]>);

impl<const N: usize> Default for CompactBufStack<N> {
    #[inline]
    fn default() -> Self {
        Self(MaybeUninit::uninit())
    }
}

impl<const N: usize> CompactBufStack<N> {
    #[inline(always)]
    fn _get(&self, i: u8) -> NodeBase {
        debug_assert!((i as usize) < N);
        unsafe { self.0.assume_init_ref()[i as usize].clone() }
    }

    #[inline(always)]
    fn _put(&mut self, i: u8, inter: NodeBase) {
        debug_assert!((i as usize) < N);
        unsafe { self.0.assume_init_mut()[i as usize] = inter };
    }
}

trait CompactBufCommon {
    const STACK_N: usize;

    fn header(&self) -> &CompactBufHeader;

    fn header_mut(&mut self) -> &mut CompactBufHeader;

    #[inline(always)]
    fn set_entry_idx(&mut self, entry_idx: u8) {
        self.header_mut().entry_idx = entry_idx;
    }

    unsafe fn heap_item_ptr(&self, idx: u8) -> *mut (NodeBase, u8);

    fn stack_get(&self, i: u8) -> NodeBase;

    fn stack_put(&mut self, i: u8, inter: NodeBase);

    fn get_root(&self) -> NodeBase;
}

pub(crate) struct CompactBufRef<'a, const N: usize, S: BorrowMut<CompactBufStack<N>>> {
    root: Option<NodeBase>,
    // for fast access
    _header: *mut CompactBufHeader,
    stack: S,
    _phan: PhantomData<&'a ()>,
}

impl<'a, const N: usize, S: BorrowMut<CompactBufStack<N>>> CompactBufCommon
    for CompactBufRef<'a, N, S>
{
    const STACK_N: usize = N;

    #[inline(always)]
    fn header(&self) -> &CompactBufHeader {
        unsafe { &*self._header }
    }

    #[inline(always)]
    fn header_mut(&mut self) -> &mut CompactBufHeader {
        unsafe { &mut *self._header }
    }

    #[inline(always)]
    unsafe fn heap_item_ptr(&self, i: u8) -> *mut (NodeBase, u8) {
        let ptr = self._header;
        #[cfg(debug_assertions)]
        {
            let cap = unsafe { (*ptr).cap.get() };
            debug_assert!(cap > STACK_FLAG, "cap {cap}");
            debug_assert!(i < cap, "i {i} >= cap {cap}");
        }
        unsafe {
            let p = (ptr as *mut u8).add(Compact::ITEMS_OFFSET) as *mut (NodeBase, u8);
            p.add(i as usize)
        }
    }

    #[inline(always)]
    fn stack_get(&self, i: u8) -> NodeBase {
        self.stack.borrow()._get(i)
    }

    #[inline(always)]
    fn stack_put(&mut self, i: u8, inter: NodeBase) {
        self.stack.borrow_mut()._put(i, inter);
    }

    #[inline(always)]
    fn get_root(&self) -> NodeBase {
        self.root.as_ref().unwrap().clone()
    }
}

unsafe impl<'a, const N: usize, S: BorrowMut<CompactBufStack<N>>> Send for CompactBufRef<'a, N, S> {}

/// Once we are calling into iter the cap will not increase.
///
/// Because CompactBufIntoIter can be moving, we extract header here,
pub(crate) struct CompactBufIntoIter<const N: usize> {
    root: Option<NodeBase>,
    header: CompactBufHeader,
    // just for dropping when we are done
    _heap: *mut u8,
    stack: CompactBufStack<N>,
}

unsafe impl<const N: usize> Send for CompactBufIntoIter<N> {}

impl<const N: usize> CompactBufCommon for CompactBufIntoIter<N> {
    const STACK_N: usize = N;

    #[inline(always)]
    fn header(&self) -> &CompactBufHeader {
        &self.header
    }

    #[inline(always)]
    fn header_mut(&mut self) -> &mut CompactBufHeader {
        &mut self.header
    }

    #[inline(always)]
    unsafe fn heap_item_ptr(&self, i: u8) -> *mut (NodeBase, u8) {
        let ptr = self._heap;
        #[cfg(debug_assertions)]
        {
            debug_assert!(!ptr.is_null());
            let cap = self.header.cap.get();
            debug_assert!(cap > STACK_FLAG, "cap {cap}");
            debug_assert!(i < cap, "i {i} >= cap {cap}");
        }
        unsafe {
            let p = (ptr as *mut u8).add(Compact::ITEMS_OFFSET) as *mut (NodeBase, u8);
            p.add(i as usize)
        }
    }

    #[inline(always)]
    fn stack_get(&self, i: u8) -> NodeBase {
        self.stack._get(i)
    }

    #[inline(always)]
    fn stack_put(&mut self, i: u8, inter: NodeBase) {
        self.stack._put(i, inter);
    }

    #[inline(always)]
    fn get_root(&self) -> NodeBase {
        self.root.as_ref().unwrap().clone()
    }
}

impl<const N: usize> Drop for CompactBufIntoIter<N> {
    #[inline]
    fn drop(&mut self) {
        if !self._heap.is_null() {
            unsafe {
                let size = Compact::buf_size_from_cap(self.header.cap.get());
                // InterNode does not have drop
                dealloc(self._heap, Compact::get_layout(size));
            }
        }
    }
}

impl<T: CompactBufCommon> PathBuffer for T {
    // --- stats method begins ---

    #[inline(always)]
    fn inc_leaf_count(&mut self) {}

    #[inline(always)]
    fn dec_leaf_count(&mut self) {}
    #[inline(always)]
    fn inc_inter_count(&mut self) {}

    #[inline(always)]
    fn dec_inter_count(&mut self) {}

    // --- stats method ends ---

    /// The count of current level items contains by the PathBuffer
    #[inline]
    fn buffer_len(&self) -> u8 {
        self.header().len
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    #[inline]
    fn buffer_pos(&self) -> i8 {
        self.header().buffer_pos
    }

    #[inline]
    fn _set_pos(&mut self, buffer_pos: i8) {
        self.header_mut().buffer_pos = buffer_pos;
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    fn _push(&mut self, inter: NodeBase, idx: u8) {
        let header = self.header_mut();
        let i = header.len;
        header.len = i + 1;
        if i < Self::STACK_N as u8 + 1 {
            debug_assert!((i as usize) < Self::STACK_N + 1, "{i} < N {} + 1", Self::STACK_N);
            header.put_idxs(i, idx);
            if i > 0 {
                self.stack_put(i - 1, inter);
            }
        } else {
            unsafe { self.heap_item_ptr(i - Self::STACK_N as u8 - 1).write((inter, idx)) };
        }
    }

    #[inline]
    unsafe fn _get_unchecked(&self, i: u8) -> (NodeBase, u8) {
        let header = self.header();
        if i < Self::STACK_N as u8 + 1 {
            let idx = header.get_idxs(i);
            if i == 0 { (self.get_root(), idx) } else { (self.stack_get(i - 1), idx) }
        } else {
            let p = unsafe { &*self.heap_item_ptr(i - 1 - Self::STACK_N as u8) };
            (p.0.clone(), p.1)
        }
    }

    /// Pop the top entry from the cache stack.
    #[inline]
    fn _pop(&mut self) -> Option<(NodeBase, u8)> {
        let header = self.header_mut();
        let mut i = header.len;
        if i > 0 {
            i -= 1;
            header.len = i;
            if i < Self::STACK_N as u8 + 1 {
                let idx = header.get_idxs(i);
                if i == 0 {
                    Some((self.get_root(), idx))
                } else {
                    let node = self.stack_get(i - 1);
                    Some((node, idx))
                }
            } else {
                let p = unsafe { &*self.heap_item_ptr(i - 1 - Self::STACK_N as u8) };
                Some((p.0.clone(), p.1))
            }
        } else {
            None
        }
    }

    /// Peek the top entry from the cache stack.
    #[inline]
    fn _last(&self) -> Option<(NodeBase, u8)> {
        let header = self.header();
        let mut i = header.len;
        if i > 0 {
            i -= 1;
            if i < Self::STACK_N as u8 + 1 {
                let idx = header.get_idxs(i);
                if i == 0 {
                    Some((self.get_root(), idx))
                } else {
                    let node = self.stack_get(i - 1);
                    Some((node, idx))
                }
            } else {
                let p = unsafe { &*self.heap_item_ptr(i - 1 - Self::STACK_N as u8) };
                Some((p.0.clone(), p.1))
            }
        } else {
            None
        }
    }
}

type CompactBufEntry<'a> = CompactBufRef<'a, ENTRY_CAP, &'a mut CompactBufStack<ENTRY_CAP>>;

pub(crate) struct CompactEntry<'a, K: Key, V: Value> {
    tree: &'a mut BTree<K, V, Compact>,
    stack: CompactBufStack<ENTRY_CAP>,
}

impl<'a, K: Key, V: Value> CompactEntry<'a, K, V> {
    #[inline]
    fn init_cache(&mut self) -> (&BTreeInner<K, V>, CompactBufEntry<'_>) {
        let (tree, stats, stack) = (&self.tree.inner, &mut self.tree.stats, &mut self.stack);
        let _header;
        let root = if let Some(inter) = tree.root_as_inter() {
            _header = stats.ensure_cap::<ENTRY_CAP>(inter.height());
            Some(inter)
        } else {
            _header = stats.header_ptr_mut();
            None
        };
        unsafe { (*_header).clear() };
        (
            tree,
            CompactBufEntry {
                _header,
                root: root.map(|n| n.into()),
                stack,
                _phan: Default::default(),
            },
        )
    }
}

impl<'a, K: Key, V: Value> EntryInner<K, V> for CompactEntry<'a, K, V> {
    #[inline(always)]
    fn get_cache(&mut self) -> impl PathBuffer {
        let root = self.tree.inner.root_as_inter().map(|_node| _node.into());
        let _header = self.tree.stats.header_ptr_mut();
        CompactBufEntry { root, _header, stack: &mut self.stack, _phan: Default::default() }
    }

    #[cfg(test)]
    #[inline(always)]
    fn get_tree(&self) -> &BTreeInner<K, V> {
        &self.tree.inner
    }

    #[inline(always)]
    fn get_tree_cache(&mut self) -> (&mut BTreeInner<K, V>, impl PathBuffer) {
        let (tree, stats) = (&mut self.tree.inner, &mut self.tree.stats);
        let root = tree.root_as_inter();
        (
            tree,
            CompactBufRef {
                root: root.map(|n| n.into()),
                _header: stats.header_ptr_mut(),
                stack: &mut self.stack,
                _phan: Default::default(),
            },
        )
    }

    #[inline(always)]
    fn set_idx(&mut self, idx: u8) {
        self.tree.stats.get_header_mut().entry_idx = idx;
    }

    #[inline(always)]
    fn get_idx(&self) -> u8 {
        self.tree.stats.get_header().entry_idx
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;
    use std::println;

    #[test]
    fn test_compact_buf_size() {
        type StackBuf<'a> = CompactBufRef<'a, STACK_CAP, &'a mut CompactBufStack<STACK_CAP>>;
        type OwnedBuf<'a> = CompactBufIntoIter<STACK_CAP>;
        println!("stack buf size: {}", size_of::<StackBuf>());
        println!("owned buf size: {}", size_of::<OwnedBuf>());
        //        println!("CompactBufferStack {}", size_of::<CompactBufferStack>());
        println!("CompactEntry {}", size_of::<CompactEntry::<u32, u32>>());
    }
}
