use crate::CACHE_LINE_SIZE;
use crate::btree::{
    self, BTree, entry::*, helper::PathBuffer, inter::*, leaf::*, node::*, tree::BTreeInner, *,
};
use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use core::borrow::BorrowMut;
use core::cell::UnsafeCell;
use core::fmt::{self, Debug};
use core::mem::{MaybeUninit, align_of, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::null_mut;

pub type BTreeMap<K, V> = btree::BTree<K, V, Compact<K>>;
pub use btree::cursor::Cursor;
pub use btree::iter::{Iter, IterMut, Keys, Range, RangeMut, Values, ValuesMut};
pub type IntoIter<K, V> = btree::iter::IntoIter<K, V, Compact<K>>;
pub type Entry<'a, K, V> = btree::entry::Entry<'a, K, V, Compact<K>>;
pub type OccupiedEntry<'a, K, V> = btree::entry::OccupiedEntry<'a, K, V, Compact<K>>;
pub type VacantEntry<'a, K, V> = btree::entry::VacantEntry<'a, K, V, Compact<K>>;

pub struct Compact<K> {
    // 8B
    header: UnsafeCell<CompactBufHeader>,
    ptr: *mut (InterNode<K>, u8),
}

const STACK_CAP: usize = 3;
const ENTRY_CAP: usize = 1;

unsafe impl<K> Send for Compact<K> {}

impl<K> Default for Compact<K> {
    fn default() -> Self {
        Self {
            header: UnsafeCell::new(CompactBufHeader {
                buffer_pos: 0,
                len: 0,
                entry_idx: 0,
                cap: 0,
                idxs: MaybeUninit::zeroed(),
            }),
            ptr: null_mut(),
        }
    }
}

impl<K> Drop for Compact<K> {
    fn drop(&mut self) {
        let p = self.ptr;
        if !p.is_null() {
            unsafe {
                let size = Self::buf_size_from_cap(self.get_header().cap);
                // InterNode does not have drop
                dealloc(p as *mut u8, Self::get_layout(size));
            }
        }
    }
}

// for log
impl<K> Debug for Compact<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Compact")
    }
}

impl<K> Compact<K> {
    const ITEM_SIZE: usize = size_of::<(InterNode<K>, u8)>();

    #[inline(always)]
    fn get_header(&self) -> &CompactBufHeader {
        unsafe { &*self.header.get() }
    }

    #[inline(always)]
    fn get_header_mut(&mut self) -> &mut CompactBufHeader {
        unsafe { &mut *self.header.get() }
    }

    #[inline(always)]
    const fn cal_new_buf_size(cap: u8) -> (usize, u8) {
        let need = cap as usize * Self::ITEM_SIZE;
        let new_size = (need + CACHE_LINE_SIZE - 1) & !(CACHE_LINE_SIZE - 1);
        (new_size, (new_size / Self::ITEM_SIZE) as u8)
    }

    #[inline(always)]
    const fn get_layout(buf_size: usize) -> Layout {
        let align = align_of::<usize>();
        #[cfg(debug_assertions)]
        {
            if align_of::<(InterNode<K>, u8)>() != align {
                panic!("TreeInfoHeader is not aligned");
            }
        }
        unsafe { Layout::from_size_align_unchecked(buf_size, align) }
    }

    #[inline(always)]
    fn buf_size_from_cap(cap: u8) -> usize {
        // one cap for root not stored on the heap
        let size = (cap - 1) as usize * Self::ITEM_SIZE;
        debug_assert_eq!(size % CACHE_LINE_SIZE, 0, "size {size} cap {cap}");
        size
    }

    /// height is the root.height (tree height - 1)
    #[inline]
    fn ensure_cap<const N: usize>(&mut self, root_height: u8) {
        assert!(root_height < u8::MAX);
        // cap include root although it's not stored
        let need_cap = root_height - 1;
        let cur_cap = self.get_header().cap;
        if (cur_cap == 0 && need_cap as usize <= N) || need_cap <= cur_cap {
            return;
        }
        let (new_size, new_cap) = Self::cal_new_buf_size(need_cap);
        let p = self.ptr;
        let new_p = if p.is_null() {
            crate::trace_log!("alloc pathbuf cap {need_cap}");
            let layout = Self::get_layout(new_size);
            unsafe { alloc(layout) }
        } else {
            crate::trace_log!("grow pathbuf cap {cur_cap}->{need_cap}");
            let old_layout = Self::get_layout(Self::buf_size_from_cap(cur_cap));
            unsafe { realloc(p as *mut u8, old_layout, new_size) }
        };
        if !new_p.is_null() {
            self.get_header_mut().cap = new_cap + 1;
            self.ptr = new_p as *mut (InterNode<K>, u8);
        } else {
            handle_alloc_error(Self::get_layout(new_size));
        }
    }

    #[inline]
    unsafe fn _item_ptr(&self, idx: u8) -> *mut (InterNode<K>, u8) {
        let cap = self.get_header().cap;
        debug_assert!(cap > 0);
        debug_assert!(idx < cap, "idx {idx} >= cap {cap}");
        let p = self.ptr;
        unsafe { p.add(idx as usize) }
    }
}

impl<K: Key> Stats<K> for Compact<K> {
    type EntryInner<'a, V>
        = CompactEntry<'a, K, V>
    where
        V: Value + 'a;

    type PathBufferRef<'a>
        = CompactBuf<K, STACK_CAP, &'a mut Compact<K>, &'a mut CompactBufStack<K, STACK_CAP>>
    where
        Self: 'a;

    type PathBuffer = CompactBuf<K, STACK_CAP, Self, CompactBufStack<K, STACK_CAP>>;

    type BufferStack = CompactBufStack<K, STACK_CAP>;

    #[inline]
    fn get_cache<'a>(
        &'a mut self, stack: &'a mut Self::BufferStack, root: Option<InterNode<K>>,
    ) -> Self::PathBufferRef<'a> {
        self.clear_cache();
        if let Some(root) = root.as_ref() {
            self.ensure_cap::<STACK_CAP>(root.height());
        }
        CompactBuf { root, stats: self, stack }
    }

    #[inline]
    fn take_cache(mut self, root: Option<InterNode<K>>) -> Self::PathBuffer {
        self.clear_cache();
        if let Some(root) = root.as_ref() {
            self.ensure_cap::<STACK_CAP>(root.height());
        }
        CompactBuf { root, stats: self, stack: CompactBufStack::default() }
    }

    /// Reset the stack without freeing the buffer.
    #[inline]
    fn clear_cache(&mut self) {
        let header = self.get_header_mut();
        header.len = 0;
        header.buffer_pos = 0;
    }

    #[inline]
    fn search_entry<'a, V: Value>(tree: &'a mut BTree<K, V, Self>, key: K) -> Entry<'a, K, V> {
        let mut inner = CompactEntry { tree, stack: Default::default() };
        let idx;
        let mut is_equal = false;
        let o_leaf: Option<LeafNode<K, V>>;
        {
            let (_tree, mut cache) = inner.init_cache();
            if let Some(root) = _tree.get_root() {
                let mut is_seq = true;
                let leaf = match root {
                    Node::Inter(inter) => {
                        inter.find_leaf_with_cache_smart::<K, V, _>(&mut cache, &key, &mut is_seq)
                    }
                    Node::Leaf(leaf) => leaf,
                };
                (idx, is_equal) = leaf.search_smart(&key, is_seq);
                o_leaf = Some(leaf);
            } else {
                idx = 0;
                o_leaf = None;
            }
        }
        inner.set_idx(idx);
        if let Some(leaf) = o_leaf {
            if is_equal {
                Entry::Occupied(OccupiedEntry { inner, leaf })
            } else {
                Entry::Vacant(VacantEntry { inner, key, leaf: Some(leaf) })
            }
        } else {
            Entry::Vacant(VacantEntry { inner, key, leaf: None })
        }
    }

    /// seek first or last entry
    #[inline]
    fn seek_entry<'a, V: Value, const FIRST: bool>(
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
                if FIRST {
                    inner.set_idx(0);
                } else {
                    inner.set_idx(count - 1);
                }
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

#[repr(C)]
pub(crate) struct CompactBufHeader {
    buffer_pos: i8,
    len: u8,
    entry_idx: u8,
    // if cap > 4, on the heap, otherwise on the stack
    cap: u8,
    /// cap: max cap of items can be hold currently, when > 2 put in the heap
    idxs: MaybeUninit<[u8; STACK_CAP + 1]>,
}

impl CompactBufHeader {
    #[inline(always)]
    fn get_idxs(&self, i: u8) -> u8 {
        unsafe { self.idxs.assume_init_ref()[i as usize] }
    }

    fn put_idxs(&mut self, i: u8, value: u8) {
        unsafe { self.idxs.assume_init_mut()[i as usize] = value };
    }
}

pub(crate) struct CompactBufStack<K, const N: usize>(MaybeUninit<[InterNode<K>; N]>);

impl<K, const N: usize> Default for CompactBufStack<K, N> {
    #[inline]
    fn default() -> Self {
        Self(MaybeUninit::zeroed())
    }
}

impl<K, const N: usize> CompactBufStack<K, N> {
    #[inline(always)]
    fn _get(&self, i: u8) -> InterNode<K> {
        debug_assert!((i as usize) < N);
        unsafe { self.0.assume_init_ref()[i as usize].clone() }
    }

    #[inline(always)]
    fn _put(&mut self, i: u8, inter: InterNode<K>) {
        debug_assert!((i as usize) < N);
        unsafe { self.0.assume_init_mut()[i as usize] = inter };
    }
}

pub(crate) struct CompactBuf<K, const N: usize, T, S: BorrowMut<CompactBufStack<K, N>>> {
    root: Option<InterNode<K>>,
    stats: T,
    stack: S,
}

impl<K: Ord, const N: usize, T: BorrowMut<Compact<K>>, S: BorrowMut<CompactBufStack<K, N>>> Deref
    for CompactBuf<K, N, T, S>
{
    type Target = Compact<K>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.stats.borrow()
    }
}

impl<K: Ord, const N: usize, T: BorrowMut<Compact<K>>, S: BorrowMut<CompactBufStack<K, N>>> DerefMut
    for CompactBuf<K, N, T, S>
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Compact<K> {
        self.stats.borrow_mut()
    }
}

impl<K: Ord, const N: usize, T: BorrowMut<Compact<K>>, S: BorrowMut<CompactBufStack<K, N>>>
    PathBuffer<K> for CompactBuf<K, N, T, S>
{
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

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        self.get_header().len
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    #[inline]
    fn buffer_pos(&self) -> i8 {
        self.get_header().buffer_pos
    }

    #[inline]
    fn move_pos(&mut self, delta: i8) {
        self.get_header_mut().buffer_pos += delta;
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    #[inline]
    fn _push(&mut self, inter: InterNode<K>, idx: u8) {
        let header = self.get_header_mut();
        let cap = header.cap;
        let i = header.len;
        header.len = i + 1;
        if i > 0 {
            if cap == 0 {
                debug_assert!((i as usize) < N + 1, "{i} < N {N} + 1");
                header.put_idxs(i, idx);
                self.stack.borrow_mut()._put(i - 1, inter);
            } else {
                unsafe { self._item_ptr(i - 1).write((inter, idx)) };
            }
        } else {
            header.put_idxs(0, idx);
        }
    }

    #[inline]
    unsafe fn _get_unchecked(&self, i: u8) -> (InterNode<K>, u8) {
        let header = self.get_header();
        let cap = header.cap;
        if i > 0 {
            let idx;
            let node;
            if cap == 0 {
                debug_assert!((i as usize) < N + 1);
                idx = header.get_idxs(i);
                node = self.stack.borrow()._get(i - 1);
            } else {
                let p = unsafe { &*self._item_ptr(i - 1) };
                idx = p.1;
                node = p.0.clone();
            }
            (node, idx)
        } else {
            let idx = header.get_idxs(0);
            (self.root.as_ref().unwrap().clone(), idx)
        }
    }

    /// Pop the top entry from the cache stack.
    #[inline]
    fn _pop(&mut self) -> Option<(InterNode<K>, u8)> {
        let header = self.get_header_mut();
        let cap = header.cap;
        let mut i = header.len;
        if i > 0 {
            i -= 1;
            header.len = i;
            if i > 0 {
                let idx;
                let node;
                if cap == 0 {
                    debug_assert!((i as usize) < N + 1);
                    idx = header.get_idxs(i);
                    node = self.stack.borrow_mut()._get(i - 1);
                } else {
                    let p = unsafe { &*self._item_ptr(i - 1) };
                    idx = p.1;
                    node = p.0.clone();
                }
                Some((node, idx))
            } else {
                let idx = header.get_idxs(0);
                Some((self.root.as_ref().unwrap().clone(), idx))
            }
        } else {
            None
        }
    }
}

type CompactBufEntry<'a, K> =
    CompactBuf<K, ENTRY_CAP, &'a mut Compact<K>, &'a mut CompactBufStack<K, ENTRY_CAP>>;

pub(crate) struct CompactEntry<'a, K: Key, V: Value> {
    tree: &'a mut BTree<K, V, Compact<K>>,
    stack: CompactBufStack<K, ENTRY_CAP>,
}

impl<'a, K: Key, V: Value> CompactEntry<'a, K, V> {
    fn init_cache(&mut self) -> (&BTreeInner<K, V>, CompactBufEntry<'_, K>) {
        self.tree.stats.clear_cache();
        let root = if let Some(inter) = self.tree.inner.root_as_inter() {
            self.tree.stats.ensure_cap::<ENTRY_CAP>(inter.height());
            Some(inter)
        } else {
            None
        };
        let (tree, stats, stack) = (&self.tree.inner, &mut self.tree.stats, &mut self.stack);
        (tree, CompactBufEntry { root, stats, stack })
    }
}

impl<'a, K: Key, V: Value> EntryInner<K, V> for CompactEntry<'a, K, V> {
    #[inline(always)]
    fn get_cache<'b>(&'b mut self) -> impl PathBuffer<K> {
        let root = self.tree.inner.root_as_inter();
        CompactBufEntry { root, stats: &mut self.tree.stats, stack: &mut self.stack }
    }

    #[cfg(test)]
    #[inline(always)]
    fn get_tree(&self) -> &BTreeInner<K, V> {
        &self.tree.inner
    }

    #[inline(always)]
    fn get_tree_cache(&mut self) -> (&mut BTreeInner<K, V>, impl PathBuffer<K>) {
        let (tree, stats) = (&mut self.tree.inner, &mut self.tree.stats);
        let root = tree.root_as_inter();
        (tree, CompactBuf { root, stats, stack: &mut self.stack })
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
        type StackBuf<'a, K> =
            CompactBuf<K, STACK_CAP, &'a mut Compact<K>, &'a mut CompactBufStack<K, STACK_CAP>>;
        type OwnedBuf<'a, K> = CompactBuf<K, STACK_CAP, Compact<K>, CompactBufStack<K, STACK_CAP>>;
        println!("stack buf size: {}", size_of::<StackBuf::<u32>>());
        println!("owned buf size: {}", size_of::<OwnedBuf::<u32>>());
        //        println!("CompactBufferStack {}", size_of::<CompactBufferStack>());
        println!("CompactEntry {}", size_of::<CompactEntry::<u32, u32>>());
    }
}
