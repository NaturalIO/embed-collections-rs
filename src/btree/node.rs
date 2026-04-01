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
    pub(crate) height: u32,
    /// Count of items in the node
    pub(crate) count: u32,
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
        self.header.as_ptr() as *mut NodeHeader
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

    /// Check if this is a leaf node
    #[inline(always)]
    pub fn is_leaf(&self) -> bool {
        self.get_header().is_leaf()
    }

    /// Get count of items in the node
    #[inline(always)]
    pub fn count(&self) -> u32 {
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
            let count = self.count();
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

    /// NOTE: it will require two calls to remove (k, v) pair, so the count is not decrease here
    #[inline]
    pub unsafe fn _remove_slot<T>(&mut self, header_offset: usize, idx: u32, mut left: u32) -> T {
        debug_assert!(idx < left + 1);
        unsafe {
            let item_p = self.item_ptr::<T>(header_offset, idx);
            let item = item_p.read();
            left -= idx;
            if left > 0 {
                ptr::copy(item_p.add(1), item_p, left as usize);
            }
            item
        }
    }

    /// Insert key value at position and return value pointer (entry insert needs to return reference)
    ///
    /// # Safety
    /// it does not check is_full
    pub unsafe fn _insert<K, V>(
        &mut self, key_header_offset: usize, value_header_offset: usize, idx: u32, key: K, value: V,
    ) -> *mut V {
        let count = self.count() as u32;
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
    #[inline]
    pub fn find_leaf(&self, key: &K) -> LeafNode<K, V> {
        match self {
            Node::Leaf(node) => return node.clone(),
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
    pub fn find_leaf_with_cache(&self, cache: &mut PathCache<K, V>, key: &K) -> LeafNode<K, V> {
        match &self {
            Node::Leaf(node) => return node.clone(),
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

    /// If depth == 0, return the root itself
    #[inline]
    pub fn find_child_with_cache(
        &self, cache: &mut PathCache<K, V>, key: &K, mut depth: u32,
    ) -> InterNode<K, V> {
        if let Node::Inter(node) = &self {
            let mut cur = node.clone();
            while depth > 0 {
                depth -= 1;
                let idx = cur.search_child(key);
                cache.push(cur.clone(), idx);
                cur = cur.get_child_as_inter(idx);
            }
            cur
        } else {
            unreachable!();
        }
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
#[repr(u8)]
pub(super) enum PathState {
    Current,
    // the cursor has been moved left, so cache content is to the right brother of leaf cursor
    Left,
    // the cursor has been moved right, so cache content is to the left brother of leaf cursor
    Right,
    // the cache content should be ignore
    Stale,
}

pub(super) struct PathCache<K, V> {
    pub state: PathState,
    pub depth: u32,
    // Various<ptr> has 13 cap, which is quite enough for btree
    pub inner: Various<(InterNode<K, V>, u32)>,
}

impl<K: Ord, V> PathCache<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self { inner: Various::new(), state: PathState::Current, depth: 0 }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.depth = 0;
    }

    #[inline]
    pub fn move_left(&mut self) {
        let state = match self.state {
            PathState::Current => PathState::Left,
            PathState::Right => PathState::Current,
            _ => {
                let _ = self.inner.take();
                PathState::Stale
            }
        };
        self.state = state;
    }

    #[inline]
    pub fn move_right(&mut self) {
        let state = match self.state {
            PathState::Current => PathState::Right,
            PathState::Left => PathState::Current,
            _ => {
                let _ = self.inner.take();
                PathState::Stale
            }
        };
        self.state = state;
    }

    #[inline(always)]
    pub fn change_state(&mut self, state: PathState) {
        match state {
            PathState::Current => {}
            PathState::Left => self.move_left(),
            PathState::Right => self.move_right(),
            PathState::Stale => self.state = PathState::Stale,
        }
    }

    #[inline(always)]
    pub fn push(&mut self, inter: InterNode<K, V>, idx: u32) {
        self.inner.push((inter, idx));
        self.depth += 1;
    }

    /// pop parent and its idx from cache, if we need new_root, return None
    ///
    /// If the cache has no acurrate infomation, fallback search top-down from
    /// root or upper level.
    #[inline(always)]
    pub fn pop(&mut self, key: &K, root: &Node<K, V>) -> Option<(InterNode<K, V>, u32)> {
        match self.state {
            PathState::Stale => {
                if self.depth == 0 {
                    return None;
                }
                let depth = self.depth - 1;
                self.depth = depth;
                let mut new_cache = Self::new();
                root.find_child_with_cache(&mut new_cache, key, depth);
                let res = new_cache.pop(key, root);
                self.inner = new_cache.inner.take();
                res
            }
            PathState::Current => {
                if let Some((node, idx)) = self.inner.pop() {
                    self.depth -= 1;
                    Some((node, idx))
                } else if self.depth == 0 {
                    None
                } else {
                    unreachable!();
                }
            }
            PathState::Left => {
                let depth = self.depth;
                if depth == 0 {
                    return None;
                }
                let (node, idx) = self.inner.pop().unwrap();
                self.depth = depth - 1;
                if idx > 0 {
                    return Some((node, idx)); // have common parent
                }
                todo!();
                // iterate top to find a common ancestor
            }
            PathState::Right => {
                let depth = self.depth;
                if depth == 0 {
                    return None;
                }
                let (node, idx) = self.inner.pop().unwrap();
                self.depth = depth - 1;
                if idx + 1 < InterNode::<K, V>::cap() as u32 {
                    return Some((node, idx)); // have common parent
                }
                todo!();
                // iterate top to find a common ancestor
            }
        }
    }
}
