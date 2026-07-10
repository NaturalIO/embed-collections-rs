use super::{inter::*, leaf::*};
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, alloc, handle_alloc_error};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::mem::{align_of, size_of};
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
        unsafe { (p.as_ptr() as *mut u8).add(offset) as *mut T }
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
    pub fn get_ptr(&self) -> *const NodeHeader {
        self.header.as_ptr()
    }

    #[inline(always)]
    pub fn get_ptr_mut(&mut self) -> *mut NodeHeader {
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
    pub unsafe fn item_ptr<T>(&self, start_offset: usize, idx: u32) -> *const T {
        let mut v_size = size_of::<T>();
        if v_size == 0 {
            v_size = 1;
        }
        unsafe { NodeHeader::get_field::<T>(self.header, start_offset + idx as usize * v_size) }
    }

    /// Get pointer to key at index with given header offset
    ///
    /// # Safety
    ///
    /// we should enough item_size has a minminum value aligned to PTR_ALIGN during cal_layout
    #[inline(always)]
    pub unsafe fn item_ptr_mut<T>(&mut self, start_offset: usize, idx: u32) -> *mut T {
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
    pub fn _search<K, Q>(&self, header_offset: usize, count: u32, key: &Q) -> (u32, bool)
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
            let key_p = self.item_ptr_mut::<K>(key_header_offset, idx);
            if idx < count {
                ptr::copy(key_p, key_p.add(1), (count - idx) as usize);
            }
            key_p.write(key);
            let value_p = self.item_ptr_mut::<V>(value_header_offset, idx);
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

#[cfg(test)]
impl<K, V> From<LeafNode<K, V>> for Node<K, V> {
    fn from(node: LeafNode<K, V>) -> Self {
        Node::<K, V>::Leaf(node)
    }
}

#[cfg(test)]
impl<K, V> From<InterNode<K, V>> for Node<K, V> {
    fn from(node: InterNode<K, V>) -> Self {
        Node::<K, V>::Inter(node)
    }
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
    #[inline(always)]
    pub fn from_root_ptr(p: NonNull<NodeHeader>) -> Self {
        if Self::root_is_leaf(p) {
            Self::Leaf(LeafNode::<K, V>::from_root_ptr(p))
        } else {
            Self::Inter(InterNode::<K, V>::from(p))
        }
    }

    #[inline(always)]
    pub fn root_is_leaf(p: NonNull<NodeHeader>) -> bool {
        p.as_ptr() as usize & NodeHeader::LEAF_MASK > 0
    }

    #[cfg(test)]
    pub fn to_root_ptr(&self) -> NonNull<NodeHeader> {
        match self {
            Self::Inter(inter) => inter.to_root_ptr(),
            Self::Leaf(leaf) => leaf.to_root_ptr(),
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
}

#[inline(always)]
pub(super) fn borrow_key_from_bound<Q: ?Sized>(bound: Bound<&Q>) -> Option<&Q> {
    match bound {
        Bound::Unbounded => None,
        Bound::Included(key) => Some(key),
        Bound::Excluded(key) => Some(key),
    }
}
