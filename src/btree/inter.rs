use super::leaf::*;
use super::node::*;
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, dealloc};
use core::fmt;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, needs_drop, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull};

/// Header size at start of key area for internal nodes
const INTER_KEY_HEAD_SIZE: usize = 8;

/// Header size at start of value area for internal nodes
const INTER_PTR_HEAD_SIZE: usize = 0;

/// Internal node wrapper - wraps Node and provides internal node-specific operations
pub(super) struct InterNode<K, V> {
    base: NodeBase,
    _phan: PhantomData<fn(&K, &V)>,
}

impl<K, V> Clone for InterNode<K, V> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self { base: self.base.clone(), _phan: Default::default() }
    }
}

impl<K, V> Deref for InterNode<K, V> {
    type Target = NodeBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<K, V> DerefMut for InterNode<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

impl<K, V> InterNode<K, V> {
    /// (inter_key_cap, leaf_key_cap)
    const LAYOUT: (u32, Layout) = Self::cal_layout();

    /// return inter_key_cap, leaf_key_cap.
    /// where:
    /// - inter_key_cap + 1 inter_value_cap;
    /// - leaf_key_cap = leaf_value_cap;
    ///
    /// assert K, V can fit into the cacheline after devided by header.
    const fn cal_layout() -> (u32, Layout) {
        let mut align = align_of::<K>();
        assert!(align <= 8);
        let key_size = size_of::<K>();
        if align < PTR_ALIGN {
            align = PTR_ALIGN;
        }
        assert!(size_of::<NodeHeader>() == INTER_KEY_HEAD_SIZE);
        assert!(key_size <= CACHE_LINE_SIZE - 16);
        let mut inter_key_cap = (AREA_SIZE - INTER_KEY_HEAD_SIZE) / key_size;
        let inter_value_cap = (AREA_SIZE - INTER_PTR_HEAD_SIZE) / PTR_SIZE;
        if inter_key_cap > inter_value_cap - 1 {
            inter_key_cap = inter_value_cap - 1;
        }
        match Layout::from_size_align(NODE_SIZE, align) {
            Ok(l) => (inter_key_cap as u32, l),
            Err(_) => panic!("invalid layout"),
        }
    }

    #[inline(always)]
    pub unsafe fn alloc(height: u32) -> Self {
        let mut base = NodeBase::_alloc(Self::LAYOUT.1);
        let header = base.get_header_mut();
        header.height = height; // Internal nodes have height > 0
        header.count = 0;
        Self { base, _phan: Default::default() }
    }

    #[inline(always)]
    pub unsafe fn dealloc(&mut self) {
        unsafe {
            if needs_drop::<K>() {
                let count = self.key_count();
                for i in 0..count as u32 {
                    (*self.key_ptr(i)).assume_init_drop();
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT.1);
        }
    }

    #[inline(always)]
    pub(super) fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(INTER_KEY_HEAD_SIZE, 0)
    }

    #[inline]
    pub const fn cap() -> u32 {
        Self::LAYOUT.0
    }

    /// Create InterNode from header pointer
    #[inline(always)]
    pub(crate) unsafe fn from_header(header: NonNull<NodeHeader>) -> Self {
        unsafe { debug_assert!(!header.as_ref().is_leaf()) };
        Self { base: NodeBase { header }, _phan: Default::default() }
    }

    #[inline(always)]
    pub(crate) fn set_left_ptr(&mut self, child_ptr: *mut NodeHeader) {
        unsafe {
            let p = self.child_ptr(0);
            p.write(child_ptr)
        }
    }
    #[inline(always)]
    pub fn is_full(&self) -> Result<(), u32> {
        let avail = Self::cap() - self.key_count();
        if avail == 0 { Ok(()) } else { Err(avail as u32) }
    }

    /// Get pointer to key at index
    #[inline(always)]
    pub unsafe fn key_ptr(&self, idx: u32) -> *mut MaybeUninit<K> {
        unsafe { self.base.item_ptr::<MaybeUninit<K>>(INTER_KEY_HEAD_SIZE, idx) }
    }

    /// Get pointer to child at index
    #[inline(always)]
    pub unsafe fn child_ptr(&self, idx: u32) -> *mut *mut NodeHeader {
        unsafe { self.base.item_ptr::<*mut NodeHeader>(AREA_SIZE + INTER_PTR_HEAD_SIZE, idx) }
    }

    #[inline]
    pub fn get_child(&self, idx: u32) -> Node<K, V> {
        unsafe {
            let child_ptr = *self.child_ptr(idx);
            if child_ptr.is_null() {
                panic!("{:?} child {idx} is null", self);
            } else {
                if (*child_ptr).is_leaf() {
                    Node::Leaf(LeafNode::<K, V>::from_header(NonNull::new_unchecked(child_ptr)))
                } else {
                    Node::Inter(InterNode::<K, V>::from_header(NonNull::new_unchecked(child_ptr)))
                }
            }
        }
    }

    /// Get child at index as a Node
    #[inline(always)]
    pub fn get_child_as_inter(&self, idx: u32) -> InterNode<K, V> {
        unsafe {
            let child_ptr = *self.child_ptr(idx);
            if child_ptr.is_null() {
                panic!("child is null");
            } else {
                InterNode::<K, V>::from_header(NonNull::new_unchecked(child_ptr))
            }
        }
    }
}

impl<K: Ord, V> InterNode<K, V> {
    /// (inter_key_cap, leaf_key_cap)
    #[inline(always)]
    pub fn new_root(
        height: u32, promote_key: K, left_ptr: *mut NodeHeader, right_ptr: *mut NodeHeader,
    ) -> Self {
        let mut root = unsafe { Self::alloc(height) };
        root.set_left_ptr(left_ptr);
        root.insert_no_split_with_idx(0, promote_key, right_ptr);
        root
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search_child(&self, key: &K) -> u32
    where
        K: Ord,
    {
        let (idx, is_equal) = self.base._search::<K>(INTER_KEY_HEAD_SIZE, key);
        if is_equal { idx + 1 } else { idx }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search_key(&self, key: &K) -> u32
    where
        K: Ord,
    {
        let (idx, _is_equal) = self.base._search::<K>(INTER_KEY_HEAD_SIZE, key);
        idx
    }

    #[inline(always)]
    pub fn insert_no_split(&mut self, key: K, ptr: *mut NodeHeader) {
        let idx = self.search_key(&key);
        self.insert_no_split_with_idx(idx, key, ptr);
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline(always)]
    fn insert_no_split_with_idx(&mut self, idx: u32, key: K, ptr: *mut NodeHeader) {
        debug_assert!(self.key_count() < Self::cap());
        let _ = unsafe {
            self.base._insert::<K, *mut NodeHeader>(
                INTER_KEY_HEAD_SIZE,
                AREA_SIZE + PTR_SIZE, // the left ptr should not be touch
                idx,
                key,
                ptr,
            )
        };
    }

    /// # Safety
    ///
    /// It does not change the count of current node (It only add the count of right node)
    #[inline(always)]
    fn copy_right(&mut self, right_node: &mut Self, start_idx: u32, copy_count: u32) {
        let right_count = right_node.key_count();
        debug_assert!(start_idx + copy_count <= self.key_count() as u32);
        debug_assert!(right_count + copy_count <= Self::cap());
        unsafe {
            // Append to tail of right_node
            // Move keys using bulk copy
            let src_key = self.key_ptr(start_idx) as *mut K;
            let dst_key = right_node.key_ptr(right_count) as *mut K;
            ptr::copy_nonoverlapping(src_key, dst_key, copy_count as usize);

            // Move children using bulk copy (need to avoid touching left_ptr)
            let src_child = self.child_ptr(start_idx + 1) as *mut *mut NodeHeader;
            let dst_child = right_node.child_ptr(right_count + 1) as *mut *mut NodeHeader;
            ptr::copy_nonoverlapping(src_child, dst_child, copy_count as usize);
            // Update counts of right node
            right_node.get_header_mut().count += copy_count;
        }
    }

    /// Split internal node when inserting at idx with key and child pointer
    /// Returns (new_right_node, promote_key)
    pub fn insert_split(&mut self, key: K, child_ptr: *mut NodeHeader) -> (Self, K) {
        let cap = Self::cap();
        debug_assert_eq!(self.key_count(), Self::cap());
        let idx = self.search_key(&key);
        let mut new_node = unsafe { InterNode::<K, V>::alloc(self.height()) };
        if idx == cap {
            // the right most position, new empty node
            new_node.set_left_ptr(child_ptr);
            return (new_node, key);
        }
        let split_idx = cap >> 1;
        unsafe {
            if idx == split_idx {
                // key don't need to insert, just promote. key < split_key, so child_ptr is left_ptr
                new_node.set_left_ptr(child_ptr);
                self.copy_right(&mut new_node, split_idx, cap - split_idx);
                self.get_header_mut().count = split_idx;
                return (new_node, key);
            }
            let promote_key = (*self.key_ptr(split_idx)).assume_init_read();
            new_node.set_left_ptr(*self.child_ptr(split_idx + 1));
            // Determine which side the insertion should go
            if idx < split_idx {
                let right_count = cap - split_idx - 1;
                if right_count > 0 {
                    self.copy_right(&mut new_node, split_idx + 1, right_count);
                }
                self.get_header_mut().count = split_idx;
                // Safety: update the count before inserting new key
                // insert to the left node
                self.insert_no_split_with_idx(idx, key, child_ptr);
            } else {
                if idx > split_idx + 1 {
                    self.copy_right(&mut new_node, split_idx + 1, idx - split_idx - 1);
                }
                // because split_idx is promote_key, skip it
                new_node.insert_no_split_with_idx(idx - split_idx - 1, key, child_ptr);
                if idx < cap {
                    self.copy_right(&mut new_node, idx, cap - idx);
                }
                self.get_header_mut().count = split_idx;
            }
            (new_node, promote_key)
        }
    }

    #[inline]
    pub fn remove_child(&mut self, key: &K)
    where
        K: Ord,
    {
        let (idx, is_equal) = self.base._search(INTER_KEY_HEAD_SIZE, key);
        let count = self.key_count() as u32; // the count is equal to keys count, but value count should + 1
        if !is_equal {
            if idx != 0 {
                panic!("imposible remove a child with key not in the node");
            }
            // remove the left child
            unsafe {
                self.base._remove_slot::<*mut NodeHeader>(AREA_SIZE + INTER_PTR_HEAD_SIZE, 0, count)
            };
        } else {
            unsafe {
                let _key = self.base._remove_slot::<K>(INTER_KEY_HEAD_SIZE, idx, count);
                // let the key drop
                self.base._remove_slot::<*mut NodeHeader>(
                    AREA_SIZE + INTER_PTR_HEAD_SIZE,
                    idx + 1,
                    count,
                );
            }
        }
        self.get_header_mut().count = count - 1;
    }
}

impl<K, V> fmt::Debug for InterNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "InterNode({:p} height:{}, count:{})",
            self.base.header,
            self.height(),
            self.key_count() + 1
        )
    }
}

impl<K: fmt::Debug, V> fmt::Display for InterNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let count = self.key_count();
        write!(
            f,
            "InterNode({:p} height:{}, count:{}, keys: [",
            self.base.header,
            self.height(),
            count + 1
        )?;
        for i in 0..count {
            unsafe {
                let key = (*self.key_ptr(i as u32)).assume_init_ref();
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}", key)?;
            }
        }
        write!(f, "])")
    }
}
