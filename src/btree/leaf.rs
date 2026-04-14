use super::node::*;
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, dealloc};
use core::borrow::Borrow;
use core::fmt;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, needs_drop, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull, null_mut};

/// Header size at start of key area for leaf nodes
const LEAF_HEAD_SIZE: usize = 16; // 8B header + 8B padding

/// Leaf node prev/next pointers
#[repr(C)]
pub(super) struct LeafPtrs {
    pub prev: *mut NodeHeader,
    pub next: *mut NodeHeader,
}

/// Leaf node wrapper - wraps Node and provides leaf-specific operations
pub(super) struct LeafNode<K, V> {
    base: NodeBase,
    _phan: PhantomData<fn(&K, &V)>,
}
impl<K, V> Clone for LeafNode<K, V> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self { base: self.base.clone(), _phan: Default::default() }
    }
}

impl<K, V> Deref for LeafNode<K, V> {
    type Target = NodeBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<K, V> DerefMut for LeafNode<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

impl<K, V> PartialEq for LeafNode<K, V> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.get_ptr() == other.get_ptr()
    }
}

impl<K, V> LeafNode<K, V> {
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
        assert!(align_of::<V>() <= 8);
        if align < align_of::<V>() {
            align = align_of::<V>();
        }
        if align < PTR_ALIGN {
            align = PTR_ALIGN;
        }
        let key_size = size_of::<K>();
        let value_size = size_of::<V>();
        // should be align to align_of
        assert!(key_size <= CACHE_LINE_SIZE - 16);
        assert!(value_size <= CACHE_LINE_SIZE - 16);
        let mut leaf_key_cap = (AREA_SIZE - LEAF_HEAD_SIZE) / key_size;
        let leaf_value_cap = (AREA_SIZE - LEAF_HEAD_SIZE) / value_size;
        if leaf_key_cap > leaf_value_cap {
            leaf_key_cap = leaf_value_cap;
        }
        match Layout::from_size_align(NODE_SIZE, align) {
            Ok(l) => (leaf_key_cap as u32, l),
            Err(_) => panic!("invalid layout"),
        }
    }

    #[inline(always)]
    pub unsafe fn alloc() -> Self {
        let mut base = NodeBase::_alloc(Self::LAYOUT.1);
        let header = base.get_header_mut();
        header.height = 0; // Leaf nodes have height 0
        header.count = 0;
        let this = Self { base, _phan: Default::default() };
        unsafe {
            let ptrs = this.brothers();
            (*ptrs).prev = null_mut();
            (*ptrs).next = null_mut();
        }
        this
    }

    #[inline(always)]
    pub fn dealloc<const DROP_ITEM: bool>(self) {
        let count = self.key_count();
        unsafe {
            if DROP_ITEM {
                if needs_drop::<K>() {
                    for i in 0..count {
                        (*self.key_ptr(i)).assume_init_drop();
                    }
                }
                if needs_drop::<V>() {
                    for i in 0..count {
                        (*self.value_ptr(i)).assume_init_drop();
                    }
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT.1);
        }
    }

    #[inline(always)]
    pub fn is_full(&self) -> bool {
        let avail = Self::cap() - self.key_count();
        avail == 0
    }

    #[cfg(test)]
    pub(super) fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(LEAF_HEAD_SIZE, 0)
    }

    #[cfg(test)]
    pub(super) fn get_values(&self) -> &[V] {
        self.base.get_array::<V>(AREA_SIZE + LEAF_HEAD_SIZE, 0)
    }

    /// Get pointer to key at index
    #[inline(always)]
    pub unsafe fn key_ptr(&self, idx: u32) -> *mut MaybeUninit<K> {
        unsafe { self.base.item_ptr::<MaybeUninit<K>>(LEAF_HEAD_SIZE, idx) }
    }

    /// Get pointer to value at index
    #[inline(always)]
    pub unsafe fn value_ptr(&self, idx: u32) -> *mut MaybeUninit<V> {
        unsafe { self.base.item_ptr::<MaybeUninit<V>>(AREA_SIZE + LEAF_HEAD_SIZE, idx) }
    }

    /// Get pointer to LeafPtrs
    #[inline(always)]
    pub unsafe fn brothers(&self) -> *mut LeafPtrs {
        unsafe { NodeHeader::get_field::<LeafPtrs>(self.header, AREA_SIZE) }
    }

    #[inline(always)]
    pub fn get_left_node(&self) -> Option<Self> {
        unsafe {
            let p = (*self.brothers()).prev;
            if p.is_null() {
                return None;
            }
            Some(Self::from_header(p))
        }
    }

    #[inline(always)]
    pub fn get_right_node(&self) -> Option<Self> {
        unsafe {
            let p = (*self.brothers()).next;
            if p.is_null() {
                return None;
            }
            Some(Self::from_header(p))
        }
    }

    /// Create LeafNode from header pointer
    #[inline(always)]
    pub unsafe fn from_header(header: *mut NodeHeader) -> Self {
        unsafe {
            debug_assert!((*header).is_leaf());
            Self {
                base: NodeBase { header: NonNull::new_unchecked(header) },
                _phan: Default::default(),
            }
        }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search<Q>(&self, key: &Q) -> (u32, bool)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base._search::<K, Q>(LEAF_HEAD_SIZE, key)
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline]
    pub fn insert_no_split_with_idx(&mut self, idx: u32, key: K, value: V) -> *mut V {
        debug_assert!(self.key_count() < Self::cap());
        unsafe {
            self.base._insert::<K, V>(LEAF_HEAD_SIZE, AREA_SIZE + LEAF_HEAD_SIZE, idx, key, value)
        }
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[cfg(test)]
    #[inline]
    pub fn insert_no_split(&mut self, key: K, value: V) -> *mut V
    where
        K: Ord,
    {
        debug_assert!(self.key_count() < Self::cap());
        let (idx, is_equal) = self.search(&key);
        debug_assert!(!is_equal);
        self.insert_no_split_with_idx(idx, key, value)
    }

    #[inline]
    pub fn remove_pair_no_borrow(&mut self, idx: u32) -> (K, V) {
        let left = self.key_count() - 1;
        let key = self._remove_slot::<K>(LEAF_HEAD_SIZE, idx, left);
        let value = self._remove_slot::<V>(AREA_SIZE + LEAF_HEAD_SIZE, idx, left);
        self.get_header_mut().count = left;
        (key, value)
    }

    #[inline]
    pub fn remove_value_no_borrow(&mut self, idx: u32) -> V {
        let left = self.key_count() - 1;
        unsafe {
            let key_p = self.item_ptr::<MaybeUninit<K>>(LEAF_HEAD_SIZE, idx);
            if needs_drop::<K>() {
                (*key_p).assume_init_drop();
            }
            if left > idx {
                ptr::copy(key_p.add(1), key_p, (left - idx) as usize);
            }
        }
        let value = self._remove_slot::<V>(AREA_SIZE + LEAF_HEAD_SIZE, idx, left);
        self.get_header_mut().count = left;
        value
    }

    /// NOTE: it will require two calls to remove (k, v) pair, so the count is not decrease here
    #[inline]
    fn _remove_slot<T>(&mut self, header_offset: usize, idx: u32, mut left: u32) -> T {
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

    #[inline(always)]
    pub fn clone_first_key(&self) -> K
    where
        K: Clone,
    {
        debug_assert!(self.key_count() > 0);
        unsafe { (*self.key_ptr(0)).assume_init_ref().clone() }
    }

    #[inline]
    pub const fn cap() -> u32 {
        Self::LAYOUT.0
    }

    /// move items at the begining of this node to the tail of left_node
    #[inline(always)]
    pub fn insert_borrow_left(
        &mut self, left_node: &mut Self, mut idx: u32, key: K, value: V,
    ) -> *mut V {
        debug_assert!(idx != 0);
        debug_assert!(idx < self.key_count());
        unsafe {
            let first_key_p = self.key_ptr(0);
            let first_val_p = self.value_ptr(0);
            let move_key = (*first_key_p).assume_init_read();
            let move_value = (*first_val_p).assume_init_read();
            left_node.insert_no_split_with_idx(left_node.key_count(), move_key, move_value);
            idx -= 1;
            if idx > 0 {
                ptr::copy(first_key_p.add(1), first_key_p, idx as usize);
                ptr::copy(first_val_p.add(1), first_val_p, idx as usize);
            }
            (*self.key_ptr(idx)).write(key);
            let value_p = self.value_ptr(idx);
            (*value_p).write(value);
            value_p as *mut V
        }
    }

    #[inline(always)]
    pub fn borrow_right(&mut self, right_node: &mut Self) {
        let idx = self.key_count() - 1;
        unsafe {
            let move_key = (*self.key_ptr(idx)).assume_init_read();
            let move_value = (*self.value_ptr(idx)).assume_init_read();
            right_node.insert_no_split_with_idx(0, move_key, move_value);
            self.get_header_mut().count = idx;
        }
    }

    #[inline(always)]
    pub fn copy_left(&mut self, left_node: &mut Self, copy_count: u32) {
        let left_count = left_node.key_count();
        debug_assert!(copy_count <= self.key_count());
        debug_assert!(left_count + copy_count <= Self::cap());

        unsafe {
            // copy keys using bulk copy
            let first_key = self.key_ptr(0);
            let dst_key = left_node.key_ptr(left_count);
            ptr::copy_nonoverlapping(first_key, dst_key, copy_count as usize);
            // copy values using bulk copy
            let first_val = self.value_ptr(0);
            let dst_val = left_node.value_ptr(left_count);
            ptr::copy_nonoverlapping(first_val, dst_val, copy_count as usize);
            left_node.get_header_mut().count += copy_count;
        }
    }

    /// move the items to the tail of right_node
    #[inline(always)]
    pub fn move_right(&mut self, right_node: &mut Self, start_idx: u32, move_count: u32) {
        self.copy_right::<true>(right_node, start_idx, move_count);
        self.get_header_mut().count -= move_count;
    }

    /// If append == true, copy the items to the tail of right_node,
    /// If append == false, prepend to items to the front of right_node.
    ///
    /// # Safety
    ///
    /// It does not change the count of current node
    #[inline]
    pub fn copy_right<const APPEND: bool>(
        &mut self, right_node: &mut Self, start_idx: u32, copy_count: u32,
    ) {
        let right_count = right_node.key_count();
        debug_assert!(start_idx + copy_count <= self.key_count());
        debug_assert!(right_count + copy_count <= Self::cap());
        unsafe {
            if APPEND {
                // Append to tail of right_node

                // Move keys using bulk copy
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(right_count);
                ptr::copy_nonoverlapping(src_key, dst_key, copy_count as usize);

                // Move values using bulk copy
                let src_val = self.value_ptr(start_idx);
                let dst_val = right_node.value_ptr(right_count);
                ptr::copy_nonoverlapping(src_val, dst_val, copy_count as usize);
            } else {
                // Prepend to head of right_node
                // Shift existing elements in right_node to make space
                if right_count > 0 {
                    let src_key = right_node.key_ptr(0);
                    let dst_key = right_node.key_ptr(copy_count);
                    ptr::copy(src_key, dst_key, right_count as usize);

                    let src_val = right_node.value_ptr(0);
                    let dst_val = right_node.value_ptr(copy_count);
                    ptr::copy(src_val, dst_val, right_count as usize);
                }

                // Move new elements to the front
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(0);
                ptr::copy_nonoverlapping(src_key, dst_key, copy_count as usize);

                let src_val = self.value_ptr(start_idx);
                let dst_val = right_node.value_ptr(0);
                ptr::copy_nonoverlapping(src_val, dst_val, copy_count as usize);
            }
            right_node.get_header_mut().count += copy_count;
        }
    }

    #[inline]
    pub fn insert_with_split(&mut self, idx: u32, key: K, value: V) -> (Self, *mut V) {
        let mut new_leaf = unsafe { LeafNode::<K, V>::alloc() };
        let count = self.key_count();
        unsafe {
            if let Some(right) = self.get_right_node() {
                (*right.brothers()).prev = new_leaf.get_ptr();
                (*new_leaf.brothers()).next = right.get_ptr();
            }
            (*new_leaf.brothers()).prev = self.get_ptr();
            (*self.brothers()).next = new_leaf.get_ptr();
        }
        if idx < count {
            let split_idx = count >> 1;
            // if split_idx == idx, then the new key must < old key at split_idx
            let insert_left = split_idx >= idx;
            let total_copy = count - split_idx;
            if insert_left {
                self.move_right(&mut new_leaf, split_idx, total_copy);
                let ptr_v = self.insert_no_split_with_idx(idx, key, value);
                (new_leaf, ptr_v)
            } else {
                debug_assert!(idx > split_idx);
                let first_copy = idx - split_idx;
                self.copy_right::<true>(&mut new_leaf, split_idx, first_copy);
                let ptr_v = new_leaf.insert_no_split_with_idx(first_copy, key, value);
                if total_copy > first_copy {
                    self.copy_right::<true>(
                        &mut new_leaf,
                        split_idx + first_copy,
                        total_copy - first_copy,
                    );
                }
                self.get_header_mut().count = split_idx;
                (new_leaf, ptr_v)
            }
        } else {
            let ptr_v = new_leaf.insert_no_split_with_idx(0, key, value);
            (new_leaf, ptr_v)
        }
    }

    /// Unlink this node from the sibling chain
    /// return right_node ptr
    #[inline(always)]
    pub fn unlink(&mut self) -> *mut NodeHeader {
        unsafe {
            let prev = (*self.brothers()).prev;
            let next = (*self.brothers()).next;
            if !prev.is_null() {
                (*LeafNode::<K, V>::from_header(prev).brothers()).next = next;
            }
            if !next.is_null() {
                let right_node = LeafNode::<K, V>::from_header(next);
                (*right_node.brothers()).prev = prev;
            }
            next
        }
    }
}

impl<K, V> fmt::Debug for LeafNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LeafNode({:p} count: {})", self.base.header, self.key_count())
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Display for LeafNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let count = self.key_count();
        write!(f, "LeafNode({:p} count: {}, keys: [", self.base.header, count)?;
        for i in 0..count {
            unsafe {
                let key = (*self.key_ptr(i)).assume_init_ref();
                let val = (*self.value_ptr(i)).assume_init_ref();
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}: {:?}", key, val)?;
            }
        }
        write!(f, "])")
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> LeafNode<K, V> {
    /// Validate leaf node structure
    /// Returns the number of keys in this node
    pub fn validate(&self, min_key: Option<&K>, max_key: Option<&K>) -> usize {
        let count = self.key_count() as usize;

        // Validate count is within bounds
        assert!(
            count as u32 <= Self::cap(),
            "Leaf {:?} node has too many keys: {} > {}",
            self,
            count,
            Self::cap()
        );

        if count == 0 {
            return 0;
        }

        unsafe {
            // Validate keys are sorted
            for i in 1..count {
                let prev_key = (*self.key_ptr((i - 1) as u32)).assume_init_ref();
                let curr_key = (*self.key_ptr(i as u32)).assume_init_ref();
                assert!(
                    prev_key < curr_key,
                    "Leaf {:?} node keys not sorted: {:?} >= {:?}",
                    self,
                    prev_key,
                    curr_key
                );
            }

            // Validate keys are within parent bounds
            let first_key = (*self.key_ptr(0)).assume_init_ref();
            let last_key = (*self.key_ptr((count - 1) as u32)).assume_init_ref();

            if let Some(min) = min_key {
                assert!(
                    min <= first_key,
                    "Leaf {:?} first key {:?} < parent min {:?}",
                    self,
                    first_key,
                    min
                );
            }
            if let Some(max) = max_key {
                assert!(
                    last_key < max,
                    "Leaf {:?} last key {:?} >= parent max {:?}",
                    self,
                    last_key,
                    max
                );
            }
        }

        count
    }
}
