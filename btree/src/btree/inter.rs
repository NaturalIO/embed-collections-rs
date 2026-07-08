use super::{helper::*, leaf::*, node::*};
use crate::{CACHE_LINE_SIZE, trace_log};
use alloc::alloc::{Layout, dealloc};
use core::borrow::Borrow;
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

impl<K, V> From<NonNull<NodeHeader>> for InterNode<K, V> {
    /// Create InterNode from header pointer
    #[inline(always)]
    fn from(header: NonNull<NodeHeader>) -> Self {
        unsafe {
            debug_assert!(!header.as_ref().is_leaf());
            Self { base: NodeBase { header }, _phan: Default::default() }
        }
    }
}

impl<K, V> InterNode<K, V> {
    /// (inter_key_cap, leaf_key_cap)
    const LAYOUT: (u32, Layout) = Self::cal_layout();

    pub(super) const UNDERFLOW_CAP: u32 = Self::LAYOUT.0 / 3;

    /// return inter_key_cap, leaf_key_cap.
    /// where:
    /// - inter_key_cap + 1 inter_value_cap;
    /// - leaf_key_cap = leaf_value_cap;
    ///
    /// assert K, V can fit into the cacheline after divided by header.
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
    pub fn dealloc<const DROP_ITEM: bool>(self) {
        unsafe {
            if DROP_ITEM && needs_drop::<K>() {
                let count = self.key_count();
                for i in 0..count {
                    (*self.key_ptr(i)).assume_init_drop();
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT.1);
        }
    }

    #[cfg(test)]
    pub(super) fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(INTER_KEY_HEAD_SIZE, 0)
    }

    #[inline]
    pub const fn cap() -> u32 {
        Self::LAYOUT.0
    }

    #[inline(always)]
    pub fn to_root_ptr(&self) -> NonNull<NodeHeader> {
        self.header
    }

    /// Create InterNode from header pointer
    #[inline(always)]
    pub unsafe fn from_header(header: *mut NodeHeader) -> Self {
        Self::from(unsafe { NonNull::new_unchecked(header) })
    }

    #[inline(always)]
    pub fn set_left_ptr(&mut self, child_ptr: *mut NodeHeader) {
        unsafe {
            let p = self.child_ptr(0);
            p.write(child_ptr)
        }
    }
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        let avail = Self::cap() - self.key_count();
        avail == 0
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

    #[inline(always)]
    pub fn get_child_ptr(&self, idx: u32) -> *mut NodeHeader {
        unsafe { *self.child_ptr(idx) }
    }

    #[inline]
    pub fn get_child(&self, idx: u32) -> Node<K, V> {
        unsafe {
            let child_ptr = *self.child_ptr(idx);
            if child_ptr.is_null() {
                panic!("{:?} child {idx} is null", self);
            } else if self.height() == 1 {
                Node::Leaf(LeafNode::<K, V>::from_header(child_ptr))
            } else {
                Node::Inter(InterNode::<K, V>::from_header(child_ptr))
            }
        }
    }

    #[inline]
    pub fn get_child_as_inter(&self, idx: u32) -> Self {
        unsafe {
            let child_ptr = *self.child_ptr(idx);
            if child_ptr.is_null() {
                panic!("{:?} child {idx} is null", self);
            } else {
                debug_assert!(!(*child_ptr).is_leaf());
                InterNode::<K, V>::from_header(child_ptr)
            }
        }
    }

    #[inline]
    pub fn get_child_as_leaf(&self, idx: u32) -> LeafNode<K, V> {
        unsafe {
            let child_ptr = *self.child_ptr(idx);
            if child_ptr.is_null() {
                panic!("{:?} child {idx} is null", self);
            } else {
                debug_assert!((*child_ptr).is_leaf());
                LeafNode::<K, V>::from_header(child_ptr)
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
    pub fn search_child<Q>(&self, key: &Q) -> u32
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let key_count = self.key_count();
        let (idx, is_equal) = self.base._search::<K, Q>(INTER_KEY_HEAD_SIZE, key_count, key);
        if is_equal { idx + 1 } else { idx }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search_child_smart<Q>(&self, key: &Q, is_seq: &mut bool) -> u32
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let key_count = self.key_count();
        let (idx, is_equal) = if !*is_seq {
            // random is more likely
            self.base._search::<K, Q>(INTER_KEY_HEAD_SIZE, key_count, key)
        } else {
            if key_count > 0 {
                let key_ref: &Q =
                    unsafe { (*self.key_ptr(key_count - 1)).assume_init_ref().borrow() };
                if key_ref <= key {
                    return key_count;
                } else {
                    *is_seq = false;
                    self.base._search::<K, Q>(INTER_KEY_HEAD_SIZE, key_count, key)
                }
            } else {
                return 0;
            }
        };
        if is_equal { idx + 1 } else { idx }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search_key<Q>(&self, key: &Q) -> u32
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (idx, _is_equal) =
            self.base._search::<K, Q>(INTER_KEY_HEAD_SIZE, self.key_count(), key);
        idx
    }

    #[inline]
    pub fn find_leaf<Q>(self, key: &Q) -> LeafNode<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut height = self.height();
        let mut cur = self;
        loop {
            let idx = cur.search_child(key);
            trace_log!("find_leaf {cur:?} {idx}");
            if height > 1 {
                height -= 1;
                cur = cur.get_child_as_inter(idx);
            } else {
                return cur.get_child_as_leaf(idx);
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache<Q>(self, cache: &mut TreeInfo<K, V>, key: &Q) -> LeafNode<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut height = self.height();
        let mut cur = self;
        loop {
            let idx = cur.search_child(key);
            trace_log!("find_leaf_with_cache {cur:?} {idx}");
            cache.push(cur.clone(), idx);
            if height > 1 {
                height -= 1;
                cur = cur.get_child_as_inter(idx);
            } else {
                let leaf = cur.get_child_as_leaf(idx);
                trace_log!("find_leaf_with_cache got {leaf:?}");
                return leaf;
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache_smart<Q>(
        self, cache: &mut TreeInfo<K, V>, key: &Q, is_seq: &mut bool,
    ) -> LeafNode<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut height = self.height();
        let mut cur = self;
        loop {
            let idx = cur.search_child_smart(key, is_seq);
            trace_log!("find_leaf_with_cache {cur:?} {idx}");
            cache.push(cur.clone(), idx);
            if height > 1 {
                height -= 1;
                cur = cur.get_child_as_inter(idx);
            } else {
                let leaf = cur.get_child_as_leaf(idx);
                trace_log!("find_leaf_with_cache got {leaf:?}");
                return leaf;
            }
        }
    }

    /// Find the first leaf node
    #[inline]
    pub fn find_first_leaf(self, mut cache: Option<&mut TreeInfo<K, V>>) -> LeafNode<K, V> {
        let mut cur = self;
        let mut height = cur.height();
        loop {
            if let Some(_cache) = cache.as_mut() {
                _cache.push(cur.clone(), 0);
            }
            if height > 1 {
                height -= 1;
                cur = cur.get_child_as_inter(0);
            } else {
                return cur.get_child_as_leaf(0);
            }
        }
    }

    /// Find the last leaf node
    #[inline]
    pub fn find_last_leaf(self, mut cache: Option<&mut TreeInfo<K, V>>) -> LeafNode<K, V> {
        let mut cur = self;
        let mut height = cur.height();
        loop {
            let idx = cur.key_count();
            if let Some(_cache) = cache.as_mut() {
                _cache.push(cur.clone(), idx);
            }
            if height > 1 {
                height -= 1;
                cur = cur.get_child_as_inter(idx);
            } else {
                return cur.get_child_as_leaf(idx);
            }
        }
    }

    #[cfg(test)]
    pub fn insert_no_split(&mut self, key: K, ptr: *mut NodeHeader) {
        let idx = self.search_key(&key);
        debug_assert!(!self.is_full());
        self.insert_no_split_with_idx(idx, key, ptr);
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    ///
    /// NOTE: idx is the idx of key
    #[inline(always)]
    pub fn insert_no_split_with_idx(&mut self, idx: u32, key: K, ptr: *mut NodeHeader) {
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

    /// Insert key and child pointer at the front of the node (index 0)
    /// This is used when borrowing space from right sibling during split propagation
    /// Shifts all existing keys and children to the right by one position
    #[inline(always)]
    pub fn insert_at_front(&mut self, left_ptr: *mut NodeHeader, key: K) {
        let count = self.key_count();
        debug_assert!(count < Self::cap(), "Node is full, cannot insert at front");
        unsafe {
            if count > 0 {
                // Shift existing keys to the right by one position
                let src_key = self.key_ptr(0);
                let dst_key = self.key_ptr(1);
                ptr::copy(src_key, dst_key, count as usize);

                // Shift existing children to the right by one position
                // Note: we copy count + 1 children to include the leftmost child pointer
                let src_child = self.child_ptr(0);
                let dst_child = self.child_ptr(1);
                ptr::copy(src_child, dst_child, (count + 1) as usize);
            } else {
                // When node is empty, the current left_ptr becomes child[1]
                *self.child_ptr(1) = *self.child_ptr(0);
            }
            // Insert the new key at position 0
            (*self.key_ptr(0)).write(key);
            // Insert the new leftmost child pointer
            (*self.child_ptr(0)) = left_ptr;
            // Update the count
            self.get_header_mut().count += 1;
        }
    }

    /// # Safety
    ///
    /// It does not change the count of current node (It only add the count of right node).
    /// It does not change the left ptr of right node.
    #[inline(always)]
    fn copy_right(&mut self, right_node: &mut Self, start_idx: u32, copy_count: u32) {
        let right_count = right_node.key_count();
        debug_assert!(start_idx + copy_count <= self.key_count());
        debug_assert!(right_count + copy_count <= Self::cap());
        unsafe {
            // Append to tail of right_node
            // Move keys using bulk copy
            let src_key = self.key_ptr(start_idx) as *mut K;
            let dst_key = right_node.key_ptr(right_count) as *mut K;
            ptr::copy_nonoverlapping(src_key, dst_key, copy_count as usize);

            // Move children using bulk copy (need to avoid touching left_ptr)
            let src_child = self.child_ptr(start_idx + 1);
            let dst_child = right_node.child_ptr(right_count + 1);
            ptr::copy_nonoverlapping(src_child, dst_child, copy_count as usize);
            // Update counts of right node
            right_node.get_header_mut().count += copy_count;
        }
    }

    /// Merge right node into self, delete `right`, pull down separator key from grandparent
    /// not including the left(0) child of right
    pub fn merge(&mut self, right: Self, grand: &mut Self, right_idx: u32) {
        let key = grand.remove_mid_child(right_idx);
        let right_count = right.key_count();
        let mut self_count = self.key_count();
        debug_assert!(right_count + self_count < Self::cap());
        // Insert separator key from grandparent with right's leftmost child
        self.insert_no_split_with_idx(self_count, key, right.get_child_ptr(0));
        // Copy all keys and remaining children from right node
        if right_count > 0 {
            unsafe {
                self_count += 1;
                // Copy keys from right to self
                let src_key = right.key_ptr(0) as *mut K;
                let dst_key = self.key_ptr(self_count) as *mut K;
                ptr::copy_nonoverlapping(src_key, dst_key, right_count as usize);
                // Copy children (starting from index 1) from right to self
                let src_child = right.child_ptr(1);
                let dst_child = self.child_ptr(self_count + 1);
                ptr::copy_nonoverlapping(src_child, dst_child, right_count as usize);
                // Update count
                self.get_header_mut().count += right_count;
            }
        }
        right.dealloc::<false>();
    }

    /// Split internal node when inserting at idx with key and child pointer
    /// Returns (new_right_node, promote_key)
    pub fn insert_split(&mut self, key: K, child_ptr: *mut NodeHeader) -> (Self, K) {
        let cap = Self::cap();
        debug_assert_eq!(self.key_count(), Self::cap());
        let idx = self.search_key(&key);
        let mut new_node = unsafe { InterNode::<K, V>::alloc(self.height()) };
        if idx == cap {
            trace_log!("{self:?} insert_split new_node {new_node:?} at cap {idx} {child_ptr:p}");
            // the right most position, new empty node
            new_node.set_left_ptr(child_ptr);
            return (new_node, key);
        }
        let split_idx = cap >> 1;
        unsafe {
            if idx == split_idx {
                trace_log!(
                    "{self:?} insert_split new_node {new_node:?} at split_idx=idx {idx} {child_ptr:p}"
                );
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
                trace_log!(
                    "{self:?} insert_split new_node {new_node:?} insert {idx} < split_idx {idx} {child_ptr:p}"
                );
                let right_count = cap - split_idx - 1;
                if right_count > 0 {
                    self.copy_right(&mut new_node, split_idx + 1, right_count);
                }
                self.get_header_mut().count = split_idx;
                // Safety: update the count before inserting new key
                // insert to the left node
                self.insert_no_split_with_idx(idx, key, child_ptr);
            } else {
                trace_log!(
                    "{self:?} insert_split new_node {new_node:?} insert {idx} > split_idx {idx} {child_ptr:p}"
                );
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
    pub fn find_child_branch(
        &self, height: u32, mut idx: u32, left: bool, mut cache: Option<&mut TreeInfo<K, V>>,
    ) -> (Self, u32) {
        debug_assert!(height > 0);
        let mut child = self.get_child_as_inter(idx);
        if let Some(_cache) = cache.as_mut() {
            _cache.push(self.clone(), idx);
        }
        idx = if left { 0 } else { child.key_count() };
        while child.height() > height {
            if let Some(_cache) = cache.as_mut() {
                _cache.push(child.clone(), idx);
            }
            child = child.get_child_as_inter(idx);
        }
        (child, idx)
    }

    /// old key is auto drop, replace with new key
    #[inline(always)]
    pub fn change_key(&self, idx: u32, key: K) -> K {
        debug_assert!(self.key_count() > idx);
        unsafe {
            let k_ptr = self.key_ptr(idx);
            let old_key = (*k_ptr).assume_init_read();
            (*k_ptr).write(key);
            old_key
        }
    }

    /// a special case of remove_mid_child
    #[inline]
    pub fn remove_last_child(&mut self) -> (K, *mut NodeHeader) {
        let idx = self.key_count();
        debug_assert!(idx > 0);
        self.get_header_mut().count = idx - 1;
        unsafe {
            let key = (*self.key_ptr(idx - 1)).assume_init_read();
            let child = *self.child_ptr(idx);
            (key, child)
        }
    }

    /// If node has no key, return Err(());
    /// otherwise shift everything left and return Ok(first_key)
    #[inline(always)]
    pub fn remove_first_child(&mut self) -> K {
        let key_count = self.key_count();
        debug_assert!(key_count > 0);
        unsafe {
            let first_key_ptr = self.key_ptr(0);
            let first_child_ptr = self.child_ptr(0);
            let first_key = (*first_key_ptr).assume_init_read();
            // key[idx] is removed, move key[idx+1..] forward, (key_count - 1) keys's left
            ptr::copy(first_key_ptr.add(1), first_key_ptr, (key_count - 1) as usize);
            // child_ptr(idx) is remove, key_count of ptrs left,
            ptr::copy(first_child_ptr.add(1), first_child_ptr, key_count as usize);
            self.get_header_mut().count = key_count - 1;
            first_key
        }
    }

    #[inline(always)]
    pub fn remove_mid_child(&mut self, child_idx: u32) -> K {
        let key_count = self.key_count();
        debug_assert!(child_idx > 0);
        debug_assert!(child_idx <= key_count);
        unsafe {
            let key = (*self.key_ptr(child_idx - 1)).assume_init_read();
            if child_idx < key_count {
                ptr::copy(
                    self.key_ptr(child_idx),
                    self.key_ptr(child_idx - 1),
                    (key_count - child_idx) as usize,
                );
            }
            // NOTE: if you want to update right sep key, do it later
            // child_ptr(idx) is removed, move child[idx+1..] forward
            ptr::copy(
                self.child_ptr(child_idx + 1),
                self.child_ptr(child_idx),
                (key_count - child_idx) as usize,
            );
            self.get_header_mut().count = key_count - 1;
            key
        }
    }

    /// my_idx: parent.child_ptr[child_idx] == self
    #[inline]
    pub fn insert_rotate_left(
        &mut self, parent: &mut Self, my_idx: u32, left: &mut Self, insert_child_idx: u32, key: K,
        child_ptr: *mut NodeHeader,
    ) {
        debug_assert!(insert_child_idx <= self.key_count());
        debug_assert!(insert_child_idx > 0);
        unsafe {
            let first_key_ptr = self.key_ptr(0);
            let first_child_ptr = self.child_ptr(0);
            let first_key = (*first_key_ptr).assume_init_read();
            let first_child = *first_child_ptr;
            // key[idx] is removed, move key[idx+1..] forward, (key_count - 1) keys's left
            if insert_child_idx > 1 {
                ptr::copy(first_key_ptr.add(1), first_key_ptr, (insert_child_idx - 1) as usize);
            }
            // child_ptr(idx) is remove, key_count of ptrs left,
            ptr::copy(first_child_ptr.add(1), first_child_ptr, insert_child_idx as usize);
            (*self.key_ptr(insert_child_idx - 1)).write(key);
            (*self.child_ptr(insert_child_idx)) = child_ptr;
            let demote_key = parent.change_key(my_idx - 1, first_key);
            left.append(demote_key, first_child);
        }
    }

    /// my_idx: parent.child_ptr[child_idx] == self
    #[inline]
    pub fn rotate_right(&mut self, parent: &mut Self, my_idx: u32, right: &mut Self) {
        let (promote_key, child) = self.remove_last_child();
        let demote_key = parent.change_key(my_idx, promote_key);
        right.insert_at_front(child, demote_key);
    }

    #[inline(always)]
    pub fn append(&mut self, key: K, child: *mut NodeHeader) {
        self.insert_no_split_with_idx(self.key_count(), key, child);
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
        unsafe { write!(f, "{:p}", (*self.child_ptr(0))) }?;
        for i in 0..count {
            unsafe {
                let key = (*self.key_ptr(i)).assume_init_ref();
                write!(f, ", ")?;
                write!(f, "{:?}|{:p}", key, (*self.child_ptr(i + 1)))?;
            }
        }
        write!(f, "])")
    }
}

#[cfg(test)]
impl<K, V> PartialEq for InterNode<K, V> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.get_ptr() == other.get_ptr()
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> InterNode<K, V> {
    /// Validate internal node structure
    pub fn validate(&self) {
        let count = self.key_count() as usize;
        if count == 0 {
            return;
        }
        // Validate count is within bounds
        assert!(
            count as u32 <= Self::cap(),
            "Internal node has too many keys: {} > {}",
            count,
            Self::cap()
        );

        // Validate keys are sorted
        unsafe {
            for i in 1..count {
                let prev_key = (*self.key_ptr((i - 1) as u32)).assume_init_ref();
                let curr_key = (*self.key_ptr(i as u32)).assume_init_ref();
                assert!(
                    prev_key < curr_key,
                    "Internal node keys not sorted: {:?} >= {:?}",
                    prev_key,
                    curr_key
                );
            }
        }
    }
}
