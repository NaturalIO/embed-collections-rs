use crate::CACHE_LINE_SIZE;
use alloc::alloc::{alloc, dealloc, handle_alloc_error};
use alloc::vec::Vec;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, needs_drop, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull, null_mut};

/// Key area size: first 128 bytes (2 cache lines)
const AREA_SIZE: usize = 2 * CACHE_LINE_SIZE; // 128 bytes

/// Total node size: 4 cache lines (256 bytes on x86_64)
const NODE_SIZE: usize = 2 * AREA_SIZE; // 256 bytes

/// Header size at start of key area for internal nodes
const INTER_KEY_HEAD_SIZE: usize = 8;

/// Header size at start of value area for internal nodes
const INTER_PTR_HEAD_SIZE: usize = 0;

/// Header size at start of key area for leaf nodes
const LEAF_HEAD_SIZE: usize = 16; // 8B header + 8B padding

/*
The Layout:
- InterNode: CACHELINE( 8B NodeHeader | Keys | alignment ),  CACHELINE(Values)
- LeafNode: CACHELINE(8B NodeHeader | 8B padding | Keys | alignment), CACHELINE( 16B LeafPtrs, values )
*/

/// Node header (8 bytes at start of key area)
/// height: 0 = leaf node, >0 = internal node (height of subtree)
#[repr(C)]
pub(crate) struct NodeHeader {
    /// Height of the node (0 = leaf, >0 = internal)
    pub(crate) height: u32,
    /// Count of items in the node
    pub(crate) count: u32,
}

impl NodeHeader {
    #[inline]
    unsafe fn get_field<T>(p: NonNull<Self>, offset: usize) -> *mut T {
        unsafe { (p.as_ptr() as *const u8).add(offset) as *mut T }
    }

    /// Check if this is a leaf node (height == 0)
    #[inline(always)]
    pub(crate) fn is_leaf(&self) -> bool {
        self.height == 0
    }
}

/// Generic node wrapper
#[derive(Clone)]
pub(crate) struct NodeBase {
    header: NonNull<NodeHeader>,
}

impl NodeBase {
    #[inline(always)]
    fn alloc(layout: Layout) -> Self {
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
    pub(crate) fn get_header(&self) -> &NodeHeader {
        unsafe { self.header.as_ref() }
    }

    #[inline(always)]
    pub(crate) fn get_header_mut(&mut self) -> &mut NodeHeader {
        unsafe { self.header.as_mut() }
    }

    #[inline(always)]
    pub(crate) fn get_ptr(&self) -> *mut NodeHeader {
        self.header.as_ptr() as *mut NodeHeader
    }

    #[inline(always)]
    fn get_array<T>(&self, header_size: usize, delta: usize) -> &[T] {
        let header = self.get_header();
        let items_ptr = unsafe { NodeHeader::get_field::<T>(self.header, header_size) };
        unsafe { core::slice::from_raw_parts::<T>(items_ptr, header.count as usize + delta) }
    }

    /// Get pointer to key at index with given header offset
    #[inline(always)]
    unsafe fn item_ptr<T>(&self, start_offset: usize, idx: u32) -> *mut T {
        unsafe {
            NodeHeader::get_field::<T>(self.header, start_offset + idx as usize * size_of::<T>())
        }
    }

    /// Check if this is a leaf node
    #[inline(always)]
    fn is_leaf(&self) -> bool {
        self.get_header().is_leaf()
    }

    /// Get count of items in the node
    #[inline(always)]
    pub(crate) fn count(&self) -> usize {
        self.get_header().count as usize
    }

    /// Get height of the node
    #[inline(always)]
    pub(crate) fn height(&self) -> u32 {
        self.get_header().height
    }

    /// search the position to insert (need to move old items from idx to the right)
    /// returns the idx, is_equal
    #[inline]
    fn search<K>(&self, header_offset: usize, key: &K) -> (u32, bool)
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
            let first_line_limit = first_line_bytes / size_of::<K>();
            if count > first_line_limit
                && *key > (*self.item_ptr::<K>(header_offset, first_line_limit as u32 - 1))
            {
                _search!(first_line_limit, count);
            } else {
                _search!(0, count);
            }
        }
    }

    /// NOTE: it will require two calls to remove (k, v) pair, so the count is not decrease here
    #[inline]
    unsafe fn remove_slot<T>(&mut self, header_offset: usize, idx: u32, mut left: u32) -> T {
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
    unsafe fn insert<K, V>(
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
                    let (idx, is_equal) = cur.search(key);
                    let child_idx = if is_equal { idx + 1 } else { idx };
                    if cur.height() == 1 {
                        return cur.get_child_as_leaf(child_idx);
                    } else {
                        cur = cur.get_child_as_inter(child_idx);
                    }
                }
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache(
        &self, cache: &mut Vec<(InterNode<K, V>, u32)>, key: &K,
    ) -> LeafNode<K, V> {
        match &self {
            Node::Leaf(node) => return node.clone(),
            Node::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let (idx, is_equal) = cur.search(key);
                    let child_idx = if is_equal { idx + 1 } else { idx };
                    if cur.height() == 1 {
                        cache.push((cur.clone(), idx));
                        return cur.get_child_as_leaf(child_idx);
                    } else {
                        cache.push((cur.clone(), idx));
                        cur = cur.get_child_as_inter(child_idx);
                    }
                }
            }
        }
    }
}

/// Leaf node prev/next pointers
#[repr(C)]
pub(crate) struct LeafPtrs {
    pub(crate) prev: *mut NodeHeader,
    pub(crate) next: *mut NodeHeader,
}

/// Internal node wrapper - wraps Node and provides internal node-specific operations
pub(crate) struct InterNode<K, V> {
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
    const LAYOUT: (usize, Layout) = Self::cal_layout();

    /// return inter_key_cap, leaf_key_cap.
    /// where:
    /// - inter_key_cap + 1 inter_value_cap;
    /// - leaf_key_cap = leaf_value_cap;
    ///
    /// assert K, V can fit into the cacheline after devided by header.
    const fn cal_layout() -> (usize, Layout) {
        let key_size = size_of::<K>();
        let value_size = size_of::<V>();
        assert!(align_of::<MaybeUninit<K>>() <= 8);
        assert!(align_of::<MaybeUninit<V>>() <= 8);
        assert!(key_size <= CACHE_LINE_SIZE - 16);
        assert!(value_size <= CACHE_LINE_SIZE - 16);
        let mut inter_key_cap = (AREA_SIZE - INTER_KEY_HEAD_SIZE) / key_size;
        let inter_value_cap = (AREA_SIZE - INTER_PTR_HEAD_SIZE) / value_size;
        if inter_key_cap > inter_value_cap - 1 {
            inter_key_cap = inter_value_cap - 1;
        }
        match Layout::from_size_align(NODE_SIZE, NODE_SIZE) {
            Ok(l) => (inter_key_cap, l),
            Err(_) => panic!("invalid layout"),
        }
    }

    #[inline(always)]
    pub fn new_root(
        height: u32, promote_key: K, left_ptr: *mut NodeHeader, right_ptr: *mut NodeHeader,
    ) -> Self {
        let root = unsafe { Self::alloc(height) };
        root.set_left_ptr(left_ptr);
        root.insert_no_split_with_idx(0, promote_key, right_ptr);
        root
    }

    #[inline(always)]
    pub unsafe fn alloc(height: u32) -> Self {
        let mut base = NodeBase::alloc(Self::LAYOUT.1);
        let header = base.get_header_mut();
        header.height = height; // Internal nodes have height > 0
        header.count = 0;
        Self { base, _phan: Default::default() }
    }

    #[inline(always)]
    pub unsafe fn dealloc(&mut self) {
        unsafe {
            if needs_drop::<K>() {
                let count = self.count();
                for i in 0..count as u32 {
                    (*self.key_ptr(i)).assume_init_drop();
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT.1);
        }
    }

    #[inline(always)]
    fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(INTER_KEY_HEAD_SIZE, 0)
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub(crate) fn search(&self, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
        self.base.search::<K>(INTER_KEY_HEAD_SIZE, key)
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
    fn get_child_as_leaf(&self, idx: u32) -> LeafNode<K, V> {
        unsafe {
            let child_ptr_ptr = self.child_ptr(idx);
            let child_ptr = *child_ptr_ptr;
            if child_ptr.is_null() {
                panic!("child is null");
            } else {
                let base = NodeBase { header: NonNull::new_unchecked(child_ptr) };
                LeafNode::<K, V> { base, _phan: Default::default() }
            }
        }
    }

    /// Get child at index as a Node
    #[inline(always)]
    fn get_child_as_inter(&self, idx: u32) -> InterNode<K, V> {
        unsafe {
            let child_ptr_ptr = self.child_ptr(idx);
            let child_ptr = *child_ptr_ptr;
            if child_ptr.is_null() {
                panic!("child is null");
            } else {
                let base = NodeBase { header: NonNull::new_unchecked(child_ptr) };
                Self { base, _phan: Default::default() }
            }
        }
    }

    pub(crate) fn cap() -> usize {
        Self::LAYOUT.0
    }

    /// Create InterNode from header pointer
    #[inline(always)]
    pub(crate) unsafe fn from_header(header: NonNull<NodeHeader>) -> Self {
        Self { base: NodeBase { header }, _phan: Default::default() }
    }

    #[inline(always)]
    pub(crate) fn set_left_ptr(&mut self, child_ptr: *mut NodeHeader) {
        unsafe {
            let p = self.child_ptr(0);
            p.write(child_ptr)
        }
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline]
    pub fn insert_no_split_with_idx(&mut self, idx: u32, key: K, ptr: *mut NodeHeader) {
        debug_assert!(self.count() < Self::cap());
        let _ = unsafe {
            self.base.insert::<K, *mut NodeHeader>(
                INTER_KEY_HEAD_SIZE,
                AREA_SIZE + size_of::<*mut NodeHeader>(), // the left ptr should not be touch
                idx,
                key,
                ptr,
            )
        };
    }

    /// If append == true, move the items to the tail,
    /// If append == false, prepend to items to the front.
    pub fn move_right(
        &mut self, right_node: &mut Self, start_idx: u32, move_count: u32, append: bool,
    ) {
        debug_assert!(start_idx + move_count <= self.count() as u32);
        debug_assert!(right_node.count() + move_count as usize <= Self::cap());

        unsafe {
            if append {
                // Append to tail of right_node
                let right_count = right_node.count() as u32;

                // Move keys using bulk copy
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(right_count);
                ptr::copy_nonoverlapping(src_key, dst_key, move_count as usize);

                // Move children using bulk copy (need move_count + 1 children)
                let src_child = self.child_ptr(start_idx);
                let dst_child = right_node.child_ptr(right_count);
                ptr::copy_nonoverlapping(src_child, dst_child, (move_count + 1) as usize);
            } else {
                // Prepend to head of right_node
                let right_count = right_node.count() as u32;

                // Shift existing elements in right_node to make space
                if right_count > 0 {
                    let src_key = right_node.key_ptr(0);
                    let dst_key = right_node.key_ptr(move_count);
                    ptr::copy(src_key, dst_key, right_count as usize);

                    let src_child = right_node.child_ptr(0);
                    let dst_child = right_node.child_ptr(move_count);
                    ptr::copy(src_child, dst_child, (right_count + 1) as usize);
                }

                // Move new elements to the front
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(0);
                ptr::copy_nonoverlapping(src_key, dst_key, move_count as usize);

                let src_child = self.child_ptr(start_idx);
                let dst_child = right_node.child_ptr(0);
                ptr::copy_nonoverlapping(src_child, dst_child, (move_count + 1) as usize);
            }

            // Update counts
            self.get_header_mut().count -= move_count;
            right_node.get_header_mut().count += move_count;
        }
    }

    /// Split internal node when inserting at idx with key and child pointer
    /// Returns (new_right_node, promote_key)
    pub fn split(&mut self, idx: u32, key: K, child_ptr: *mut NodeHeader) -> (Self, K) {
        let count = self.count() as u32;
        let split_idx = count >> 1;
        let mut new_node = unsafe { InterNode::<K, V>::alloc(self.height()) };

        unsafe {
            // Determine which side the insertion should go
            let insert_left = idx <= split_idx;

            if insert_left {
                // Split point is to the right of insertion
                // Move right half (including split_idx) to new node
                let right_count = count - split_idx;
                self.move_right(&mut new_node, split_idx, right_count, true);

                // Extract the promote key (first key of new_node)
                let promote_key_ptr = new_node.key_ptr(0);
                let promote_key = (*promote_key_ptr).assume_init_read();

                // Remove the promote key from new_node (shift left keys and children)
                for i in 0..(right_count - 1) {
                    let src_key = new_node.key_ptr(i + 1);
                    let dst_key = new_node.key_ptr(i);
                    let k = (*src_key).assume_init_read();
                    (*dst_key).write(k);
                }
                // Shift children left - remove the first child which corresponds to the promoted key
                for i in 0..right_count {
                    let src_child = new_node.child_ptr(i + 1);
                    let dst_child = new_node.child_ptr(i);
                    let child = (*src_child).clone();
                    (*dst_child) = child;
                }
                new_node.get_header_mut().count -= 1;

                // Insert the new key and child into left node
                self.insert_no_split(idx, key, child_ptr);

                (new_node, promote_key)
            } else {
                // Split point is to the left of insertion
                // Move right half (after split_idx) to new node, excluding split_idx
                let right_count = count - split_idx - 1;
                if right_count > 0 {
                    self.move_right(&mut new_node, split_idx + 1, right_count, true);
                }

                // Extract the promote key (key at split_idx)
                let promote_key_ptr = self.key_ptr(split_idx);
                let promote_key = (*promote_key_ptr).assume_init_read();

                // Remove the promote key from left node (shift left keys and children)
                for i in split_idx..(count - 1) {
                    let src_key = self.key_ptr(i + 1);
                    let dst_key = self.key_ptr(i);
                    let k = (*src_key).assume_init_read();
                    (*dst_key).write(k);
                }
                // Shift children left - remove the child after the promoted key
                for i in (split_idx + 1)..count {
                    let src_child = self.child_ptr(i + 1);
                    let dst_child = self.child_ptr(i);
                    let child = (*src_child).clone();
                    (*dst_child) = child;
                }
                self.get_header_mut().count -= 1;

                // Insert the new key and child into right node
                let insert_pos = idx - split_idx - 1;
                new_node.insert_no_split(insert_pos, key, child_ptr);

                (new_node, promote_key)
            }
        }
    }

    #[inline]
    pub fn remove_child(&mut self, key: &K)
    where
        K: Ord,
    {
        let (idx, is_equal) = self.search(key);
        let count = self.count() as u32; // the count is equal to keys count, but value count should + 1
        if !is_equal {
            if idx != 0 {
                panic!("imposible remove a child with key not in the node");
            }
            // remove the left child
            unsafe {
                self.base.remove_slot::<*mut NodeHeader>(AREA_SIZE + INTER_PTR_HEAD_SIZE, 0, count)
            };
        } else {
            unsafe {
                let _key = self.base.remove_slot::<K>(INTER_KEY_HEAD_SIZE, idx, count);
                // let the key drop
                self.base.remove_slot::<*mut NodeHeader>(
                    AREA_SIZE + INTER_PTR_HEAD_SIZE,
                    idx + 1,
                    count,
                );
            }
        }
        self.get_header_mut().count = count - 1;
    }
}

/// Leaf node wrapper - wraps Node and provides leaf-specific operations
pub(crate) struct LeafNode<K, V> {
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

impl<K, V> LeafNode<K, V> {
    /// (inter_key_cap, leaf_key_cap)
    const LAYOUT: (usize, Layout) = Self::cal_layout();

    /// return inter_key_cap, leaf_key_cap.
    /// where:
    /// - inter_key_cap + 1 inter_value_cap;
    /// - leaf_key_cap = leaf_value_cap;
    ///
    /// assert K, V can fit into the cacheline after devided by header.
    const fn cal_layout() -> (usize, Layout) {
        let key_size = size_of::<K>();
        let value_size = size_of::<V>();
        assert!(align_of::<MaybeUninit<K>>() <= 8);
        assert!(align_of::<MaybeUninit<V>>() <= 8);
        assert!(key_size <= CACHE_LINE_SIZE - 16);
        assert!(value_size <= CACHE_LINE_SIZE - 16);
        let mut leaf_key_cap = (AREA_SIZE - LEAF_HEAD_SIZE) / key_size;
        let leaf_value_cap = (AREA_SIZE - LEAF_HEAD_SIZE) / value_size;
        if leaf_key_cap > leaf_value_cap {
            leaf_key_cap = leaf_value_cap;
        }
        match Layout::from_size_align(NODE_SIZE, NODE_SIZE) {
            Ok(l) => (leaf_key_cap, l),
            Err(_) => panic!("invalid layout"),
        }
    }

    #[inline(always)]
    pub unsafe fn alloc() -> Self {
        let mut base = NodeBase::alloc(Self::LAYOUT.1);
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
    pub unsafe fn dealloc(&mut self) {
        let count = self.count();
        unsafe {
            if needs_drop::<K>() {
                for i in 0..count as u32 {
                    (*self.key_ptr(i)).assume_init_drop();
                }
            }
            if needs_drop::<V>() {
                for i in 0..count as u32 {
                    (*self.value_ptr(i)).assume_init_drop();
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT.1);
        }
    }

    #[inline(always)]
    pub fn is_full(&self) -> Result<(), u32> {
        let avail = Self::cap() - self.count();
        if avail == 0 { Ok(()) } else { Err(avail as u32) }
    }

    #[inline(always)]
    fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(LEAF_HEAD_SIZE, 0)
    }

    #[inline(always)]
    fn get_values(&self) -> &[V] {
        self.base.get_array::<V>(AREA_SIZE + LEAF_HEAD_SIZE, 0)
    }

    /// Get pointer to key at index
    #[inline(always)]
    pub(crate) unsafe fn key_ptr(&self, idx: u32) -> *mut MaybeUninit<K> {
        unsafe { self.base.item_ptr::<MaybeUninit<K>>(LEAF_HEAD_SIZE, idx) }
    }

    /// Get pointer to value at index
    #[inline(always)]
    pub(crate) unsafe fn value_ptr(&self, idx: u32) -> *mut MaybeUninit<V> {
        unsafe { self.base.item_ptr::<MaybeUninit<V>>(AREA_SIZE + LEAF_HEAD_SIZE, idx) }
    }

    /// Get pointer to LeafPtrs
    #[inline(always)]
    pub(crate) unsafe fn brothers(&self) -> *mut LeafPtrs {
        unsafe { NodeHeader::get_field::<LeafPtrs>(self.header, AREA_SIZE) }
    }

    #[inline(always)]
    pub(crate) fn get_left_node(&self) -> Option<Self> {
        unsafe {
            let p = (*self.brothers()).prev;
            if p.is_null() {
                return None;
            }
            Some(Self::from_header(NonNull::new_unchecked(p)))
        }
    }

    #[inline(always)]
    pub(crate) fn get_right_node(&self) -> Option<Self> {
        unsafe {
            let p = (*self.brothers()).next;
            if p.is_null() {
                return None;
            }
            Some(Self::from_header(NonNull::new_unchecked(p)))
        }
    }

    /// Create LeafNode from header pointer
    #[inline(always)]
    pub(crate) unsafe fn from_header(header: NonNull<NodeHeader>) -> Self {
        Self { base: NodeBase { header }, _phan: Default::default() }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search(&self, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
        self.base.search::<K>(LEAF_HEAD_SIZE, key)
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline]
    pub fn insert_no_split_with_idx(&mut self, idx: u32, key: K, value: V) -> *mut V {
        debug_assert!(self.count() < Self::cap());
        unsafe {
            self.base.insert::<K, V>(LEAF_HEAD_SIZE, AREA_SIZE + LEAF_HEAD_SIZE, idx, key, value)
        }
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline]
    pub fn insert_no_split(&mut self, key: K, value: V) -> *mut V
    where
        K: Ord,
    {
        debug_assert!(self.count() < Self::cap());
        let (idx, is_equal) = self.search(&key);
        debug_assert!(!is_equal);
        unsafe {
            self.base.insert::<K, V>(LEAF_HEAD_SIZE, AREA_SIZE + LEAF_HEAD_SIZE, idx, key, value)
        }
    }

    #[inline]
    pub fn remove_no_borrow(&mut self, idx: u32) -> (K, V) {
        let left = self.count() as u32 - 1;
        unsafe {
            let key = self.base.remove_slot::<K>(LEAF_HEAD_SIZE, idx, left);
            let value = self.base.remove_slot::<V>(AREA_SIZE + LEAF_HEAD_SIZE, idx, left);
            self.get_header_mut().count = left;
            (key, value)
        }
    }

    #[inline]
    pub(crate) fn cap() -> usize {
        Self::LAYOUT.0
    }

    /// move items to the tail of left_node
    pub fn move_left(&mut self, left_node: &mut Self, start_idx: u32, move_count: u32) {
        debug_assert!(start_idx + move_count <= self.count() as u32);
        debug_assert!(left_node.count() + move_count as usize <= Self::cap());

        unsafe {
            let left_count = left_node.count() as u32;

            // Move keys using bulk copy
            let src_key = self.key_ptr(start_idx);
            let dst_key = left_node.key_ptr(left_count);
            ptr::copy_nonoverlapping(src_key, dst_key, move_count as usize);

            // Move values using bulk copy
            let src_val = self.value_ptr(start_idx);
            let dst_val = left_node.value_ptr(left_count);
            ptr::copy_nonoverlapping(src_val, dst_val, move_count as usize);

            // Update counts
            self.get_header_mut().count -= move_count;
            left_node.get_header_mut().count += move_count;
        }
    }

    /// If append == true, move the items to the tail,
    /// If append == false, prepend to items to the front.
    pub fn move_right(
        &mut self, right_node: &mut Self, start_idx: u32, move_count: u32, append: bool,
    ) {
        debug_assert!(start_idx + move_count <= self.count() as u32);
        debug_assert!(right_node.count() + move_count as usize <= Self::cap());

        unsafe {
            if append {
                // Append to tail of right_node
                let right_count = right_node.count() as u32;

                // Move keys using bulk copy
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(right_count);
                ptr::copy_nonoverlapping(src_key, dst_key, move_count as usize);

                // Move values using bulk copy
                let src_val = self.value_ptr(start_idx);
                let dst_val = right_node.value_ptr(right_count);
                ptr::copy_nonoverlapping(src_val, dst_val, move_count as usize);
            } else {
                // Prepend to head of right_node
                let right_count = right_node.count() as u32;

                // Shift existing elements in right_node to make space
                if right_count > 0 {
                    let src_key = right_node.key_ptr(0);
                    let dst_key = right_node.key_ptr(move_count);
                    ptr::copy(src_key, dst_key, right_count as usize);

                    let src_val = right_node.value_ptr(0);
                    let dst_val = right_node.value_ptr(move_count);
                    ptr::copy(src_val, dst_val, right_count as usize);
                }

                // Move new elements to the front
                let src_key = self.key_ptr(start_idx);
                let dst_key = right_node.key_ptr(0);
                ptr::copy_nonoverlapping(src_key, dst_key, move_count as usize);

                let src_val = self.value_ptr(start_idx);
                let dst_val = right_node.value_ptr(0);
                ptr::copy_nonoverlapping(src_val, dst_val, move_count as usize);
            }

            // Update counts
            self.get_header_mut().count -= move_count;
            right_node.get_header_mut().count += move_count;
        }
    }

    pub fn insert_with_split(&mut self, idx: u32, key: K, value: V) -> (Self, *mut V) {
        let mut new_leaf = unsafe { LeafNode::<K, V>::alloc() };
        let count = self.count() as u32;
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
                self.move_right(&mut new_leaf, split_idx, total_copy, true);
                let ptr_v = self.insert_no_split_with_idx(idx, key, value);
                return (new_leaf, ptr_v);
            } else {
                debug_assert!(idx > split_idx);
                let first_copy = idx - split_idx;
                self.move_right(&mut new_leaf, split_idx, first_copy, true);
                let ptr_v = new_leaf.insert_no_split_with_idx(first_copy, key, value);
                if total_copy > first_copy {
                    self.move_right(
                        &mut new_leaf,
                        split_idx + first_copy,
                        total_copy - first_copy,
                        true,
                    );
                }
                return (new_leaf, ptr_v);
            }
        } else {
            let ptr_v = new_leaf.insert_no_split_with_idx(0, key, value);
            (new_leaf, ptr_v)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_node_capacity() {
        // On x86_64 with 64-byte cache line:
        // Leaf: (128 - 16) / 8 = 14 keys/values, but limited by smaller of key/value space
        // Actually should be (128-16)/8 = 14 for both keys and values
        let leaf_cap = LeafNode::<i64, i64>::cap();
        let inter_cap = InterNode::<i64, i64>::cap();

        // Leaf can hold more because keys and values share the same space
        assert!(leaf_cap >= 2, "Leaf should hold at least 2 items");
        // Internal: n keys, n+1 children
        assert!(inter_cap >= 2, "Internal node should hold at least 2 keys");
    }

    #[test]
    fn test_leaf_node_search() {
        unsafe {
            let mut leaf = LeafNode::<usize, usize>::alloc();
            let cap = LeafNode::<usize, usize>::cap();
            // Insert sorted keys: 10, 20, 30, 40
            for k in 10..(cap + 10) {
                leaf.insert_no_split(k * 2, k * 2);
            }
            assert_eq!(leaf.count(), cap);
            // Test search - existing key
            for k in 10..(cap + 10) {
                let (idx, found) = leaf.search(&(k * 2));
                assert!(found);
                assert_eq!(idx, (k - 10) as u32);
            }
            // Test search - key smaller than all
            let (idx, found) = leaf.search(&0);
            assert!(!found);
            assert_eq!(idx, 0);

            // non-existing key (should return insertion point)
            let (idx, found) = leaf.search(&21);
            assert!(!found);
            assert_eq!(idx, 1);

            // larger than max key
            let (idx, found) = leaf.search(&((cap + 11) * 2));
            assert!(!found);
            assert_eq!(idx as usize, cap);

            leaf.dealloc();
        }
    }

    #[test]
    fn test_internal_node_search() {
        unsafe {
            let mut inter = InterNode::<usize, usize>::alloc(1);
            let cap = InterNode::<usize, usize>::cap();

            for i in 1..(cap + 1) {
                inter.insert_no_split(i, i as *mut NodeHeader);
            }
            assert_eq!(inter.count(), cap);
            for i in 1..(cap + 1) {
                let (idx, found) = inter.search(&i);
                assert!(found);
                assert_eq!(idx, (i - 1) as u)
            }

            // Test search - existing key
            let (idx, found) = inter.search(&20);
            assert!(found);
            assert_eq!(idx, 1);

            // Test search - non-existing key
            // For key=15, should go to child 1 (between 10 and 20)
            let (idx, found) = inter.search(&15);
            assert!(!found);
            assert_eq!(idx, 1);

            // Test search - key smaller than all
            let (idx, found) = inter.search(&5);
            assert!(!found);
            assert_eq!(idx, 0);

            // Test search - key larger than all
            let (idx, found) = inter.search(&50);
            assert!(!found);
            assert_eq!(idx, 3);

            inter.dealloc();
        }
    }

    #[test]
    fn test_leaf_node_linked_list() {
        unsafe {
            let mut leaf1 = LeafNode::<i32, i32>::alloc();
            let mut leaf2 = LeafNode::<i32, i32>::alloc();

            // Link leaf1 -> leaf2
            let ptrs1 = leaf1.brothers();
            let ptrs2 = leaf2.brothers();

            (*ptrs1).next = leaf2.header.as_ptr();
            (*ptrs2).prev = leaf1.header.as_ptr();

            // Verify links
            assert_eq!((*ptrs1).next, leaf2.header.as_ptr());
            assert_eq!((*ptrs2).prev, leaf1.header.as_ptr());
            assert!((*ptrs1).prev.is_null());
            assert!((*ptrs2).next.is_null());

            leaf1.dealloc();
            leaf2.dealloc();
        }
    }

    #[test]
    fn test_leaf_node_split() {
        unsafe {
            // Create a leaf node and fill it to capacity
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let cap = LeafNode::<i32, i32>::cap();

            // Fill the leaf with keys 0..cap
            for i in 0..cap {
                let key_ptr = leaf.key_ptr(i as u32);
                let val_ptr = leaf.value_ptr(i as u32);
                (*key_ptr).write(i as i32);
                (*val_ptr).write((i * 10) as i32);
            }
            leaf.get_header_mut().count = cap as u32;

            // Verify the leaf is full
            assert!(leaf.is_full().is_ok());
            assert_eq!(leaf.count(), cap);

            // Test 1: Insert at split_idx (new key should go to left node)
            let split_idx = (cap >> 1) as u32;
            let old_key_at_split = (*leaf.key_ptr(split_idx)).assume_init_ref().clone();
            let new_key = old_key_at_split - 1; // New key is smaller than old key at split_idx
            let new_value = new_key * 10;

            let (mut new_leaf, _ptr_v) = leaf.insert_with_split(split_idx, new_key, new_value);

            // Verify the split - new key should be in left node at split_idx
            let left_count = leaf.count();
            let right_count = new_leaf.count();

            assert!(left_count > 0);
            assert!(right_count > 0);
            assert_eq!(left_count + right_count, cap + 1);

            // Verify new key is in left node at split_idx
            let found_key = (*leaf.key_ptr(split_idx)).assume_init_ref();
            let found_value = (*leaf.value_ptr(split_idx)).assume_init_ref();
            assert_eq!(*found_key, new_key);
            assert_eq!(*found_value, new_value);

            // Verify old key at split_idx was moved to right node
            let old_key_in_right = (*new_leaf.key_ptr(0)).assume_init_ref();
            assert_eq!(*old_key_in_right, old_key_at_split);

            // Verify sibling pointers
            assert_eq!((*leaf.brothers()).next, new_leaf.get_ptr());
            assert_eq!((*new_leaf.brothers()).prev, leaf.get_ptr());
            assert!((*leaf.brothers()).prev.is_null());
            assert!((*new_leaf.brothers()).next.is_null());

            // Cleanup
            leaf.dealloc();
            new_leaf.dealloc();
        }
    }

    #[test]
    fn test_leaf_node_split_at_split_idx_with_search() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let cap = LeafNode::<i32, i32>::cap();

            // Fill with keys 0, 2, 4, 6, ... (even numbers)
            for i in 0..cap {
                let key_ptr = leaf.key_ptr(i as u32);
                let val_ptr = leaf.value_ptr(i as u32);
                (*key_ptr).write((i * 2) as i32);
                (*val_ptr).write((i * 20) as i32);
            }
            leaf.get_header_mut().count = cap as u32;

            let split_idx = (cap >> 1) as u32;
            let old_key_at_split = (*leaf.key_ptr(split_idx)).assume_init_ref().clone();

            // Insert an odd key that should be placed at split_idx
            let new_key = old_key_at_split - 1;
            let (search_idx, is_equal) = leaf.search(&new_key);

            // Verify search returns correct position
            assert!(!is_equal);
            assert_eq!(search_idx, split_idx);

            // Now perform the split
            let (mut new_leaf, _ptr_v) = leaf.insert_with_split(search_idx, new_key, new_key * 10);

            // Verify new key is at split_idx in left node
            let found_key = (*leaf.key_ptr(split_idx)).assume_init_ref();
            assert_eq!(*found_key, new_key);

            // Cleanup
            leaf.dealloc();
            new_leaf.dealloc();
        }
    }

    #[test]

    fn test_internal_node_split_basic() {
        unsafe {
            // Create an internal node with just a few items

            let mut node = InterNode::<i32, i32>::alloc(1);

            // Add 3 keys and 4 children (node is not full)

            (*node.key_ptr(0)).write(10);

            (*node.key_ptr(1)).write(20);

            (*node.key_ptr(2)).write(30);

            (*node.child_ptr(0)) = 100 as *mut NodeHeader;

            (*node.child_ptr(1)) = 200 as *mut NodeHeader;

            (*node.child_ptr(2)) = 300 as *mut NodeHeader;

            (*node.child_ptr(3)) = 400 as *mut NodeHeader;

            node.get_header_mut().count = 3;

            // Split at middle (idx = 1)

            let new_key = 25;

            let new_child = 250 as *mut NodeHeader;

            let (mut new_node, promote_key) = node.split(1, new_key, new_child);

            // Just verify no crash and counts are reasonable

            assert!(node.count() > 0);

            assert!(new_node.count() > 0);

            // Cleanup

            node.dealloc();

            new_node.dealloc();
        }
    }
}
