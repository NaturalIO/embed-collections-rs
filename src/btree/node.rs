use crate::CACHE_LINE_SIZE;
use alloc::alloc::{alloc, dealloc, handle_alloc_error};
use alloc::vec::Vec;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, needs_drop, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{NonNull, null_mut};

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
    fn is_leaf(&self) -> bool {
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
    pub(crate) fn header(&self) -> NonNull<NodeHeader> {
        self.header
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

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline]
    fn search<K>(&self, header_offset: usize, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
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
                    if is_equal {
                        if node.height() == 1 {
                            return node.get_child_as_leaf(idx);
                        } else {
                            cur = node.get_child_as_inter(idx);
                        }
                    } else {
                        // there must be a leaf for this
                        cur = node.get_child_as_inter(idx)
                    }
                }
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache(
        &self, cache: &mut Vec<InterNode<K, V>>, key: &K,
    ) -> LeafNode<K, V> {
        match &self {
            Node::Leaf(node) => return node.clone(),
            Node::Inter(node) => {
                let mut cur = node.clone();
                loop {
                    let (idx, is_equal) = cur.search(key);
                    if is_equal {
                        if node.height() == 1 {
                            return node.get_child_as_leaf(idx);
                        } else {
                            cache.push(node.clone());
                            cur = node.get_child_as_inter(idx);
                        }
                    } else {
                        // there must be a leaf for this
                        cur = node.get_child_as_inter(idx)
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
    fn search(&self, key: &K) -> (u32, bool)
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
    pub(crate) unsafe fn child_ptr(&self, idx: u32) -> *mut *mut NodeHeader {
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
        // Initialize leaf pointers
        let ptrs =
            unsafe { NodeHeader::get_field::<LeafPtrs>(base.header, AREA_SIZE) as *mut LeafPtrs };
        unsafe {
            (*ptrs).prev = null_mut();
            (*ptrs).next = null_mut();
        }
        Self { base, _phan: Default::default() }
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
        let base = self.header.as_ptr() as *mut u8;
        unsafe { base.add(AREA_SIZE) as *mut LeafPtrs }
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

    pub(crate) fn cap() -> usize {
        Self::LAYOUT.0
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
    fn test_leaf_node_alloc_and_dealloc() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            assert_eq!(leaf.height(), 0);
            assert_eq!(leaf.count(), 0);

            // Insert some values
            for i in 0..4 {
                let key_ptr = leaf.key_ptr(i as u32);
                let val_ptr = leaf.value_ptr(i as u32);
                (*key_ptr).write((i * 10) as i32);
                (*val_ptr).write((i * 100) as i32);
            }
            leaf.get_header_mut().count = 4;

            // Verify values
            for i in 0..4 {
                let key_ptr = leaf.key_ptr(i as u32);
                let val_ptr = leaf.value_ptr(i as u32);
                assert_eq!((*key_ptr).assume_init_ref(), &((i * 10) as i32));
                assert_eq!((*val_ptr).assume_init_ref(), &((i * 100) as i32));
            }

            leaf.dealloc();
        }
    }

    #[test]
    fn test_leaf_node_search() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();

            // Insert sorted keys: 10, 20, 30, 40
            let keys = [10i32, 20, 30, 40];
            for (i, &k) in keys.iter().enumerate() {
                let key_ptr = leaf.key_ptr(i as u32);
                let val_ptr = leaf.value_ptr(i as u32);
                (*key_ptr).write(k);
                (*val_ptr).write(k * 10);
            }
            leaf.get_header_mut().count = 4;

            // Test search - existing key
            let (idx, found) = leaf.search(&20);
            assert!(found);
            assert_eq!(idx, 1);

            // Test search - non-existing key (should return insertion point)
            let (idx, found) = leaf.search(&25);
            assert!(!found);
            assert_eq!(idx, 2);

            // Test search - key smaller than all
            let (idx, found) = leaf.search(&5);
            assert!(!found);
            assert_eq!(idx, 0);

            // Test search - key larger than all
            let (idx, found) = leaf.search(&50);
            assert!(!found);
            assert_eq!(idx, 4);

            leaf.dealloc();
        }
    }

    #[test]
    fn test_internal_node_alloc() {
        unsafe {
            let mut inter = InterNode::<i32, i32>::alloc(1);
            assert_eq!(inter.height(), 1);
            assert_eq!(inter.count(), 0);

            // Insert keys
            for i in 0..3 {
                let key_ptr = inter.key_ptr(i as u32);
                (*key_ptr).write((i * 10) as i32);
            }
            inter.get_header_mut().count = 3;

            // Set up child pointers (just null for test)
            for i in 0..=3 {
                let child_ptr = inter.child_ptr(i as u32);
                *child_ptr = core::ptr::null_mut();
            }

            inter.dealloc();
        }
    }

    #[test]
    fn test_internal_node_search() {
        unsafe {
            let mut inter = InterNode::<i32, i32>::alloc(1);

            // Insert sorted keys: 10, 20, 30
            let keys = [10i32, 20, 30];
            for (i, &k) in keys.iter().enumerate() {
                let key_ptr = inter.key_ptr(i as u32);
                (*key_ptr).write(k);
            }
            inter.get_header_mut().count = 3;

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
}
