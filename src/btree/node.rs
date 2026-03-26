use crate::CACHE_LINE_SIZE;
use alloc::alloc::{alloc, dealloc, handle_alloc_error};
use alloc::vec::Vec;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, size_of};
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
    height: u32,
    /// Count of items in the node
    count: u32,
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
struct NodeBase {
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
    unsafe fn dealloc(&self) {
        unsafe {
            dealloc(self.header.as_ptr() as *mut u8, Self::LAYOUT);
        }
    }

    #[inline(always)]
    fn get_header(&self) -> &NodeHeader {
        unsafe { self.header.as_ref() }
    }

    #[inline(always)]
    fn get_header_mut(&mut self) -> &mut NodeHeader {
        unsafe { self.header.as_mut() }
    }

    #[inline(always)]
    fn get_array<T>(&self, header_size: usize, delta: usize) -> &[T] {
        let header = self.get_header();
        let items_ptr = unsafe { NodeHeader::get_field::<T>(self.header, header_size) };
        unsafe { core::slice::from_raw_parts::<T>(items_ptr, header.count as usize + delta) }
    }

    /// Get pointer to key at index with given header offset
    #[inline(always)]
    unsafe fn item_ptr<T>(&self, start_offset: usize, idx: usize) -> *mut T {
        unsafe { NodeHeader::get_field::<T>(self.header, start_offset + idx * size_of::<T>) }
    }

    /// Check if this is a leaf node
    #[inline(always)]
    fn is_leaf(&self) -> bool {
        self.get_header().is_leaf()
    }

    /// Get count of items in the node
    #[inline(always)]
    fn count(&self) -> usize {
        self.get_header().count as usize
    }

    /// Get height of the node
    #[inline(always)]
    fn height(&self) -> u32 {
        self.get_header().height
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline]
    fn search<K>(header_offset: usize, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
        macro_rules! _search {
            ($start: expr, $end: expr) => {
                let mut idx = $start;
                if $start < $end {
                    let mut k = self.item_ptr::<K>($start);
                    loop {
                        if (*k) == key {
                            return (idx as u32, true);
                        } else if (*k) > key {
                            // insert to this pos, idx should move right
                            return (idx as u32, false);
                        }
                        idx += 1;
                        k = k.add(1);
                        if idx == $end {
                            break;
                        }
                    }
                    // NOTE: be aware to check idx == cap
                }
                return (idx as u32, false);
            };
        }

        let count = self.count();
        let first_line_bytes = CACHE_LINE_SIZE - header_offset;
        let first_line_limit = (first_line_bytes / size_of::<K>());
        if count > first_line_limit
            && key > (*self.item_ptr::<K>(header_offset, first_line_limit - 1))
        {
            _search!(first_line_limit, count);
        } else {
            _search!(0, count);
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
        let mut cur = self;
        match cur {
            Node::Leaf(node) => return Some(node.clone()),
            Node::Inter(node) => {
                let (idx, is_equal) = node.search(key);
                if is_equal {
                    if node.height() == 1 {
                        return node.get_child_as_leaf(idx);
                    } else {
                        cur = node.get_child_as_inter(idx);
                    }
                } else {
                    cur = node.get_child_as_inter(idx)
                }
            }
        }
    }

    #[inline]
    pub fn find_leaf_with_cache(
        &self, cache: &mut Vec<InterNode<K, V>>, key: &K,
    ) -> LeafNode<K, V> {
        let mut cur = self;
        match cur {
            Node::Leaf(node) => return Some(node.clone()),
            Node::Inter(node) => {
                let (idx, is_equal) = node.search(key);
                if is_equal {
                    if node.height() == 1 {
                        return node.get_child_as_leaf(idx);
                    } else {
                        cur = node.get_child_as_inter(idx);
                        cache.push(node.clone());
                    }
                } else {
                    cur = node.get_child_as_inter(idx)
                }
            }
        }
    }
}

/// Leaf node prev/next pointers
#[repr(C)]
struct LeafPtrs {
    prev: *mut NodeHeader,
    next: *mut NodeHeader,
}

/// Internal node wrapper - wraps Node and provides internal node-specific operations
#[derive(Clone)]
pub(crate) struct InterNode<K, V> {
    base: NodeBase,
    _phan: PhantomData<fn(&K, &V)>,
}

impl<K, V> Deref for InterNode<K, V> {
    type Target = Node<K, V>;

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
        let mut node = unsafe { Node::alloc(Self::LAYOUT[1]) };
        let header = node.get_header_mut();
        header.height = height; // Internal nodes have height > 0
        header.count = 0;
        Self(node)
    }

    #[inline(always)]
    pub unsafe fn dealloc(self) {
        unsafe {
            if needs_drop::<K>() {
                let count = self.count();
                for i in 0..count {
                    (*self.key_ptr(i)).assume_init_drop();
                }
            }
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT);
        }
    }

    #[inline(always)]
    fn get_keys(&self) -> &[K] {
        self.base.get_array::<K>(INTER_KEY_HEAD_SIZE, 0)
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    fn search(key: &K) -> (usize, bool)
    where
        K: Ord,
    {
        self.base.search::<K>(INTER_KEY_HEAD_SIZE)
    }

    /// Get pointer to key at index
    #[inline(always)]
    unsafe fn key_ptr(&self, idx: usize) -> *mut MaybeUninit<K> {
        self.base.item_ptr::<MaybeUninit<K>>(INTER_KEY_HEAD_SIZE, idx)
    }

    /// Get pointer to child at index
    #[inline(always)]
    unsafe fn child_ptr(&self, idx: usize) -> *mut MaybeUninit<*mut NodeHeader> {
        self.base.item_ptr::<MaybeUninit<*mut NodeHeader>>(AREA_SIZE, idx)
    }

    #[inline]
    fn get_child_as_leaf(&self) -> LeafNode<K, V> {
        let child_ptr = unsafe { &*self.child_ptr(idx) };
        if child_ptr.is_null() {
            panic!("child is null");
        } else {
            let base = NodeBase { header: NonNull::new_unchecked(child_ptr) };
            LeafNode::<K, V> { base: Node::Leaf(base), _phan: Default::default() }
        }
    }

    /// Get child at index as a Node
    #[inline(always)]
    fn get_child_as_inter(&self, idx: usize) -> InterNode<K, V> {
        let child_ptr = unsafe { &*self.child_ptr(idx) };
        if child_ptr.is_null() {
            panic!("child is null");
        } else {
            let base = NodeBase { header: NonNull::new_unchecked(child_ptr) };
            Self { base: Node::Inter(base), _phan: Default::default() }
        }
    }

    fn cap() -> usize {
        Self::LAYOUT[0]
    }
}

/// Leaf node wrapper - wraps Node and provides leaf-specific operations
#[derive(Clone)]
pub(crate) struct LeafNode<K, V> {
    base: NodeBase,
    _phan: PhantomData<fn(&K, &V)>,
}

impl<K, V> Deref for LeafNode<K, V> {
    type Target = Node<K, V>;

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
        let mut node = Node::alloc(Self::LAYOUT[1]);
        let header = node.get_header_mut();
        header.height = 0; // Leaf nodes have height 0
        header.count = 0;
        // Initialize leaf pointers
        let ptrs =
            unsafe { NodeHeader::get_field::<LeafPtrs>(node.header, AREA_SIZE) as *mut LeafPtrs };
        unsafe {
            (*ptrs).prev = null_mut();
            (*ptrs).next = null_mut();
        }
        Self { node, _phan: Default::default() }
    }

    #[inline(always)]
    pub unsafe fn dealloc(self) {
        let count = self.count();
        unsafe {
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
            dealloc(self.base.header.as_ptr() as *mut u8, Self::LAYOUT);
        }
    }

    #[inline(always)]
    fn get_keys(&self) -> &[K] {
        self.get_array::<K>(LEAF_HEAD_SIZE, 0)
    }

    #[inline(always)]
    fn get_values(&self) -> &[V] {
        self.get_array::<V>(AREA_SIZE + LEAF_HEAD_SIZE, 0)
    }

    /// Get pointer to key at index
    #[inline(always)]
    unsafe fn key_ptr(&self, idx: usize) -> *mut MaybeUninit<K> {
        self.base.item_ptr::<MaybeUninit<K>>(LEAF_HEAD_SIZE, idx)
    }

    /// Get pointer to value at index
    #[inline(always)]
    unsafe fn value_ptr(&self, idx: usize) -> *mut MaybeUninit<V> {
        self.base.item_ptr::<MaybeUninit<V>>(AREA_SIZE + LEAF_HEAD_SIZE, idx)
    }

    /// Get pointer to LeafPtrs
    #[inline(always)]
    unsafe fn brothers(&self) -> *mut LeafPtrs {
        let base = self.header.as_ptr() as *mut u8;
        base.add(AREA_SIZE) as *mut LeafPtrs
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search(key: &K) -> (usize, bool)
    where
        K: Ord,
    {
        self.base.search::<K>(LEAF_HEAD_SIZE)
    }

    fn cap() -> usize {
        Self::LAYOUT[0]
    }
}

#[cfg(test)]
mod tests {

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_fill_node() {
        assert_eq(LeafNode::<usize, usize>::cap(), 16);
        assert_eq(InterNode::<usize, usize>::cap(), 15);
    }
}
