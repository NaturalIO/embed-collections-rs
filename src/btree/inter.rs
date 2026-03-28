use super::leaf::*;
use super::node::*;
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, dealloc};
use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, needs_drop, size_of};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull, null_mut};

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
        let mut root = unsafe { Self::alloc(height) };
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
        let (idx, is_equal) = self.base.search::<K>(INTER_KEY_HEAD_SIZE, key);
        if is_equal { (idx + 1, true) } else { (idx, false) }
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
    pub fn get_child_as_leaf(&self, idx: u32) -> LeafNode<K, V> {
        unsafe {
            let child_ptr_ptr = self.child_ptr(idx);
            let child_ptr = *child_ptr_ptr;
            if child_ptr.is_null() {
                panic!("child is null");
            } else {
                LeafNode::<K, V>::from_header(NonNull::new_unchecked(child_ptr))
            }
        }
    }

    /// Get child at index as a Node
    #[inline(always)]
    pub fn get_child_as_inter(&self, idx: u32) -> InterNode<K, V> {
        unsafe {
            let child_ptr_ptr = self.child_ptr(idx);
            let child_ptr = *child_ptr_ptr;
            if child_ptr.is_null() {
                panic!("child is null");
            } else {
                InterNode::<K, V>::from_header(NonNull::new_unchecked(child_ptr))
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
                self.insert_no_split_with_idx(idx, key, child_ptr);

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
                new_node.insert_no_split_with_idx(insert_pos, key, child_ptr);

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

#[cfg(test)]
mod tests {
    use super::*;

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
