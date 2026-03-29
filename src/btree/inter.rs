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

    pub(crate) fn cap() -> u32 {
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
        let avail = Self::cap() - self.count();
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
                panic!("child is null");
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
    fn search_key(&self, key: &K) -> u32
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
        debug_assert!(self.count() < Self::cap());
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
        debug_assert!(start_idx + copy_count <= self.count() as u32);
        debug_assert!(right_node.count() + copy_count <= Self::cap());
        unsafe {
            // Append to tail of right_node
            let right_count = right_node.count();
            // Move keys using bulk copy
            let src_key = self.key_ptr(start_idx) as *mut K;
            println!(
                "copy right start_idx {start_idx} right_count {right_count}, copy {copy_count}"
            );
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
        debug_assert_eq!(self.count(), Self::cap());
        let idx = self.search_key(&key);
        let mut new_node = unsafe { InterNode::<K, V>::alloc(self.height()) };
        if idx == cap {
            println!("cap");
            // the right most position, new empty node
            new_node.set_left_ptr(child_ptr);
            return (new_node, key);
        }
        let split_idx = cap >> 1;
        unsafe {
            if idx == split_idx {
                println!("equal");
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
                println!("insert left split_idx {split_idx}");
                // Split point is to the right of insertion
                // Move right half (including split_idx) to new node
                let right_count = cap - split_idx - 1;
                if right_count > 0 {
                    self.copy_right(&mut new_node, split_idx + 1, right_count);
                }
                self.get_header_mut().count = split_idx;
                // Safety: update the count before inserting new key
                self.insert_no_split_with_idx(idx, key, child_ptr);
            } else {
                // Split point is to the left of insertion
                // Move right half (after split_idx) to new node, excluding split_idx
                if idx > split_idx + 1 {
                    self.copy_right(&mut new_node, split_idx + 1, idx - split_idx - 1);
                }
                new_node.insert_no_split_with_idx(idx, key, child_ptr);
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
        let count = self.count() as u32; // the count is equal to keys count, but value count should + 1
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

impl<K: fmt::Debug, V> fmt::Debug for InterNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let count = self.count();
        write!(f, "InterNode {{ height: {}, count: {}, keys: [", self.height(), count)?;
        for i in 0..count {
            unsafe {
                let key = (*self.key_ptr(i as u32)).assume_init_ref();
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}", key)?;
            }
        }
        write!(f, "], children: {} }}", count + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inter_node_search() {
        unsafe {
            let mut inter = InterNode::<usize, usize>::alloc(1);
            let cap = InterNode::<usize, usize>::cap();
            println!("InterNode<usize> cap {}", cap);

            inter.set_left_ptr(0 as *mut NodeHeader);
            for i in 1..(cap + 1) {
                inter.insert_no_split(i as usize, i as *mut NodeHeader);
            }
            assert_eq!(inter.count(), cap);
            // Test search - existing key
            for i in 1..(cap + 1) {
                let idx = inter.search_child(&(i as usize));
                assert_eq!(idx, i as u32);
            }
            // search left ptr
            let idx = inter.search_child(&0);
            assert_eq!(idx, 0);

            // Test search - key larger than all
            let idx = inter.search_child(&50);
            assert_eq!(idx, cap as u32);

            inter.dealloc();
        }
    }

    #[test]
    fn test_inter_split_insert_left() {
        let cap = InterNode::<i32, i32>::cap();
        println!("InterNode<i32> cap {}", cap);
        // TODO should test split_idx == count ?  cap = 2
        unsafe {
            // Test Case 2: Insert key before split_idx (should go to left node)
            let mut node = InterNode::<i32, i32>::alloc(1);
            // Fill the node to capacity with dummy pointers
            for i in 0..cap {
                node.insert_no_split(
                    (i * 10) as i32,
                    (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
                );
            }
            node.set_left_ptr(0x1000 as *mut NodeHeader);

            let split_idx = cap >> 1;
            let insert_key = (split_idx * 10 - 15) as i32; // Key before split_idx
            let insert_child = 0x5000 as *mut NodeHeader;
            let insert_idx = node.search_key(&insert_key);
            assert!(insert_idx < split_idx);
            println!("cap {cap} split_idx {split_idx}, insert_idx {insert_idx}");
            let (mut new_node, _promote_key) = node.insert_split(insert_key, insert_child);
            // Verify counts
            let left_count = node.count();
            let right_count = new_node.count();
            println!("left {left_count} right {right_count}");
            // although the keys will promote, the values are the same

            assert_eq!(left_count, split_idx + 1, "Left node should have split_idx keys");
            assert_eq!(
                right_count,
                cap - split_idx - 1,
                "Right node should have cap - split_idx keys"
            );
            assert_eq!(left_count + right_count + 2, cap + 2); // one more node, one more left ptr,
            // total value is unchanged

            // Verify the inserted key is in left node
            //            let in_left = (0..split_idx).any(|i| {
            //                let key = (*node.key_ptr(i)).assume_init_ref();
            //                *key == insert_key
            //            });
            //            assert!(in_left, "Key inserted before split_idx should be in left node");

            // Cleanup
            new_node.dealloc();
            node.dealloc();
            println!("Test Case 2 completed successfully");
        }
    }

    #[test]
    fn test_internal_node_split_at_promote() {
        // Insert key at split_idx position (will be promoted, not inserted)
        unsafe {
            let cap = InterNode::<i32, i32>::cap();

            println!("=== Test Internal Node Split Basic ===");
            println!("cap = {}", cap);

            let mut node = InterNode::<i32, i32>::alloc(1);

            // Fill the node to capacity with dummy pointers
            (*node.child_ptr(0)) = 0x1000 as *mut NodeHeader;
            for i in 0..cap {
                (*node.key_ptr(i)).write((i * 10) as i32);
                (*node.child_ptr(i + 1)) = (0x1000 + (i + 1) * 0x100) as *mut NodeHeader;
            }
            node.get_header_mut().count = cap;

            println!(
                "Before split: node.count = {}, node.ptr = {:?}",
                node.count(),
                node.get_ptr()
            );

            let split_idx = cap >> 1;
            let insert_key = (split_idx * 10 - 5) as i32; // Key between split_idx-1 and split_idx
            let insert_child = 0x5000 as *mut NodeHeader;

            println!(
                "split_idx = {}, insert_key = {}, insert_child = {:?}",
                split_idx, insert_key, insert_child
            );

            let (mut new_node, promote_key) = node.insert_split(insert_key, insert_child);

            println!(
                "After split: left count = {}, right count = {}, promote_key = {}",
                node.count(),
                new_node.count(),
                promote_key
            );
            println!("left ptr = {:?}, right ptr = {:?}", node.get_ptr(), new_node.get_ptr());

            // Verify counts
            let left_count = node.count() as u32;
            let right_count = new_node.count() as u32;

            println!("Asserting: left_count({}) == split_idx({})", left_count, split_idx);
            assert_eq!(left_count, split_idx, "Left node should have split_idx keys");
            assert_eq!(right_count, cap - split_idx, "Right node should have cap - split_idx keys");
            assert_eq!(
                left_count + right_count,
                cap,
                "Total keys should be cap when insert_key == promote_key"
            );
            assert_eq!(promote_key, insert_key, "Promoted key should be the inserted key");

            // Verify the inserted key is NOT in either node (it was promoted)
            let in_left = (0..split_idx).any(|i| {
                let key = (*node.key_ptr(i)).assume_init_ref();
                *key == insert_key
            });
            let in_right = (0..(cap - split_idx)).any(|i| {
                let key = (*new_node.key_ptr(i)).assume_init_ref();
                *key == insert_key
            });
            assert!(
                !in_left && !in_right,
                "Inserted key at split_idx should be promoted, not stored in nodes"
            );

            // Cleanup
            new_node.dealloc();
            node.dealloc();
            println!("Test Case 1 completed successfully");
        }
    }

    #[test]
    fn test_inter_split_insert_right() {
        let cap = InterNode::<i32, i32>::cap() as u32;
        // Test Case 3: Insert key after split_idx (should go to right node)
        unsafe {
            println!("\n--- Test Case 3: Insert after split_idx (key goes to right node) ---");
            let mut node = InterNode::<i32, i32>::alloc(1);

            // Fill the node to capacity with dummy pointers
            (*node.child_ptr(0)) = 0x1000 as *mut NodeHeader;
            for i in 0..cap {
                (*node.key_ptr(i)).write((i * 10) as i32);
                (*node.child_ptr(i + 1)) = (0x1000 + (i + 1) * 0x100) as *mut NodeHeader;
            }
            node.get_header_mut().count = cap;

            let split_idx = cap >> 1;
            let insert_key = (split_idx * 10 + 5) as i32; // Key after split_idx
            let insert_child = 0x5000 as *mut NodeHeader;

            let (mut new_node, _promote_key) = node.insert_split(insert_key, insert_child);

            // Verify counts
            let left_count = node.count() as u32;
            let right_count = new_node.count() as u32;

            assert_eq!(left_count, split_idx, "Left node should have split_idx keys");
            assert_eq!(right_count, cap - split_idx, "Right node should have cap - split_idx keys");
            assert_eq!(
                left_count + right_count,
                cap + 1,
                "Total keys should be cap + 1 when insert_key != promote_key"
            );

            // Verify the inserted key is in right node
            let in_right = (0..(cap - split_idx)).any(|i| {
                let key = (*new_node.key_ptr(i)).assume_init_ref();
                *key == insert_key
            });
            assert!(in_right, "Key inserted after split_idx should be in right node");

            // Cleanup
            new_node.dealloc();
            node.dealloc();
            println!("Test Case 3 completed successfully");
        }
    }
}
