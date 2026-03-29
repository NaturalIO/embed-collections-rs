use super::node::*;
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, dealloc};
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
            Ok(l) => (leaf_key_cap as u32, l),
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
            Some(Self::from_header(NonNull::new_unchecked(p)))
        }
    }

    #[inline(always)]
    pub fn get_right_node(&self) -> Option<Self> {
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
    pub unsafe fn from_header(header: NonNull<NodeHeader>) -> Self {
        unsafe { debug_assert!(header.as_ref().is_leaf()) };
        Self { base: NodeBase { header }, _phan: Default::default() }
    }

    /// search the position to insert
    /// returns the idx, is_equal
    #[inline(always)]
    pub fn search(&self, key: &K) -> (u32, bool)
    where
        K: Ord,
    {
        self.base._search::<K>(LEAF_HEAD_SIZE, key)
    }

    /// Insert key-value at index (assuming there is space)
    /// Uses copy_within pattern for efficient shifting
    #[inline]
    pub fn insert_no_split_with_idx(&mut self, idx: u32, key: K, value: V) -> *mut V {
        debug_assert!(self.count() < Self::cap());
        unsafe {
            self.base._insert::<K, V>(LEAF_HEAD_SIZE, AREA_SIZE + LEAF_HEAD_SIZE, idx, key, value)
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
            self.base._insert::<K, V>(LEAF_HEAD_SIZE, AREA_SIZE + LEAF_HEAD_SIZE, idx, key, value)
        }
    }

    #[inline]
    pub fn remove_no_borrow(&mut self, idx: u32) -> (K, V) {
        let left = self.count() as u32 - 1;
        unsafe {
            let key = self.base._remove_slot::<K>(LEAF_HEAD_SIZE, idx, left);
            let value = self.base._remove_slot::<V>(AREA_SIZE + LEAF_HEAD_SIZE, idx, left);
            self.get_header_mut().count = left;
            (key, value)
        }
    }

    #[inline]
    pub fn cap() -> u32 {
        Self::LAYOUT.0
    }

    /// move items to the tail of left_node
    pub fn move_left(&mut self, left_node: &mut Self, start_idx: u32, move_count: u32) {
        debug_assert!(start_idx + move_count <= self.count());
        debug_assert!(left_node.count() + move_count <= Self::cap());

        unsafe {
            let left_count = left_node.count();

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
    #[inline(always)]
    pub fn move_right<const APPEND: bool>(
        &mut self, right_node: &mut Self, start_idx: u32, move_count: u32,
    ) {
        self.copy_right::<APPEND>(right_node, start_idx, move_count);
        self.get_header_mut().count -= move_count;
    }

    /// If append == true, move the items to the tail,
    /// If append == false, prepend to items to the front.
    ///
    /// # Safety
    ///
    /// It does not change the count of current node
    #[inline]
    pub fn copy_right<const APPEND: bool>(
        &mut self, right_node: &mut Self, start_idx: u32, copy_count: u32,
    ) {
        debug_assert!(start_idx + copy_count <= self.count());
        debug_assert!(right_node.count() + copy_count <= Self::cap());
        unsafe {
            if APPEND {
                // Append to tail of right_node
                let right_count = right_node.count();

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
                let right_count = right_node.count() as u32;

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
                self.move_right::<true>(&mut new_leaf, split_idx, total_copy);
                let ptr_v = self.insert_no_split_with_idx(idx, key, value);
                return (new_leaf, ptr_v);
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
                return (new_leaf, ptr_v);
            }
        } else {
            println!("leaf insert_with_split  right");
            let ptr_v = new_leaf.insert_no_split_with_idx(0, key, value);
            (new_leaf, ptr_v)
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for LeafNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let count = self.count();
        write!(f, "LeafNode {{ count: {}, keys: [", count)?;
        for i in 0..count {
            unsafe {
                let key = (*self.key_ptr(i as u32)).assume_init_ref();
                let val = (*self.value_ptr(i as u32)).assume_init_ref();
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}: {:?}", key, val)?;
            }
        }
        write!(f, "] }}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leaf_node_search() {
        unsafe {
            let mut leaf = LeafNode::<usize, usize>::alloc();
            let cap = LeafNode::<usize, usize>::cap() as usize;
            // Insert sorted keys: 10, 20, 30, 40
            for k in 10..(cap + 10) {
                leaf.insert_no_split(k * 2, k * 2);
            }
            assert_eq!(leaf.count(), cap as u32);
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

    /// Test leaf node split when inserting key at split_idx (new key < old key at split_idx)
    #[test]
    fn test_leaf_node_split_insert_at_split_idx_left() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let cap = LeafNode::<i32, i32>::cap();

            // Fill the leaf with keys 0..cap
            for i in 0..cap {
                // println!("insert {} {}", i, i*10);
                leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
            }

            // Insert key smaller than the key at split_idx
            let split_idx = (cap >> 1) as u32;
            let new_key = split_idx * 2 - 2 - 2 - 1; // odd key
            let new_value = new_key * 10;
            let (insert_idx, _is_equal) = leaf.search(&(new_key as i32));
            assert_eq!(insert_idx, split_idx - 2);
            assert!(!_is_equal);
            println!(
                "cap {cap} insert_idx {insert_idx} insert ({new_key}, {new_value}) split_idx {split_idx}"
            );

            let (mut new_leaf, _ptr_v) =
                leaf.insert_with_split(insert_idx, new_key as i32, new_value as i32);

            // Verify the split
            let left_count = leaf.count();
            let right_count = new_leaf.count();

            assert_eq!(left_count, split_idx + 1, "Left node should have keys");
            assert_eq!(left_count, insert_idx + 3, "Left node should have keys");
            assert_eq!(right_count, cap - split_idx, "Right node should have keys");
            assert_eq!(left_count + right_count, cap + 1, "Total keys should be cap + 1");

            for i in 0..insert_idx {
                assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32 * 2);
                assert_eq!((*leaf.value_ptr(i)).assume_init_read(), (i as i32) * 10);
            }
            // New key should be at split_idx in left node
            let found_key = (*leaf.key_ptr(insert_idx)).assume_init_ref();
            let found_value = (*leaf.value_ptr(insert_idx)).assume_init_ref();
            assert_eq!(*found_key, new_key as i32, "New key should be at split_idx in left node");
            assert_eq!(
                *found_value, new_value as i32,
                "New value should be at split_idx in left node"
            );

            assert_eq!((*leaf.key_ptr(insert_idx + 1)).assume_init_read(), insert_idx as i32 * 2);
            assert_eq!(
                (*leaf.value_ptr(insert_idx + 1)).assume_init_read(),
                insert_idx as i32 * 10
            );
            assert_eq!(
                (*leaf.key_ptr(insert_idx + 2)).assume_init_read(),
                (insert_idx + 1) as i32 * 2
            );
            assert_eq!(
                (*leaf.value_ptr(insert_idx + 2)).assume_init_read(),
                (insert_idx + 1) as i32 * 10
            );

            for i in 0..(cap - split_idx) {
                assert_eq!((*new_leaf.key_ptr(i)).assume_init_read(), (i + split_idx) as i32 * 2);
                assert_eq!(
                    (*new_leaf.value_ptr(i)).assume_init_read(),
                    (i + split_idx) as i32 * 10
                );
            }

            // Verify sibling pointers
            assert_eq!(
                (*leaf.brothers()).next,
                new_leaf.get_ptr(),
                "Left node's next should point to right node"
            );
            assert_eq!(
                (*new_leaf.brothers()).prev,
                leaf.get_ptr(),
                "Right node's prev should point to left node"
            );
            assert!((*leaf.brothers()).prev.is_null(), "Left node's prev should be null");
            assert!((*new_leaf.brothers()).next.is_null(), "Right node's next should be null");

            // Cleanup
            leaf.dealloc();
            new_leaf.dealloc();
        }
    }

    /// Test leaf node split when inserting key at split_idx (new key > old key at split_idx)
    #[test]
    fn test_leaf_node_split_insert_at_split_idx_right() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let cap = LeafNode::<i32, i32>::cap();
            // Fill the leaf with keys 0..cap
            for i in 0..cap {
                // println!("insert {} {}", i, i*10);
                leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
            }

            // Insert key larger than the key at split_idx
            let split_idx = (cap >> 1) as u32;
            println!("split_idx {split_idx}");
            let new_key = split_idx * 2 + 1; // odd number
            let new_value = new_key * 10;
            let (insert_idx, _is_equal) = leaf.search(&(new_key as i32));
            assert_eq!(insert_idx, split_idx + 1);
            assert!(!_is_equal);

            let (mut new_leaf, _ptr_v) =
                leaf.insert_with_split(insert_idx, new_key as i32, new_value as i32);

            // Verify the split
            let left_count = leaf.count();
            let right_count = new_leaf.count();
            assert_eq!(left_count, split_idx, "Left node should have keys");
            assert!(right_count > 0, "Right node should have keys");
            assert_eq!(left_count + right_count, cap + 1, "Total keys should be cap + 1");
            for i in 0..split_idx {
                assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32 * 2);
                assert_eq!((*leaf.value_ptr(i)).assume_init_read(), i as i32 * 10);
            }
            assert_eq!((*new_leaf.key_ptr(0)).assume_init_read(), split_idx as i32 * 2);
            assert_eq!((*new_leaf.value_ptr(0)).assume_init_read(), split_idx as i32 * 10);

            let found_key = (*new_leaf.key_ptr(1)).assume_init_ref();
            let found_value = (*new_leaf.value_ptr(1)).assume_init_ref();
            assert_eq!(*found_key, new_key as i32, "New key should be at position 1 in right node");
            assert_eq!(
                *found_value, new_value as i32,
                "New value should be at position 1 in right node"
            );
            for i in 0..(cap - split_idx - 1) {
                // println!("checkout {i} {}", i+2);
                assert_eq!(
                    (*new_leaf.key_ptr(i + 2)).assume_init_read(),
                    (i + split_idx + 1) as i32 * 2
                );
                assert_eq!(
                    (*new_leaf.value_ptr(i + 2)).assume_init_read(),
                    (i + split_idx + 1) as i32 * 10
                );
            }
            // Cleanup
            leaf.dealloc();
            new_leaf.dealloc();
        }
    }

    /// Test leaf node split when inserting key at the end (index = cap)
    #[test]
    fn test_leaf_node_split_insert_at_end() {
        unsafe {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let cap = LeafNode::<i32, i32>::cap();
            // Fill the leaf with keys 0..cap
            for i in 0..cap {
                leaf.insert_no_split(i as i32, i as i32 * 10);
            }
            let new_key = cap as i32;
            let new_value = new_key * 10;

            let (mut new_leaf, _ptr_v) = leaf.insert_with_split(cap, new_key, new_value);
            assert_eq!(*_ptr_v, new_value);

            // Verify the split
            let left_count = leaf.count();
            let right_count = new_leaf.count();

            assert_eq!(left_count, cap, "Left node keys unchanged");
            assert_eq!(right_count, 1, "Right node should have keys");

            // New key should be at position 0 in right node
            let found_key = (*new_leaf.key_ptr(0)).assume_init_ref();
            let found_value = (*new_leaf.value_ptr(0)).assume_init_ref();
            assert_eq!(*found_key, new_key, "New key should be at position 0 in right node");
            assert_eq!(*found_value, new_value, "New value should be at position 0 in right node");
            for i in 0..cap {
                assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32);
                assert_eq!((*leaf.value_ptr(i)).assume_init_read(), (i as i32) * 10);
            }
            // Cleanup
            leaf.dealloc();
            new_leaf.dealloc();
        }
    }
}
