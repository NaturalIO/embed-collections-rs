use super::{inter::*, leaf::*};
use crate::CACHE_LINE_SIZE;
use alloc::alloc::{Layout, alloc, handle_alloc_error};
use alloc::vec::Vec;
use core::ptr::{self, NonNull, null_mut};

/// Key area size: first 128 bytes (2 cache lines)
pub(super) const AREA_SIZE: usize = 2 * CACHE_LINE_SIZE; // 128 bytes

/// Total node size: 4 cache lines (256 bytes on x86_64)
pub(super) const NODE_SIZE: usize = 2 * AREA_SIZE; // 256 bytes

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
    pub(crate) height: u32,
    /// Count of items in the node
    pub(crate) count: u32,
}

impl NodeHeader {
    #[inline]
    pub unsafe fn get_field<T>(p: NonNull<Self>, offset: usize) -> *mut T {
        unsafe { (p.as_ptr() as *const u8).add(offset) as *mut T }
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
    pub fn alloc(layout: Layout) -> Self {
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
    pub fn get_ptr(&self) -> *mut NodeHeader {
        self.header.as_ptr() as *mut NodeHeader
    }

    #[inline(always)]
    pub fn get_array<T>(&self, header_size: usize, delta: usize) -> &[T] {
        let header = self.get_header();
        let items_ptr = unsafe { NodeHeader::get_field::<T>(self.header, header_size) };
        unsafe { core::slice::from_raw_parts::<T>(items_ptr, header.count as usize + delta) }
    }

    /// Get pointer to key at index with given header offset
    #[inline(always)]
    pub unsafe fn item_ptr<T>(&self, start_offset: usize, idx: u32) -> *mut T {
        unsafe {
            NodeHeader::get_field::<T>(self.header, start_offset + idx as usize * size_of::<T>())
        }
    }

    /// Check if this is a leaf node
    #[inline(always)]
    pub fn is_leaf(&self) -> bool {
        self.get_header().is_leaf()
    }

    /// Get count of items in the node
    #[inline(always)]
    pub fn count(&self) -> usize {
        self.get_header().count as usize
    }

    /// Get height of the node
    #[inline(always)]
    pub fn height(&self) -> u32 {
        self.get_header().height
    }

    /// search the position to insert (need to move old items from idx to the right)
    /// returns the idx, is_equal
    #[inline]
    pub fn search<K>(&self, header_offset: usize, key: &K) -> (u32, bool)
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
    pub unsafe fn remove_slot<T>(&mut self, header_offset: usize, idx: u32, mut left: u32) -> T {
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
    pub unsafe fn insert<K, V>(
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
                    if cur.is_leaf() {
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
                    if cur.is_leaf() {
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

#[cfg(test)]
mod tests {
    use super::super::inter::*;
    use super::super::leaf::*;
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
}
