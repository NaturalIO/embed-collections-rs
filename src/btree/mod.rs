//! B+Tree Map - A in memory cache-optimized B+Tree for single-threaded use.
//!
//! ## Feature outlines
//! - Designed for CPU cache efficiency and memory efficiency
//! - Optimised for numeric key type
//!   - Typical scenario: [range-tree-rs](https://docs.rs/range-tree-rs)
//! - A B+tree. Data stores only at leaf level, with links at leaf level.
//!   - Provides efficient iteration of data
//!   - Linear search within nodes, respecting cacheline boundaries
//! - Nodes are filled up in 4 cache lines (256 bytes on x86_64)
//!   - keys stored in first 128B (with header)
//!   - Values/pointers stored in last 128B
//!   - the capacity is calculated according to the size of K, V, with limitations:
//!     - K & V should <= CACHE_LINE_SIZE - 16  (If K & V is larger should put into `Box`)
//! - Specially Entry API which allow to modify after moving the cursor to adjacent data.
//! - The detail design notes are with the source in mod.rs and node.rs
//!
//! ## Special APIs
//!
//! batch removal:
//! - [BTreeMap::remove_range()]
//! - [BTreeMap::remove_range_with()]
//!
//! adjacent entry:
//! - [Entry::peak_forward()]
//! - [Entry::peak_backward()]
//! - [Entry::move_forward()]
//! - [Entry::move_backward()]
//! - [VacantEntry::peak_forward()]
//! - [VacantEntry::peak_backward()]
//! - [VacantEntry::move_forward()]
//! - [VacantEntry::move_backward()]
//! - [OccupiedEntry::peak_forward()]
//! - [OccupiedEntry::peak_backward()]
//! - [OccupiedEntry::move_forward()]
//! - [OccupiedEntry::move_backward()]
//! - [OccupiedEntry::alter_key()]

/*

# Designer notes

 Target scenario:  To maintain slab tree for disk, lets say 1 billion nodes, this design is aim for high fan-out.

 Since There're no parent pointer, no fence keys. So we maintain a cache to accelerate the look
 up for parent nodes.
 Since we support combining cursor moving in Entry API (try to merge with previous or next adjacent
 node). But user can call `remove()` on moved cursor.

## Acceleration Search for finding the parent using PathCache

- Assume PathCache is for Node A, Node B is the right brother of node A. A's ptr is at ParentA[idx]
  - To find parent for Node B
    - If idx < last (Cap - 1), then A and B has common parent,
    - otherwise A and B have no common parent. Should continue iteration to upper PathCache. There will be common ancestor until idx < last

- Assume PathCache is for Node B, Node A is the left brother of node B, B's ptr is at ParentB[idx]
  - To find parent for Node A
    - If idx > 0, then A and B has common parent.
    - otherwise A and B have no common parent. Should continue iteration to upper PathCache. There will be common ancestor until idx > 0

## Rebalance

- When insert on a full LeafNode, we try to move items to left/right brother, to delay split operation.

- One entry removed, current node usage < 50% (the threshold can be adjust according to tree size)

  - we don't need to borrow data from brothers (to avoid trashing), and we have already done borrowing on insert.

  - try to merge data, with left + current < cap, or current + right < cap, or left + current + right == 2 * cap

  - No need to mere 3 -> 1, because before reaching 30% average usage, we already checked 3 -> 2.

- The threshold to check merge for InterNode can be lower (like 30%), to avoid trashing


## Future ideas

- dynamically incress InterNode size, or variable size
- borrow from leaf / right on InterNode split, increase fill ratio to 80%
- 2 - 3 split (increase fill ratio to 90%)
*/

use core::borrow::Borrow;
use core::cell::UnsafeCell;
use core::fmt::Debug;
use core::ops::{Bound, RangeBounds};
mod entry;
pub use entry::*;
mod node;
use node::*;
mod inter;
use inter::*;
mod leaf;
use leaf::*;
mod iter;
#[allow(unused_imports)]
use crate::{print_log, trace_log};
use iter::RangeBase;
pub use iter::{IntoIter, Iter, IterMut, Keys, Range, RangeMut, Values, ValuesMut};

#[cfg(test)]
mod tests;

/// B+Tree Map for single-threaded usage, optimized for numeric type.
pub struct BTreeMap<K: Ord + Clone + Sized, V: Sized> {
    /// Root node (may be null for empty tree)
    root: Option<Node<K, V>>,
    /// Number of elements in the tree
    len: usize,
    // use unsafe to avoid borrow problems
    cache: UnsafeCell<PathCache<K, V>>,
    // count of leaf nodes
    leaf_count: usize,
    #[cfg(test)]
    triggers: u32,
}

#[cfg(test)]
#[repr(u32)]
enum TestFlag {
    LeafSplit = 1,
    InterSplit = 1 << 1,
    LeafMoveLeft = 1 << 2,
    LeafMoveRight = 1 << 3,
    LeafMergeLeft = 1 << 4,
    LeafMergeRight = 1 << 5,
    InterMoveLeft = 1 << 6,
    InterMoveLeftFirst = 1 << 7,
    InterMoveRight = 1 << 8,
    InterMoveRightLast = 1 << 9,
    InterMergeLeft = 1 << 10,
    InterMergeRight = 1 << 11,
    UpdateSepKey = 1 << 12,
    RemoveOnlyChild = 1 << 13,
    RemoveChildFirst = 1 << 14,
    RemoveChildMid = 1 << 15,
    RemoveChildLast = 1 << 16,
}

unsafe impl<K: Ord + Clone + Sized + Send, V: Sized + Send> Send for BTreeMap<K, V> {}
unsafe impl<K: Ord + Clone + Sized + Send, V: Sized + Send> Sync for BTreeMap<K, V> {}

#[cfg(feature = "std")]
impl<K: Ord + Clone + Sized, V: Sized> std::panic::RefUnwindSafe for BTreeMap<K, V> {}

impl<K: Ord + Sized + Clone, V: Sized> BTreeMap<K, V> {
    /// Create a new empty BTreeMap
    pub fn new() -> Self {
        Self {
            root: None,
            len: 0,
            cache: UnsafeCell::new(PathCache::<K, V>::new()),
            leaf_count: 0,
            #[cfg(test)]
            triggers: 0,
        }
    }

    /// Returns the number of elements in the map
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the map is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// return (cap_of_inter_node, cap_of_leaf_node)
    #[inline]
    pub const fn cap() -> (u32, u32) {
        let inter_cap = InterNode::<K, V>::cap();
        let leaf_cap = LeafNode::<K, V>::cap();
        (inter_cap, leaf_cap)
    }

    /// Return the number of leaf nodes
    #[inline]
    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    #[cfg(all(test, feature = "std"))]
    pub fn print_trigger_flags(&self) {
        let mut s = String::from("");
        if self.triggers & TestFlag::InterSplit as u32 > 0 {
            s += "InterSplit,";
        }
        if self.triggers & TestFlag::LeafSplit as u32 > 0 {
            s += "LeafSplit,";
        }
        if self.triggers & TestFlag::LeafMoveLeft as u32 > 0 {
            s += "LeafMoveLeft,";
        }
        if self.triggers & TestFlag::LeafMoveRight as u32 > 0 {
            s += "LeafMoveRight,";
        }
        if self.triggers & TestFlag::InterMoveLeft as u32 > 0 {
            s += "InterMoveLeft,";
        }
        if self.triggers & TestFlag::InterMoveRight as u32 > 0 {
            s += "InterMoveRight,";
        }
        if s.len() > 0 {
            print_log!("{s}");
        }
        let mut s = String::from("");
        if self.triggers & TestFlag::InterMergeLeft as u32 > 0 {
            s += "InterMergeLeft,";
        }
        if self.triggers & TestFlag::InterMergeRight as u32 > 0 {
            s += "InterMergeRight,";
        }
        if self.triggers & TestFlag::RemoveOnlyChild as u32 > 0 {
            s += "RemoveOnlyChild,";
        }
        if self.triggers
            & (TestFlag::RemoveChildFirst as u32
                | TestFlag::RemoveChildMid as u32
                | TestFlag::RemoveChildLast as u32)
            > 0
        {
            s += "RemoveChild,";
        }
        if s.len() > 0 {
            print_log!("{s}");
        }
    }

    /// Return the average fill ratio of leaf nodes
    ///
    /// The range is [0.0, 100]
    #[inline]
    pub fn get_fill_ratio(&self) -> f32 {
        if self.len == 0 {
            0.0
        } else {
            let cap = LeafNode::<K, V>::cap() as usize * self.leaf_count;
            self.len as f32 / cap as f32 * 100.0
        }
    }

    /// When root is leaf, returns 1, otherwise return the number of layers of inter node
    #[inline(always)]
    pub fn height(&self) -> u32 {
        if let Some(Node::Inter(node)) = &self.root {
            return node.height() + 1;
        }
        1
    }

    #[inline(always)]
    fn get_cache(&self) -> &mut PathCache<K, V> {
        unsafe { (&mut *self.cache.get()) as _ }
    }

    /// Returns an entry to the key in the map
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let cache = self.get_cache();
        cache.clear();
        let leaf = match &self.root {
            None => return Entry::Vacant(VacantEntry { tree: self, key, idx: 0, leaf: None }),
            Some(root) => root.find_leaf_with_cache(cache, &key),
        };
        let (idx, is_equal) = leaf.search(&key);
        if is_equal {
            Entry::Occupied(OccupiedEntry { tree: self, idx, leaf })
        } else {
            Entry::Vacant(VacantEntry { tree: self, key, idx, leaf: Some(leaf) })
        }
    }

    #[inline(always)]
    fn find<Q>(&self, key: &Q) -> Option<(LeafNode<K, V>, u32)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let leaf = match &self.root {
            None => return None,
            Some(root) => root.find_leaf(key),
        };
        let (idx, is_equal) = leaf.search(key);
        trace_log!("find leaf {leaf:?} {idx} exist {is_equal}");
        if is_equal { Some((leaf, idx)) } else { None }
    }

    /// Returns true if the map contains the key
    #[inline(always)]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.find::<Q>(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some((leaf, idx)) = self.find::<Q>(key) {
            let value = unsafe { leaf.value_ptr(idx) };
            debug_assert!(!value.is_null());
            Some(unsafe { (*value).assume_init_ref() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the key
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some((leaf, idx)) = self.find::<Q>(key) {
            let value = unsafe { leaf.value_ptr(idx) };
            debug_assert!(!value.is_null());
            Some(unsafe { (*value).assume_init_mut() })
        } else {
            None
        }
    }

    /// Insert a key-value pair into the map
    /// Returns the old value if the key already existed
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // use entry api to insert
        match self.entry(key) {
            Entry::Occupied(mut entry) => Some(entry.insert(value)),
            Entry::Vacant(entry) => {
                entry.insert(value);
                None
            }
        }
    }

    /// Remove a key from the map, returning the value if it existed
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(root) = &self.root {
            let cache = self.get_cache();
            cache.clear();
            let mut leaf = root.find_leaf_with_cache::<Q>(cache, key);
            let (idx, is_equal) = leaf.search(key);
            if is_equal {
                trace_log!("{leaf:?} remove {idx}");
                let val = leaf.remove_value_no_borrow(idx);
                self.len -= 1;
                // Check for underflow and handle merge
                let new_count = leaf.key_count();
                let min_count = LeafNode::<K, V>::cap() >> 1;
                if new_count < min_count && !root.is_leaf() {
                    // The cache should already contain the path from the entry lookup
                    self.handle_leaf_underflow(leaf, true);
                }
                Some(val)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Perform removal in batch mode and return the last item removed
    ///
    /// NOTE: this function speed up by skipping the underflow of LeafNode until the last operation.
    pub fn remove_range<R>(&mut self, range: R) -> Option<(K, V)>
    where
        R: RangeBounds<K>,
    {
        self.remove_range_with::<R, _>(range, |_, _| {})
    }

    /// Perform removal in batch mode and return the last item removed
    ///
    /// On each removal, callback function `cb` is invoke with (ref of key, ref of value)
    ///
    /// NOTE: this function speed up by skipping the underflow of LeafNode until the last operation.
    #[inline]
    pub fn remove_range_with<R, F>(&mut self, range: R, mut cb: F) -> Option<(K, V)>
    where
        R: RangeBounds<K>,
        F: FnMut(&K, &V),
    {
        macro_rules! end_contains {
            ($key: expr) => {{
                match range.end_bound() {
                    Bound::Excluded(k) => $key < k,
                    Bound::Included(k) => $key <= k,
                    Bound::Unbounded => true,
                }
            }};
        }
        // Note: do not use find_leaf_with_bound, it's a different behavior
        let mut ent = match range.start_bound() {
            Bound::Excluded(k) => match self.entry(k.clone()).move_forward() {
                Ok(ent) => {
                    if end_contains!(ent.key()) {
                        ent
                    } else {
                        return None;
                    }
                }
                Err(_) => return None,
            },
            Bound::Included(k) => match self.entry(k.clone()) {
                Entry::Occupied(ent) => ent,
                Entry::Vacant(ent) => match ent.move_forward() {
                    Ok(ent) => {
                        if end_contains!(ent.key()) {
                            ent
                        } else {
                            return None;
                        }
                    }
                    Err(_) => return None,
                },
            },
            Bound::Unbounded => {
                if let Some(ent) = self.first_entry() {
                    ent
                } else {
                    return None;
                }
            }
        };
        loop {
            if let Some((_next_k, _next_v)) = ent.peak_forward() {
                if end_contains!(_next_k) {
                    let next_key = _next_k.clone();
                    let (_k, _v) = ent._remove_entry(false);
                    cb(&_k, &_v);
                    if let Entry::Occupied(_ent) = self.entry(next_key) {
                        ent = _ent;
                        continue;
                    } else {
                        unreachable!();
                    }
                }
            }
            let (_k, _v) = ent._remove_entry(true);
            cb(&_k, &_v);
            return Some((_k, _v));
        }
    }

    #[inline(always)]
    fn get_root_unwrap(&self) -> &Node<K, V> {
        self.root.as_ref().unwrap()
    }

    /// update the separate_key in parent after borrowing space from left/right node
    #[inline(always)]
    fn update_ancestor_sep_key<const MOVE: bool>(&mut self, sep_key: K) {
        // if idx == 0, this is the leftmost ptr in the InterNode, we go up until finding a
        // split key
        let ret = if MOVE {
            self.get_cache()
                .move_to_ancenstor(|_node, idx| -> bool { idx > 0 }, dummy_post_callback)
        } else {
            self.get_cache().peak_ancenstor(|_node, idx| -> bool { idx > 0 })
        };
        if let Some((parent, parent_idx)) = ret {
            trace_log!("update_ancestor_sep_key move={MOVE} at {parent:?}:{}", parent_idx - 1);
            #[cfg(test)]
            {
                self.triggers |= TestFlag::UpdateSepKey as u32;
            }
            parent.change_key(parent_idx - 1, sep_key);
        }
    }

    /// Insert with split handling - called when leaf is full
    fn insert_with_split(
        &mut self, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
    ) -> *mut V {
        debug_assert!(leaf.is_full());
        let cap = LeafNode::<K, V>::cap();
        if idx < cap {
            // random insert, try borrow space from left and right
            if let Some(mut left_node) = leaf.get_left_node()
                && !left_node.is_full()
            {
                trace_log!("insert {leaf:?}:{idx} borrow left {left_node:?}");
                let val_p = if idx == 0 {
                    // leaf is not change, but since the insert pos is leftmost of this node, mean parent
                    // separate_key <= key, need to update its separate_key
                    left_node.insert_no_split_with_idx(left_node.key_count(), key, value)
                } else {
                    leaf.insert_borrow_left(&mut left_node, idx, key, value)
                };
                #[cfg(test)]
                {
                    self.triggers |= TestFlag::LeafMoveLeft as u32;
                }
                self.update_ancestor_sep_key::<true>(leaf.clone_first_key());
                return val_p;
            }
        } else {
            // insert into empty new node, left is probably full, right is probably none
        }
        if let Some(mut right_node) = leaf.get_right_node()
            && !right_node.is_full()
        {
            trace_log!("insert {leaf:?}:{idx} borrow right {right_node:?}");
            let val_p = if idx == cap {
                // leaf is not change, in this condition, right_node is the leftmost child
                // of its parent, key < right_node.get_keys()[0]
                right_node.insert_no_split_with_idx(0, key, value)
            } else {
                leaf.borrow_right(&mut right_node);
                leaf.insert_no_split_with_idx(idx, key, value)
            };
            #[cfg(test)]
            {
                self.triggers |= TestFlag::LeafMoveRight as u32;
            }
            self.get_cache().move_right();
            self.update_ancestor_sep_key::<true>(right_node.clone_first_key());
            return val_p;
        }
        #[cfg(test)]
        {
            self.triggers |= TestFlag::LeafSplit as u32;
        }
        let (new_leaf, ptr_v) = leaf.insert_with_split(idx, key, value);
        self.leaf_count += 1;
        let split_key = unsafe { (*new_leaf.key_ptr(0)).assume_init_ref().clone() };
        self.propagate_split(split_key, leaf.get_ptr(), new_leaf.get_ptr());
        ptr_v
    }

    /// Propagate node split up the tree using iteration (non-recursive)
    /// First tries to borrow space from left/right sibling before splitting
    ///
    /// left_ptr: existing child
    /// right_ptr: new_child split from left_ptr
    /// promote_key: sep_key to split left_ptr & right_ptr
    #[inline(always)]
    fn propagate_split(
        &mut self, mut promote_key: K, mut left_ptr: *mut NodeHeader,
        mut right_ptr: *mut NodeHeader,
    ) {
        let mut height = 0;
        // If we have parent nodes in cache, process them iteratively
        while let Some((mut parent, idx)) = self.get_cache().pop() {
            if !parent.is_full() {
                trace_log!("propagate_split {parent:?}:{idx} insert {right_ptr:p}");
                // should insert next to left_ptr
                parent.insert_no_split_with_idx(idx, promote_key, right_ptr);
                return;
            } else {
                // Parent is full, try to borrow space from sibling through grand_parent
                if let Some((mut grand, grand_idx)) = self.get_cache().peak_next() {
                    // Try to borrow from left sibling of parent
                    if grand_idx > 0 {
                        let mut left_parent = grand.get_child_as_inter(grand_idx - 1);
                        if !left_parent.is_full() {
                            #[cfg(test)]
                            {
                                self.triggers |= TestFlag::InterMoveLeft as u32;
                            }
                            if idx == 0 {
                                trace_log!(
                                    "propagate_split rotate_left {grand:?}:{} first ->{left_parent:?} left {left_ptr:p} insert {idx} {right_ptr:p}",
                                    grand_idx - 1
                                );
                                // special case: split from first child of parent
                                let demote_key = grand.change_key(grand_idx - 1, promote_key);
                                debug_assert_eq!(parent.get_child_ptr(0), left_ptr);
                                unsafe { (*parent.child_ptr(0)) = right_ptr };
                                left_parent.append(demote_key, left_ptr);
                                #[cfg(test)]
                                {
                                    self.triggers |= TestFlag::InterMoveLeftFirst as u32;
                                }
                            } else {
                                trace_log!(
                                    "propagate_split insert_rotate_left {grand:?}:{grand_idx} -> {left_parent:?} insert {idx} {right_ptr:p}"
                                );
                                parent.insert_rotate_left(
                                    &mut grand,
                                    grand_idx,
                                    &mut left_parent,
                                    idx,
                                    promote_key,
                                    right_ptr,
                                );
                            }
                            return;
                        }
                    }
                    // Try to borrow from right sibling of parent
                    if grand_idx < grand.key_count() {
                        let mut right_parent = grand.get_child_as_inter(grand_idx + 1);
                        if !right_parent.is_full() {
                            #[cfg(test)]
                            {
                                self.triggers |= TestFlag::InterMoveRight as u32;
                            }
                            if idx == parent.key_count() {
                                trace_log!(
                                    "propagate_split rotate_right last {grand:?}:{grand_idx} -> {right_parent:?}:0 insert right {right_parent:?}:0 {right_ptr:p}"
                                );
                                // split from last child of parent
                                let demote_key = grand.change_key(grand_idx, promote_key);
                                right_parent.insert_at_front(right_ptr, demote_key);
                                #[cfg(test)]
                                {
                                    self.triggers |= TestFlag::InterMoveRightLast as u32;
                                }
                            } else {
                                trace_log!(
                                    "propagate_split rotate_right {grand:?}:{grand_idx} -> {right_parent:?}:0 insert {parent:?}:{idx} {right_ptr:p}"
                                );
                                parent.rotate_right(&mut grand, grand_idx, &mut right_parent);
                                parent.insert_no_split_with_idx(idx, promote_key, right_ptr);
                            }
                            return;
                        }
                    }
                }
                height += 1;

                // Cannot borrow from siblings, need to split internal node
                let (right, _promote_key) = parent.insert_split(promote_key, right_ptr);
                promote_key = _promote_key;
                right_ptr = right.get_ptr();
                left_ptr = parent.get_ptr();
                #[cfg(test)]
                {
                    self.triggers |= TestFlag::InterSplit as u32;
                }
                // Continue to next parent in cache (loop will pop next parent)
            }
        }
        // No more parents in cache, create new root
        let new_root = InterNode::<K, V>::new_root(height + 1, promote_key, left_ptr, right_ptr);
        let _old_root = self.root.replace(Node::Inter(new_root)).expect("should have old root");
        #[cfg(debug_assertions)]
        {
            match _old_root {
                Node::Inter(node) => {
                    debug_assert_eq!(height, node.height(), "old inter root at {height}");
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
                Node::Leaf(node) => {
                    debug_assert_eq!(height, 0);
                    debug_assert_eq!(node.get_ptr(), left_ptr);
                }
            }
        }
    }

    /// Handle leaf node underflow by merging with sibling
    /// Uses PathCache to accelerate parent lookup
    /// Following the merge strategy from Designer Notes:
    /// - Try merge with left sibling (if left + current <= cap)
    /// - Try merge with right sibling (if current + right <= cap)
    /// - Try 3-node merge (if left + current + right <= 2 * cap)
    fn handle_leaf_underflow(&mut self, mut leaf: LeafNode<K, V>, merge: bool) {
        debug_assert!(!self.get_root_unwrap().is_leaf());
        let cur_count = leaf.key_count();
        let cap = LeafNode::<K, V>::cap();
        debug_assert!(cur_count <= cap >> 1);
        let mut can_unlink: bool = false;
        let (mut left_avail, mut right_avail) = (0, 0);
        let mut merge_right = false;
        if cur_count == 0 {
            trace_log!("handle_leaf_underflow {leaf:?} unlink");
            // if the right and left are full, or they not exist, can come to this
            can_unlink = true;
        }
        if merge {
            if !can_unlink && let Some(mut left_node) = leaf.get_left_node() {
                let left_count = left_node.key_count();
                if left_count + cur_count <= cap {
                    trace_log!(
                        "handle_leaf_underflow {leaf:?} merge left {left_node:?} {cur_count}"
                    );
                    leaf.copy_left(&mut left_node, cur_count);
                    can_unlink = true;
                    #[cfg(test)]
                    {
                        self.triggers |= TestFlag::LeafMergeLeft as u32;
                    }
                } else {
                    left_avail = cap - left_count;
                }
            }
            if !can_unlink && let Some(mut right_node) = leaf.get_right_node() {
                let right_count = right_node.key_count();
                if right_count + cur_count <= cap {
                    trace_log!(
                        "handle_leaf_underflow {leaf:?} merge right {right_node:?} {cur_count}"
                    );
                    leaf.copy_right::<false>(&mut right_node, 0, cur_count);
                    can_unlink = true;
                    merge_right = true;
                    #[cfg(test)]
                    {
                        self.triggers |= TestFlag::LeafMergeRight as u32;
                    }
                } else {
                    right_avail = cap - right_count;
                }
            }
            // if we require left_avail + right_avail > cur_count, not possible to construct a 3-2
            // merge, only either triggering merge left or merge right.
            if !can_unlink
                && left_avail > 0
                && right_avail > 0
                && left_avail + right_avail == cur_count
            {
                let mut left_node = leaf.get_left_node().unwrap();
                let mut right_node = leaf.get_right_node().unwrap();
                debug_assert!(left_avail < cur_count);
                trace_log!("handle_leaf_underflow {leaf:?} merge left {left_node:?} {left_avail}");
                leaf.copy_left(&mut left_node, left_avail);
                trace_log!(
                    "handle_leaf_underflow {leaf:?} merge right {right_node:?} {}",
                    cur_count - left_avail
                );
                leaf.copy_right::<false>(&mut right_node, left_avail, cur_count - left_avail);
                merge_right = true;
                can_unlink = true;
                #[cfg(test)]
                {
                    self.triggers |=
                        TestFlag::LeafMergeLeft as u32 | TestFlag::LeafMergeRight as u32;
                }
            }
        }
        if !can_unlink {
            return;
        }
        self.leaf_count -= 1;
        let right_sep = if merge_right {
            let right_node = leaf.get_right_node().unwrap();
            Some(right_node.clone_first_key())
        } else {
            None
        };
        let no_right = leaf.unlink().is_null();
        leaf.dealloc::<false>();
        let (mut parent, mut idx) = self.get_cache().pop().unwrap();
        trace_log!("handle_leaf_underflow pop parent {parent:?}:{idx}");
        if parent.key_count() == 0 {
            if let Some((grand, grand_idx)) = self.remove_only_child(parent) {
                trace_log!("handle_leaf_underflow remove_only_child until {grand:?}:{grand_idx}");
                parent = grand;
                idx = grand_idx;
            } else {
                trace_log!("handle_leaf_underflow remove_only_child all");
                return;
            }
        }
        self.remove_child_from_inter(&mut parent, idx, right_sep, no_right);
        if parent.key_count() <= 1 {
            self.handle_inter_underflow(parent);
        }
    }

    /// To simplify the logic, we perform delete first.
    /// return the Some(node) when need to rebalance
    #[inline]
    fn remove_child_from_inter(
        &mut self, node: &mut InterNode<K, V>, delete_idx: u32, right_sep: Option<K>,
        _no_right: bool,
    ) {
        self.get_cache().assert_center();
        debug_assert!(node.key_count() > 0, "{:?} {}", node, node.key_count());
        if delete_idx == node.key_count() {
            trace_log!("remove_child_from_inter {node:?}:{delete_idx} last");
            #[cfg(test)]
            {
                self.triggers |= TestFlag::RemoveChildLast as u32;
            }
            // delete the last child of this node
            node.remove_last_child();
            if let Some(key) = right_sep
                && let Some((grand_parent, grand_idx)) =
                    self.get_cache().peak_ancenstor(|_node: &InterNode<K, V>, idx: u32| -> bool {
                        _node.key_count() > idx
                    })
            {
                #[cfg(test)]
                {
                    self.triggers |= TestFlag::UpdateSepKey as u32;
                }
                trace_log!("remove_child_from_inter change_key {grand_parent:?}:{grand_idx}");
                // key idx = child idx - 1 , and + 1 for right node
                grand_parent.change_key(grand_idx, key);
            }
        } else if delete_idx > 0 {
            trace_log!("remove_child_from_inter {node:?}:{delete_idx} mid");
            node.remove_mid_child(delete_idx);
            #[cfg(test)]
            {
                self.triggers |= TestFlag::RemoveChildMid as u32;
            }
            // sep key of right node shift left
            if let Some(key) = right_sep {
                trace_log!("remove_child_from_inter change_key {node:?}:{}", delete_idx - 1);
                node.change_key(delete_idx - 1, key);
                #[cfg(test)]
                {
                    self.triggers |= TestFlag::UpdateSepKey as u32;
                }
            }
        } else {
            trace_log!("remove_child_from_inter {node:?}:{delete_idx} first");
            // delete_idx is the first but not the last
            let mut sep_key = node.remove_first_child();
            #[cfg(test)]
            {
                self.triggers |= TestFlag::RemoveChildFirst as u32;
            }
            if let Some(key) = right_sep {
                sep_key = key;
            }
            self.update_ancestor_sep_key::<false>(sep_key);
        }
    }

    #[inline]
    fn handle_inter_underflow(&mut self, mut node: InterNode<K, V>) {
        let cap = InterNode::<K, V>::cap();
        while node.key_count() <= InterNode::<K, V>::UNDERFLOW_CAP {
            if node.key_count() == 0 {
                let root_height = self.get_root_unwrap().height();
                if node.height() == root_height
                    || self
                        .get_cache()
                        .peak_ancenstor(|_node: &InterNode<K, V>, _idx: u32| -> bool {
                            _node.key_count() > 0
                        })
                        .is_none()
                {
                    let root = unsafe { Node::from_header(*node.child_ptr(0)) };
                    trace_log!("handle_inter_underflow downgrade root {root:?}");
                    let _old_root = self.root.replace(root);
                    debug_assert!(_old_root.is_some());

                    while let Some((parent, _)) = self.get_cache().pop() {
                        parent.dealloc::<false>();
                    }
                    node.dealloc::<false>(); // they all have no key
                }
                return;
            } else {
                if let Some((mut grand, grand_idx)) = self.get_cache().pop() {
                    if grand_idx > 0 {
                        let mut left = grand.get_child_as_inter(grand_idx - 1);
                        // the sep key should pull down,  key+1 + key + 1 > cap + 1
                        if left.key_count() + node.key_count() < cap {
                            #[cfg(test)]
                            {
                                self.triggers |= TestFlag::InterMergeLeft as u32;
                            }
                            trace_log!(
                                "handle_inter_underflow {node:?} merge left {left:?} parent {grand:?}:{grand_idx}"
                            );
                            left.merge(node, &mut grand, grand_idx);
                            node = grand;
                            continue;
                        }
                    }
                    if grand_idx < grand.key_count() {
                        let right = grand.get_child_as_inter(grand_idx + 1);
                        // the sep key should pull down,  key+1 + key + 1 > cap + 1
                        if right.key_count() + node.key_count() < cap {
                            #[cfg(test)]
                            {
                                self.triggers |= TestFlag::InterMergeRight as u32;
                            }
                            trace_log!(
                                "handle_inter_underflow {node:?} cap {cap} merge right {right:?} parent {grand:?}:{}",
                                grand_idx + 1
                            );
                            node.merge(right, &mut grand, grand_idx + 1);
                            node = grand;
                            continue;
                        }
                    }
                }
                return;
            }
        }
    }

    #[inline]
    fn remove_only_child(&mut self, node: InterNode<K, V>) -> Option<(InterNode<K, V>, u32)> {
        debug_assert_eq!(node.key_count(), 0);
        #[cfg(test)]
        {
            self.triggers |= TestFlag::RemoveOnlyChild as u32;
        }
        if let Some((parent, idx)) = self.get_cache().move_to_ancenstor(
            |node: &InterNode<K, V>, _idx: u32| -> bool { node.key_count() != 0 },
            InterNode::<K, V>::dealloc::<false>,
        ) {
            node.dealloc::<true>();
            Some((parent, idx))
        } else {
            node.dealloc::<true>();
            // we are empty, my ancestor are all empty and delete by move_to_ancenstor
            self.root = None;
            None
        }
    }

    /// Dump the entire tree structure for debugging
    #[cfg(all(test, feature = "std"))]
    pub fn dump(&self)
    where
        K: Debug,
        V: Debug,
    {
        print_log!("=== BTreeMap Dump ===");
        print_log!("Length: {}", self.len());
        if let Some(root) = &self.root {
            self.dump_node(root, 0);
        } else {
            print_log!("(empty)");
        }
        print_log!("=====================");
    }

    #[cfg(all(test, feature = "std"))]
    fn dump_node(&self, node: &Node<K, V>, depth: usize)
    where
        K: Debug,
        V: Debug,
    {
        match node {
            Node::Leaf(leaf) => {
                print!("{:indent$}", "", indent = depth * 2);
                print_log!("{}", leaf);
            }
            Node::Inter(inter) => {
                print!("{:indent$}", "", indent = depth * 2);
                print_log!("{}", inter);
                // Dump children
                let count = inter.key_count() as u32;
                for i in 0..=count {
                    unsafe {
                        let child_ptr = *inter.child_ptr(i);
                        if !child_ptr.is_null() {
                            let child_node = if (*child_ptr).is_leaf() {
                                Node::Leaf(LeafNode::<K, V>::from_header(child_ptr))
                            } else {
                                Node::Inter(InterNode::<K, V>::from_header(child_ptr))
                            };
                            self.dump_node(&child_node, depth + 1);
                        }
                    }
                }
            }
        }
    }

    /// Validate the entire tree structure
    /// Uses the same traversal logic as Drop to avoid recursion
    pub fn validate(&self)
    where
        K: Debug,
        V: Debug,
    {
        if self.root.is_none() {
            assert_eq!(self.len, 0, "Empty tree should have len 0");
            return;
        }

        let mut total_keys = 0usize;
        let mut prev_leaf_max: Option<K> = None;

        match &self.root {
            Some(Node::Leaf(leaf)) => {
                total_keys += leaf.validate(None, None);
            }
            Some(Node::Inter(inter)) => {
                // Do not use btree internal PathCache (might distrupt test scenario)
                let mut cache = PathCache::new();
                let mut cur = inter.clone();
                loop {
                    cache.push(cur.clone(), 0);
                    cur.validate();
                    match cur.get_child(0) {
                        Node::Leaf(leaf) => {
                            // Validate first leaf with no min/max bounds from parent
                            let min_key: Option<K> = None;
                            let max_key = if inter.key_count() > 0 {
                                unsafe { Some((*inter.key_ptr(0)).assume_init_ref().clone()) }
                            } else {
                                None
                            };
                            total_keys += leaf.validate(min_key.as_ref(), max_key.as_ref());
                            if let Some(ref prev_max) = prev_leaf_max {
                                let first_key = unsafe { (*leaf.key_ptr(0)).assume_init_ref() };
                                assert!(
                                    prev_max < first_key,
                                    "{:?} Leaf keys not in order: prev max {:?} >= current min {:?}",
                                    leaf,
                                    prev_max,
                                    first_key
                                );
                            }
                            prev_leaf_max = unsafe {
                                Some(
                                    (*leaf.key_ptr(leaf.key_count() - 1)).assume_init_ref().clone(),
                                )
                            };
                            break;
                        }
                        Node::Inter(child_inter) => {
                            cur = child_inter;
                        }
                    }
                }

                // Continue traversal like Drop does
                while let Some((parent, idx)) =
                    cache.move_right_and_pop_l1(dummy_post_callback::<K, V>)
                {
                    cache.push(parent.clone(), idx);
                    if let Node::Leaf(leaf) = parent.get_child(idx) {
                        // Calculate bounds for this leaf
                        let min_key = if idx > 0 {
                            unsafe { Some((*parent.key_ptr(idx - 1)).assume_init_ref().clone()) }
                        } else {
                            None
                        };
                        let max_key = if idx < parent.key_count() {
                            unsafe { Some((*parent.key_ptr(idx)).assume_init_ref().clone()) }
                        } else {
                            None
                        };
                        total_keys += leaf.validate(min_key.as_ref(), max_key.as_ref());

                        // Check ordering with previous leaf
                        if let Some(ref prev_max) = prev_leaf_max {
                            let first_key = unsafe { (*leaf.key_ptr(0)).assume_init_ref() };
                            assert!(
                                prev_max < first_key,
                                "{:?} Leaf keys not in order: prev max {:?} >= current min {:?}",
                                leaf,
                                prev_max,
                                first_key
                            );
                        }
                        prev_leaf_max = unsafe {
                            Some((*leaf.key_ptr(leaf.key_count() - 1)).assume_init_ref().clone())
                        };
                    } else {
                        panic!("{parent:?} child {:?} is not leaf", parent.get_child(idx));
                    }
                }
            }
            None => unreachable!(),
        }
        assert_eq!(
            total_keys, self.len,
            "Total keys in tree ({}) doesn't match len ({})",
            total_keys, self.len
        );
    }

    /// Returns the first key-value pair in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let leaf = match &self.root {
            None => return None,
            Some(root) => root.find_first_leaf(None),
        };
        if leaf.key_count() == 0 {
            return None;
        }
        unsafe {
            let key = (*leaf.key_ptr(0)).assume_init_ref();
            let value = (*leaf.value_ptr(0)).assume_init_ref();
            Some((key, value))
        }
    }

    /// Returns the last key-value pair in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let leaf = match &self.root {
            None => return None,
            Some(root) => root.find_last_leaf(None),
        };
        let count = leaf.key_count();
        if count == 0 {
            return None;
        }
        unsafe {
            let last_idx = count - 1;
            let key = (*leaf.key_ptr(last_idx)).assume_init_ref();
            let value = (*leaf.value_ptr(last_idx)).assume_init_ref();
            Some((key, value))
        }
    }

    /// Returns an entry to the first key in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let cache = self.get_cache();
        cache.clear();
        let leaf = match &self.root {
            None => return None,
            Some(root) => {
                // Populate cache with the path to first leaf
                root.find_first_leaf(Some(cache))
            }
        };
        if leaf.key_count() == 0 {
            return None;
        }
        Some(OccupiedEntry { tree: self, idx: 0, leaf })
    }

    /// Returns an entry to the last key in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>> {
        let cache = self.get_cache();
        cache.clear();
        let leaf = match &self.root {
            None => return None,
            Some(root) => {
                // Populate cache with the path to last leaf
                root.find_last_leaf(Some(cache))
            }
        };
        let count = leaf.key_count();
        if count == 0 {
            return None;
        }
        Some(OccupiedEntry { tree: self, idx: count - 1, leaf })
    }

    /// Removes and returns the first key-value pair in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        match self.first_entry() {
            Some(entry) => Some(entry.remove_entry()),
            _ => None,
        }
    }

    /// Removes and returns the last key-value pair in the map
    /// Returns `None` if the map is empty
    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        match self.last_entry() {
            Some(entry) => Some(entry.remove_entry()),
            _ => None,
        }
    }

    /// Returns an iterator over the map's entries
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self.find_first_and_last_leaf(), self.len)
    }

    /// Returns a mutable iterator over the map's entries
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self.find_first_and_last_leaf(), self.len)
    }

    /// Returns an iterator over the map's keys
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(self.iter())
    }

    /// Returns an iterator over the map's values
    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(self.iter())
    }

    /// Returns a mutable iterator over the map's values
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::new(self.iter_mut())
    }

    #[inline]
    fn find_first_and_last_leaf(&self) -> Option<(LeafNode<K, V>, LeafNode<K, V>)> {
        let root = self.root.as_ref()?;
        Some((root.find_first_leaf(None), root.find_last_leaf(None)))
    }

    /// Internal helper to find range bounds
    /// Returns (front_leaf, front_idx, back_leaf, back_idx) where both leaves are Some or both are None
    #[inline]
    fn find_range_bounds<R>(&self, range: R) -> Option<RangeBase<'_, K, V>>
    where
        R: RangeBounds<K>,
    {
        let root = self.root.as_ref()?;
        let (front_leaf, front_idx) = root.find_leaf_with_bound(range.start_bound(), true);
        let (back_leaf, back_idx) = root.find_leaf_with_bound(range.end_bound(), false);
        Some(RangeBase::new(front_leaf, front_idx, back_leaf, back_idx))
    }

    /// Returns an iterator over a sub-range of entries in the map
    #[inline]
    pub fn range<R>(&self, range: R) -> Range<'_, K, V>
    where
        R: RangeBounds<K>,
    {
        Range::new(self.find_range_bounds(range))
    }

    /// Returns a mutable iterator over a sub-range of entries in the map
    #[inline]
    pub fn range_mut<R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        R: RangeBounds<K>,
    {
        RangeMut::new(self.find_range_bounds(range))
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone + Sized, V: Sized> Drop for BTreeMap<K, V> {
    fn drop(&mut self) {
        let mut cache = self.get_cache().take();
        let mut cur = match self.root.take() {
            None => return,
            Some(root) => root.find_first_leaf(Some(&mut cache)),
        };
        cur.dealloc::<true>();
        // To navigate to next leaf,
        // return None when reach the end
        while let Some((parent, idx)) = cache.move_right_and_pop_l1(InterNode::dealloc::<true>) {
            cache.push(parent.clone(), idx);
            cur = parent.get_child_as_leaf(idx);
            cur.dealloc::<true>();
        }
    }
}

impl<K: Ord + Clone + Sized, V: Sized> IntoIterator for BTreeMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self, true)
    }
}
impl<'a, K: Ord + Clone + Sized, V: Sized> IntoIterator for &'a BTreeMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: Ord + Clone + Sized, V: Sized> IntoIterator for &'a mut BTreeMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
