#[cfg(all(test, feature = "trace_log"))]
use super::TestFlag;
use super::{helper::*, inter::*, leaf::*, node::*, stats::*};
#[allow(unused_imports)]
use crate::{print_log, trace_log};
use core::fmt::Debug;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// B+Tree Map for single-threaded usage, optimized for numeric type.
pub(super) struct BTreeInner<K: Ord + Clone + Sized, V: Sized> {
    // Root node (may be None for empty tree)
    // `Option<Node>` is larger than `Option<NonNull<NodeHeader>>`
    pub root: Option<NonNull<NodeHeader>>,
    /// Number of elements in the tree
    pub len: usize,
    #[cfg(all(test, feature = "trace_log"))]
    pub triggers: u32,
    pub _phan: PhantomData<fn(&K, &V)>,
}

impl<K: Ord + Clone + Sized, V: Sized> BTreeInner<K, V> {
    #[inline(always)]
    pub fn get_root_unwrap(&self) -> Node<K, V> {
        Node::<K, V>::from_root_ptr(*self.root.as_ref().unwrap())
    }

    #[inline(always)]
    pub fn get_root(&self) -> Option<Node<K, V>> {
        Some(Node::<K, V>::from_root_ptr(*self.root.as_ref()?))
    }

    #[inline(always)]
    pub fn root_is_inter(&self) -> bool {
        if let Some(root) = self.root { !Node::<K, V>::root_is_leaf(root) } else { false }
    }

    #[inline]
    pub fn init_empty(&mut self, key: K, value: V) -> &mut V {
        debug_assert!(self.root.is_none());
        unsafe {
            // empty tree
            let mut leaf = LeafNode::<K, V>::alloc();
            self.root = Some(leaf.to_root_ptr());
            self.len = 1;
            &mut *leaf.insert_no_split_with_idx(0, key, value)
        }
    }

    /// return Some(leaf)
    #[inline(always)]
    pub fn search_leaf_with_cache<'a, S: Stats<K>, F>(
        &self, stats: &'a S, search: F,
    ) -> (Option<LeafNode<K, V>>, S::PathBufferRef<'a>)
    where
        F: FnOnce(InterNode<K>, &S::PathBufferRef<'a>) -> LeafNode<K, V>,
    {
        if let Some(root) = self.root {
            if !Node::<K, V>::root_is_leaf(root) {
                let _root = InterNode::<K>::from(root);
                let cache = stats.get_cache(_root.height() as u8);
                (Some(search(_root, &cache)), cache)
            } else {
                (Some(LeafNode::<K, V>::from_root_ptr(root)), stats.get_cache(0))
            }
        } else {
            (None, stats.get_cache(0))
        }
    }

    /// return Some(leaf)
    #[inline(always)]
    pub fn search_leaf_with<F>(&self, search: F) -> Option<LeafNode<K, V>>
    where
        F: FnOnce(InterNode<K>) -> LeafNode<K, V>,
    {
        let root = self.root?;
        if !Node::<K, V>::root_is_leaf(root) {
            let _root = InterNode::<K>::from(root);
            Some(search(_root))
        } else {
            Some(LeafNode::<K, V>::from_root_ptr(root))
        }
    }

    /// Handle leaf node underflow by merging with sibling
    /// Uses PathBuffer to accelerate parent lookup
    /// Following the try_merge strategy from Designer Notes:
    /// - Try merge with left sibling (if left + current <= cap)
    /// - Try merge with right sibling (if current + right <= cap)
    /// - Try 3-node merge (if left + current + right <= 2 * cap)
    pub fn handle_leaf_underflow<C: PathBuffer<K>>(
        &mut self, cache: &C, mut leaf: LeafNode<K, V>, try_merge: bool,
    ) {
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
        if try_merge {
            if !can_unlink && let Some(mut left_node) = leaf.get_left_node() {
                let left_count = left_node.key_count();
                if left_count + cur_count <= cap {
                    trace_log!(
                        "handle_leaf_underflow {leaf:?} merge left {left_node:?} {cur_count}"
                    );
                    leaf.copy_left(&mut left_node, cur_count);
                    can_unlink = true;
                    #[cfg(all(test, feature = "trace_log"))]
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
                    #[cfg(all(test, feature = "trace_log"))]
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
                #[cfg(all(test, feature = "trace_log"))]
                {
                    self.triggers |=
                        TestFlag::LeafMergeLeft as u32 | TestFlag::LeafMergeRight as u32;
                }
            }
        }
        if !can_unlink {
            return;
        }
        cache.dec_leaf_count();
        let right_sep = if merge_right {
            let right_node = leaf.get_right_node().unwrap();
            Some(right_node.clone_first_key())
        } else {
            None
        };
        let no_right = leaf.unlink().is_null();
        leaf.dealloc::<false>();
        let (mut parent, mut idx) = cache.pop_path().unwrap();
        trace_log!("handle_leaf_underflow pop parent {parent:?}:{idx}");
        if parent.key_count() == 0 {
            if let Some((grand, grand_idx)) = self.remove_only_child(cache, parent) {
                trace_log!("handle_leaf_underflow remove_only_child until {grand:?}:{grand_idx}");
                parent = grand;
                idx = grand_idx;
            } else {
                trace_log!("handle_leaf_underflow remove_only_child all");
                return;
            }
        }
        self.remove_child_from_inter(cache, &mut parent, idx, right_sep, no_right);
        if parent.key_count() <= 1 {
            self.handle_inter_underflow(cache, parent);
        }
    }

    /// Propagate node split up the tree using iteration (non-recursive)
    /// First tries to borrow space from left/right sibling before splitting
    ///
    /// left_ptr: existing child
    /// right_ptr: new_child split from left_ptr
    /// promote_key: sep_key to split left_ptr & right_ptr
    ///
    /// XXX due to borrow issue, we use &self here
    #[inline(always)]
    fn propagate_split<C: PathBuffer<K>>(
        &mut self, cache: &C, mut promote_key: K, mut left_ptr: *mut NodeHeader,
        mut right_ptr: *mut NodeHeader,
    ) -> Result<u32, InterNode<K>> {
        let mut height = 0;
        #[allow(unused_mut)]
        let mut flags = 0;
        // If we have parent nodes in cache, process them iteratively
        while let Some((mut parent, idx)) = cache.pop_path() {
            if !parent.is_full() {
                trace_log!("propagate_split normal {parent:?}:{idx} insert {right_ptr:p}");
                // should insert next to left_ptr
                parent.insert_no_split_with_idx(idx, promote_key, right_ptr);
                return Ok(flags);
            } else {
                // Parent is full, try to borrow space from sibling through grand_parent
                if let Some((mut grand, grand_idx)) = cache.peek_parent() {
                    // Try to borrow from left sibling of parent
                    if grand_idx > 0 {
                        let mut left_parent = grand.get_child_as_inter(grand_idx - 1);
                        if !left_parent.is_full() {
                            #[cfg(all(test, feature = "trace_log"))]
                            {
                                flags |= TestFlag::InterMoveLeft as u32;
                            }
                            if idx == 0 {
                                trace_log!(
                                    "propagate_split rotate_left {grand:?}:{} first ->{left_parent:?} left {left_ptr:p} insert {idx} {right_ptr:p}",
                                    grand_idx - 1
                                );
                                // special case: split from first child of parent
                                let demote_key = grand.change_key(grand_idx - 1, promote_key);
                                debug_assert_eq!(parent.get_child_ptr(0), left_ptr);
                                unsafe { (*parent.child_ptr_mut(0)) = right_ptr };
                                left_parent.append(demote_key, left_ptr);
                                #[cfg(all(test, feature = "trace_log"))]
                                {
                                    flags |= TestFlag::InterMoveLeftFirst as u32;
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
                            return Ok(flags);
                        }
                    }
                    // Try to borrow from right sibling of parent
                    if grand_idx < grand.key_count() {
                        let mut right_parent = grand.get_child_as_inter(grand_idx + 1);
                        if !right_parent.is_full() {
                            #[cfg(all(test, feature = "trace_log"))]
                            {
                                flags |= TestFlag::InterMoveRight as u32;
                            }
                            if idx == parent.key_count() {
                                trace_log!(
                                    "propagate_split rotate_right last {grand:?}:{grand_idx} -> {right_parent:?}:0 insert right {right_parent:?}:0 {right_ptr:p}"
                                );
                                // split from last child of parent
                                let demote_key = grand.change_key(grand_idx, promote_key);
                                right_parent.insert_at_front(right_ptr, demote_key);
                                #[cfg(all(test, feature = "trace_log"))]
                                {
                                    flags |= TestFlag::InterMoveRightLast as u32;
                                }
                            } else {
                                trace_log!(
                                    "propagate_split rotate_right {grand:?}:{grand_idx} -> {right_parent:?}:0 insert {parent:?}:{idx} {right_ptr:p}"
                                );
                                parent.rotate_right(&mut grand, grand_idx, &mut right_parent);
                                parent.insert_no_split_with_idx(idx, promote_key, right_ptr);
                            }
                            return Ok(flags);
                        }
                    }
                }
                height += 1;

                // Cannot borrow from siblings, need to split internal node
                let (mut right, _promote_key) = parent.insert_split(promote_key, right_ptr);
                cache.inc_inter_count();

                promote_key = _promote_key;
                right_ptr = right.get_ptr_mut();
                left_ptr = parent.get_ptr_mut();
                #[cfg(all(test, feature = "trace_log"))]
                {
                    flags |= TestFlag::InterSplit as u32;
                }
                // Continue to next parent in cache (loop will pop next parent)
            }
        }
        // XXX We have no use for the PathBuffer for now, will call ensure_cap the next time get_cache
        // cache.ensure_cap(height + 1);
        cache.inc_inter_count();
        // No more parents in cache, create new root
        let new_root =
            InterNode::<K>::new_root(height as u32 + 1, promote_key, left_ptr, right_ptr);

        // to avoid borrow issue, set root outside
        #[cfg(debug_assertions)]
        {
            let mut _old_root = self.root.as_ref().unwrap();
            if height == 0 {
                left_ptr = LeafNode::<K, V>::wrap_root_ptr(left_ptr).as_ptr();
            }
            assert_eq!(_old_root.as_ptr(), left_ptr, "height {}", height + 1);
        }
        Err(new_root)
    }

    /// To simplify the logic, we perform delete first.
    /// return the Some(node) when need to rebalance
    #[inline]
    fn remove_child_from_inter<C: PathBuffer<K>>(
        &mut self, cache: &C, node: &mut InterNode<K>, delete_idx: u32, right_sep: Option<K>,
        _no_right: bool,
    ) {
        debug_assert!(node.key_count() > 0, "{:?} {}", node, node.key_count());
        if delete_idx == node.key_count() {
            trace_log!("remove_child_from_inter {node:?}:{delete_idx} last");
            #[cfg(all(test, feature = "trace_log"))]
            {
                self.triggers |= TestFlag::RemoveChildLast as u32;
            }
            // delete the last child of this node
            node.remove_last_child();
            if let Some(key) = right_sep
                && let Some((mut grand_parent, grand_idx)) =
                    cache.peek_ancestor(|_node: &InterNode<K>, idx: u32| -> bool {
                        _node.key_count() > idx
                    })
            {
                #[cfg(all(test, feature = "trace_log"))]
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
            #[cfg(all(test, feature = "trace_log"))]
            {
                self.triggers |= TestFlag::RemoveChildMid as u32;
            }
            // sep key of right node shift left
            if let Some(key) = right_sep {
                trace_log!("remove_child_from_inter change_key {node:?}:{}", delete_idx - 1);
                node.change_key(delete_idx - 1, key);
                #[cfg(all(test, feature = "trace_log"))]
                {
                    self.triggers |= TestFlag::UpdateSepKey as u32;
                }
            }
        } else {
            trace_log!("remove_child_from_inter {node:?}:{delete_idx} first");
            // delete_idx is the first but not the last
            let mut sep_key = node.remove_first_child();
            #[cfg(all(test, feature = "trace_log"))]
            {
                self.triggers |= TestFlag::RemoveChildFirst as u32;
            }
            if let Some(key) = right_sep {
                sep_key = key;
            }
            self.update_ancestor_sep_key::<false, C>(cache, sep_key);
        }
    }

    #[inline]
    pub(crate) fn handle_inter_underflow<C: PathBuffer<K>>(
        &mut self, cache: &C, mut node: InterNode<K>,
    ) {
        let cap = InterNode::<K>::cap();
        let mut root_height = 0;
        let mut _flags = 0;
        cache.assert_center();
        while node.key_count() <= InterNode::<K>::UNDERFLOW_CAP {
            if node.key_count() == 0 {
                if root_height == 0 {
                    root_height = self.get_root_unwrap().height();
                }
                let node_height = node.height();
                // XXX with peek_ancestor we can determine whether the tree
                // only a high link with only left child. Is it necessary?
                // I guess remove_range delay the underflow might make it possible.
                if node_height == root_height
                    || cache
                        .peek_ancestor(|_node: &InterNode<K>, _idx: u32| -> bool {
                            _node.key_count() > 0
                        })
                        .is_none()
                {
                    let child_ptr = unsafe { *node.child_ptr(0) };
                    debug_assert!(!child_ptr.is_null());
                    let root = if node_height == 1 {
                        LeafNode::<K, V>::wrap_root_ptr(child_ptr)
                    } else {
                        unsafe { NonNull::new_unchecked(child_ptr) }
                    };
                    trace_log!(
                        "handle_inter_underflow downgrade root {:?}",
                        Node::<K, V>::from_root_ptr(root)
                    );
                    let _old_root = self.root.replace(root);
                    debug_assert!(_old_root.is_some());

                    while let Some((parent, _)) = cache.pop_path() {
                        parent.dealloc::<false>();
                        cache.dec_inter_count();
                    }
                    node.dealloc::<false>(); // they all have no key
                    cache.dec_inter_count();
                }
                break;
            } else {
                if let Some((mut grand, grand_idx)) = cache.pop_path() {
                    if grand_idx > 0 {
                        let mut left = grand.get_child_as_inter(grand_idx - 1);
                        // the sep key should pull down,  key+1 + key + 1 > cap + 1
                        if left.key_count() + node.key_count() < cap {
                            #[cfg(all(test, feature = "trace_log"))]
                            {
                                _flags |= TestFlag::InterMergeLeft as u32;
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
                            #[cfg(all(test, feature = "trace_log"))]
                            {
                                _flags |= TestFlag::InterMergeRight as u32;
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
                let _ = cache;
                break;
            }
        }
        #[cfg(all(test, feature = "trace_log"))]
        {
            self.triggers |= _flags;
        }
    }

    #[inline]
    fn remove_only_child<C: PathBuffer<K>>(
        &mut self, cache: &C, node: InterNode<K>,
    ) -> Option<(InterNode<K>, u32)> {
        debug_assert_eq!(node.key_count(), 0);
        #[cfg(all(test, feature = "trace_log"))]
        {
            self.triggers |= TestFlag::RemoveOnlyChild as u32;
        }
        let r = cache.move_path_to_ancestor(
            |node: &InterNode<K>, _idx: u32| -> bool { node.key_count() != 0 },
            |node| {
                cache.dec_inter_count();
                node.dealloc::<false>();
            },
        );
        node.dealloc::<true>();
        cache.dec_inter_count();
        if r.is_none() {
            // we are empty, my ancestor are all empty and delete by move_to_ancestor
            self.root = None;
        }
        r
    }

    /// update the separate_key in parent after borrowing space from left/right node
    #[inline(always)]
    pub fn update_ancestor_sep_key<const MOVE: bool, C: PathBuffer<K>>(
        &mut self, cache: &C, sep_key: K,
    ) {
        // if idx == 0, this is the leftmost ptr in the InterNode, we go up until finding a
        // split key
        let ret = if MOVE {
            cache.move_path_to_ancestor(|_node, idx| -> bool { idx > 0 }, dummy_post_callback)
        } else {
            cache.peek_ancestor(|_node, idx| -> bool { idx > 0 })
        };
        if let Some((mut parent, parent_idx)) = ret {
            trace_log!("update_ancestor_sep_key move={MOVE} at {parent:?}:{}", parent_idx - 1);
            parent.change_key(parent_idx - 1, sep_key);
            #[cfg(all(test, feature = "trace_log"))]
            {
                self.triggers |= TestFlag::UpdateSepKey as u32;
            }
        }
    }

    /// Insert with split handling - called when leaf is full
    pub fn insert_with_split<C: PathBuffer<K>>(
        &mut self, cache: &C, key: K, value: V, mut leaf: LeafNode<K, V>, idx: u32,
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
                #[cfg(all(test, feature = "trace_log"))]
                {
                    self.triggers |= TestFlag::LeafMoveLeft as u32;
                }
                self.update_ancestor_sep_key::<true, C>(cache, leaf.clone_first_key());
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
            #[cfg(all(test, feature = "trace_log"))]
            {
                self.triggers |= TestFlag::LeafMoveRight as u32;
            }
            cache.move_path_right();
            self.update_ancestor_sep_key::<true, C>(cache, right_node.clone_first_key());
            return val_p;
        }
        #[cfg(all(test, feature = "trace_log"))]
        {
            self.triggers |= TestFlag::LeafSplit as u32;
        }
        let (mut new_leaf, ptr_v) = leaf.insert_with_split(idx, key, value);
        let split_key = unsafe { (*new_leaf.key_ptr(0)).assume_init_ref().clone() };

        let ptr_v = if self.root_is_inter() {
            match self.propagate_split(cache, split_key, leaf.get_ptr_mut(), new_leaf.get_ptr_mut())
            {
                Ok(_flags) => {
                    #[cfg(all(test, feature = "trace_log"))]
                    {
                        self.triggers |= _flags;
                    }
                }
                Err(new_root) => {
                    self.root.replace(new_root.to_root_ptr());
                }
            }
            ptr_v
        } else {
            let new_root =
                InterNode::<K>::new_root(1, split_key, leaf.get_ptr_mut(), new_leaf.get_ptr_mut());
            let _old_root = self.root.replace(new_root.to_root_ptr());
            debug_assert_eq!(_old_root.unwrap(), leaf.to_root_ptr());
            ptr_v
        };
        cache.inc_leaf_count();
        ptr_v
    }

    #[cfg(all(test, feature = "trace_log"))]
    pub fn print_trigger_flags(&self) {
        let mut s = alloc::string::String::from("");
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
        let mut s = alloc::string::String::from("");
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

    /// Validate the entire tree structure
    /// Uses the same traversal logic as Drop to avoid recursion
    pub fn validate<S: Stats<K>>(&self)
    where
        K: Debug,
        V: Debug,
    {
        let root = if let Some(_root) = self.get_root() {
            _root
        } else {
            assert_eq!(self.len, 0, "Empty tree should have len 0");
            return;
        };
        let mut total_keys = 0usize;
        let mut prev_leaf_max: Option<K> = None;

        match root {
            Node::Leaf(leaf) => {
                total_keys += leaf.validate(None, None);
            }
            Node::Inter(inter) => {
                // Do not use btree internal PathBuffer (might distrupt test scenario)
                let stats = S::default();
                let cache = stats.get_cache(inter.height() as u8);
                let mut cur = inter.clone();
                loop {
                    cache.push_path(cur.clone(), 0);
                    cur.validate();
                    match cur.get_child::<V>(0) {
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
                    cache.move_path_right_and_pop_l1(dummy_post_callback::<K>)
                {
                    cache.push_path(parent.clone(), idx);
                    if let Node::Leaf(leaf) = parent.get_child::<V>(idx) {
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
                        panic!("{parent:?} child {:?} is not leaf", parent.get_child::<V>(idx));
                    }
                }
            }
        }
        assert_eq!(
            total_keys, self.len,
            "Total keys in tree ({}) doesn't match len ({})",
            total_keys, self.len
        );
    }
}
