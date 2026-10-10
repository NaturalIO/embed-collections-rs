use super::inter::*;
use super::node::NodeBase;
use core::marker::PhantomData;

pub(super) fn dummy_post_callback<K, C>(_cache: &mut C, _node: InterNode<K>) {}

macro_rules! _move_to_ancestor {
    ($queue: expr, $pop: ident, $cond: expr, $post: expr) => {{
        let mut res = None;
        // For dropping scenario, cannot move further, reach the end at root
        while let Some((_grand_parent, idx)) = $queue.$pop() {
            let grand_parent = InterNode::from(_grand_parent);
            if $cond(&grand_parent, idx) {
                res.replace((grand_parent, idx));
                break;
            } else {
                ($post)($queue, grand_parent);
            }
        }
        // grand_parent idx reach the end, will not visit again
        res
    }};
}

pub(crate) trait PathBuffer: Sized {
    // --- stats method begins ---
    // methods should belong to Stats, but we put here due to borrow checker issues
    fn inc_leaf_count(&mut self);

    fn dec_leaf_count(&mut self);

    fn inc_inter_count(&mut self);

    fn dec_inter_count(&mut self);

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8;

    fn buffer_pos(&self) -> i8;

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    fn move_pos(&mut self, delta: i8);

    /// Push one entry onto the cache stack, growing the buffer if needed.
    fn _push(&mut self, inter: NodeBase, idx: u8);

    /// Pop the top entry from the cache stack.
    fn _pop(&mut self) -> Option<(NodeBase, u8)>;

    unsafe fn _get_unchecked(&self, idx: u8) -> (NodeBase, u8);

    /// Reverse (bottom->top) iterator over the stack without consuming it.
    #[inline]
    fn iter<'a, K>(&'a self) -> PathBufferIter<'a, K, Self> {
        PathBufferIter { idx: self.buffer_len(), buf: self, _phan: Default::default() }
    }

    /// Peek at the last item (parent)
    #[inline]
    fn last<K>(&self) -> Option<(InterNode<K>, u8)> {
        let i = self.buffer_len();
        if i > 0 {
            let (node, idx) = unsafe { self._get_unchecked(i - 1) };
            Some((InterNode::<K>::from(node), idx))
        } else {
            None
        }
    }

    #[inline(always)]
    fn assert_center(&self) {
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline]
    fn _move_left_and_pop<K: Ord, F>(&mut self, mut post_callback: F) -> Option<(InterNode<K>, u8)>
    where
        F: FnMut(&mut Self, InterNode<K>),
    {
        while let Some((_parent, idx)) = self._pop() {
            let parent = InterNode::<K>::from(_parent);
            let pos = self.buffer_pos();
            debug_assert!(pos < 0);
            let move_step = (-pos) as u8;
            if idx > 0 {
                if move_step > idx {
                    self.move_pos(idx as i8);
                } else {
                    self.move_pos(move_step as i8);
                    return Some((parent, idx - move_step)); // have common parent
                }
            }
            // only move 1 since we change the branch, leave the rest to the loop
            self.move_pos(1);
            let pre_height = parent.height();
            post_callback(self, parent);
            let cond = |_node: &InterNode<K>, idx: u8| -> bool { idx > 0 };
            // this is for entry API, we already know there is a previous node
            if let Some((grand_parent, grand_idx)) =
                _move_to_ancestor!(self, _pop, cond, post_callback)
            {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx - 1, false, Some(self));
                if self.buffer_pos() == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move left
                    self._push(parent.into(), idx);
                }
            } else {
                return None;
            }
        }
        None
    }

    /// Return the last parent
    #[inline]
    fn _move_right_and_pop<K: Ord, F>(&mut self, mut post_callback: F) -> Option<(InterNode<K>, u8)>
    where
        F: FnMut(&mut Self, InterNode<K>),
    {
        // move of the time move_step is just 1
        while let Some((_parent, idx)) = self._pop() {
            let parent = InterNode::<K>::from(_parent);
            let move_step = self.buffer_pos();
            debug_assert!(move_step > 0);
            let right_count = parent.key_count() - idx;
            if right_count > 0 {
                if right_count < move_step as u8 {
                    self.move_pos(-(right_count as i8));
                } else {
                    self.move_pos(-move_step);
                    debug_assert_eq!(self.buffer_pos(), 0);
                    return Some((parent, idx + move_step as u8)); // have common parent
                }
            }
            // parent idx reach the end, will not visit again
            let pre_height = parent.height();
            self.move_pos(-1);
            post_callback(self, parent);
            // only move 1 since we change the branch, leave the rest to the loop
            if let Some((grand_parent, grand_idx)) = _move_to_ancestor!(
                self,
                _pop,
                |node: &InterNode<K>, idx: u8| -> bool { node.key_count() > idx },
                post_callback
            ) {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx + 1, true, Some(self));
                if self.buffer_pos() == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move right
                    self._push(parent.into(), idx);
                }
            } else {
                return None;
            }
        }
        None
    }

    #[inline(always)]
    fn peek_parent<K: Ord>(&mut self) -> Option<(InterNode<K>, u8)> {
        self.assert_center();
        let (parent, idx) = self.last::<K>()?;
        Some((parent.clone(), idx))
    }

    /// iter backward through cache internal stack, without changing the cache,
    /// return None if reaches root
    #[inline(always)]
    fn peek_ancestor<K: Ord, FC>(&mut self, cond: FC) -> Option<(InterNode<K>, u8)>
    where
        FC: Fn(&InterNode<K>, u8) -> bool,
    {
        self.fix_path_center::<K>();
        let iter = self.iter::<K>();
        // For dropping scenario, cannot move further, reach the end at root
        for (grand_parent, idx) in iter {
            if cond(&grand_parent, idx) {
                return Some((grand_parent.clone(), idx));
            }
        }
        // grand_parent idx reach the end, will not visit again
        None
    }

    /// pop cache until `cond` condition is met.
    /// return None if reaches root
    #[inline(always)]
    fn move_path_to_ancestor<K: Ord, FC, FP>(
        &mut self, cond: FC, mut post_callback: FP,
    ) -> Option<(InterNode<K>, u8)>
    where
        FC: Fn(&InterNode<K>, u8) -> bool,
        FP: FnMut(&mut Self, InterNode<K>),
    {
        // Self::pop() will detect pos and fix position
        _move_to_ancestor!(self, pop_path, cond, post_callback)
    }

    /// For moving the Entry position
    #[inline(always)]
    fn move_path_left<K: Ord>(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        if self.buffer_pos() > i8::MIN {
        } else {
            self._fix_center_from_left::<K>();
        }
        self.move_pos(-1);
    }

    /// For moving the Entry position
    #[inline(always)]
    fn move_path_right<K: Ord>(&mut self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        if self.buffer_pos() < i8::MAX {
        } else {
            self._fix_center_from_right::<K>();
        }
        self.move_pos(1);
    }

    #[inline(always)]
    fn _fix_center_from_left<K: Ord>(&mut self) {
        debug_assert!(self.buffer_pos() < 0);
        if let Some((parent, idx)) = self._move_left_and_pop::<K, _>(dummy_post_callback::<K, Self>)
        {
            self._push(parent.into(), idx);
        }
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline(always)]
    fn _fix_center_from_right<K: Ord>(&mut self) {
        debug_assert!(self.buffer_pos() > 0);
        if let Some((parent, idx)) =
            self._move_right_and_pop::<K, _>(dummy_post_callback::<K, Self>)
        {
            self._push(parent.into(), idx);
        }
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline(always)]
    fn fix_path_center<K: Ord>(&mut self) {
        let pos = self.buffer_pos();
        if pos == 0 { // most frequent path
        } else if pos > 0 {
            self._fix_center_from_right::<K>();
        } else {
            debug_assert!(pos < 0);
            self._fix_center_from_left::<K>();
        }
    }

    #[inline(always)]
    fn push_path<K>(&mut self, inter: InterNode<K>, idx: u8) {
        self.assert_center();
        self._push(inter.into(), idx);
    }

    /// pop parent and its idx from cache, if we need new_root, return None
    #[inline(always)]
    fn pop_path<K: Ord>(&mut self) -> Option<(InterNode<K>, u8)> {
        let pos = self.buffer_pos();
        if pos == 0 {
            self._pop().map(|(node, idx)| (InterNode::from(node), idx))
        } else if pos > 0 {
            self._move_right_and_pop::<K, _>(dummy_post_callback::<K, Self>)
        } else {
            debug_assert!(pos < 0);
            self._move_left_and_pop::<K, _>(dummy_post_callback::<K, Self>)
        }
    }

    // for dropping the tree, post order visit, `post_callback` should dealloc on the node
    #[inline(always)]
    fn move_path_right_and_pop_l1<K: Ord, F>(
        &mut self, post_callback: F,
    ) -> Option<(InterNode<K>, u8)>
    where
        F: FnMut(&mut Self, InterNode<K>) + Clone,
    {
        if self.buffer_pos() < i8::MAX {
        } else {
            self._fix_center_from_right::<K>();
        }
        self.move_pos(1);
        self._move_right_and_pop::<K, F>(post_callback)
    }

    // for dropping the tree, post order visit in reversed order, `post_callback` should dealloc on the node
    #[inline(always)]
    fn move_path_left_and_pop_l1<K: Ord, F>(
        &mut self, post_callback: F,
    ) -> Option<(InterNode<K>, u8)>
    where
        F: Fn(&mut Self, InterNode<K>) + Clone,
    {
        if self.buffer_pos() > i8::MIN {
        } else {
            self._fix_center_from_left::<K>();
        }
        self.move_pos(-1);
        self._move_left_and_pop::<K, F>(post_callback)
    }

    #[cfg(test)]
    fn to_vec<K>(&self) -> alloc::vec::Vec<(InterNode<K>, u8)> {
        let mut v = alloc::vec::Vec::new();
        for (parent, idx) in self.iter() {
            v.push((parent.clone(), idx));
        }
        v
    }
}

impl<T: PathBuffer + Sized> PathBuffer for &mut T {
    // --- stats method begins ---
    // methods should belong to Stats, but we put here due to borrow checker issues

    fn inc_leaf_count(&mut self) {
        T::inc_leaf_count(self)
    }

    fn dec_leaf_count(&mut self) {
        T::dec_leaf_count(self)
    }

    fn inc_inter_count(&mut self) {
        T::inc_inter_count(self)
    }

    fn dec_inter_count(&mut self) {
        T::dec_inter_count(self)
    }

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        T::buffer_len(self)
    }

    fn buffer_pos(&self) -> i8 {
        T::buffer_pos(self)
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    fn move_pos(&mut self, delta: i8) {
        T::move_pos(self, delta)
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    fn _push(&mut self, inter: NodeBase, idx: u8) {
        T::_push(self, inter, idx)
    }

    /// Pop the top entry from the cache stack.
    fn _pop(&mut self) -> Option<(NodeBase, u8)> {
        T::_pop(self)
    }

    #[inline]
    unsafe fn _get_unchecked(&self, idx: u8) -> (NodeBase, u8) {
        unsafe { T::_get_unchecked(self, idx) }
    }

    /// Reverse (bottom->top) iterator over the stack without consuming it.
    #[inline]
    fn iter<'a, K>(&'a self) -> PathBufferIter<'a, K, Self> {
        PathBufferIter { idx: self.buffer_len(), buf: self, _phan: Default::default() }
    }

    /// Peek at the top of the stack (equivalent to `Various::last`).
    fn last<K>(&self) -> Option<(InterNode<K>, u8)> {
        T::last(self)
    }
}

/// Reverse (top-of-stack → bottom) iterator produced by [`TreeInfo::_iter`].
pub(crate) struct PathBufferIter<'a, K, T: PathBuffer> {
    buf: &'a T,
    idx: u8,
    _phan: PhantomData<fn(&K)>,
}

impl<'a, K, T: PathBuffer> Iterator for PathBufferIter<'a, K, T> {
    type Item = (InterNode<K>, u8);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx > 0 {
            self.idx -= 1;
            let (node, idx) = unsafe { self.buf._get_unchecked(self.idx) };
            Some((InterNode::<K>::from(node), idx))
        } else {
            None
        }
    }
}
