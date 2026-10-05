use super::inter::*;

pub(super) fn dummy_post_callback<K: Ord>(_node: InterNode<K>) {}

macro_rules! _move_to_ancestor {
    ($queue: expr, $pop: ident, $cond: expr, $post: expr) => {{
        let mut res = None;
        // For dropping scenario, cannot move further, reach the end at root
        while let Some((grand_parent, idx)) = $queue.$pop() {
            if $cond(&grand_parent, idx) {
                res.replace((grand_parent, idx));
                break;
            } else {
                ($post)(grand_parent);
            }
        }
        // grand_parent idx reach the end, will not visit again
        res
    }};
}

#[allow(private_bounds)]
pub(super) trait PathBuffer<K: Ord>: Sized {
    type Iter<'a>: Iterator<Item = (&'a InterNode<K>, u32)>
    where
        Self: 'a,
        K: 'a;

    // --- stats method begins ---
    // methods should belong to Stats, but we put here due to borrow checker issues
    fn inc_leaf_count(&self);

    fn dec_leaf_count(&self);

    fn inc_inter_count(&self);

    fn dec_inter_count(&self);

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8;

    fn ensure_cap(&self, height: u8);

    fn buffer_pos(&self) -> i8;

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    fn move_pos(&self, delta: i8);

    /// Push one entry onto the cache stack, growing the buffer if needed.
    fn _push(&self, inter: InterNode<K>, idx: u32);

    /// Pop the top entry from the cache stack.
    fn _pop(&self) -> Option<(InterNode<K>, u32)>;

    /// Reverse (top → bottom) iterator over the stack without consuming it.
    fn iter<'a>(&'a self) -> Self::Iter<'a>;

    /// Peek at the top of the stack (equivalent to `Various::last`).
    fn last(&self) -> Option<(&InterNode<K>, u32)>;

    #[inline(always)]
    fn assert_center(&self) {
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline]
    fn _move_left_and_pop<F>(&self, post_callback: F) -> Option<(InterNode<K>, u32)>
    where
        F: Fn(InterNode<K>),
    {
        while let Some((parent, idx)) = self._pop() {
            let pos = self.buffer_pos();
            debug_assert!(pos < 0);
            let move_step = (-pos) as u8;
            if idx > 0 {
                if move_step as u32 > idx {
                    self.move_pos(idx as i8);
                } else {
                    self.move_pos(move_step as i8);
                    return Some((parent, idx - (move_step as u32))); // have common parent
                }
            }
            // only move 1 since we change the branch, leave the rest to the loop
            self.move_pos(1);
            let pre_height = parent.height();
            post_callback(parent);
            let cond = |_node: &InterNode<K>, idx: u32| -> bool { idx > 0 };
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
                    self._push(parent, idx);
                }
            } else {
                return None;
            }
        }
        None
    }

    /// Return the last parent
    #[inline]
    fn _move_right_and_pop<F>(&self, post_callback: F) -> Option<(InterNode<K>, u32)>
    where
        F: Fn(InterNode<K>),
    {
        // move of the time move_step is just 1
        while let Some((parent, idx)) = self._pop() {
            let move_step = self.buffer_pos();
            debug_assert!(move_step > 0);
            let right_count = parent.key_count() - idx;
            if right_count > 0 {
                if right_count < move_step as u32 {
                    self.move_pos(-(right_count as i8));
                } else {
                    self.move_pos(-move_step);
                    debug_assert_eq!(self.buffer_pos(), 0);
                    return Some((parent, idx + move_step as u32)); // have common parent
                }
            }
            // parent idx reach the end, will not visit again
            let pre_height = parent.height();
            self.move_pos(-1);
            post_callback(parent);
            // only move 1 since we change the branch, leave the rest to the loop
            if let Some((grand_parent, grand_idx)) = _move_to_ancestor!(
                self,
                _pop,
                |node: &InterNode<K>, idx: u32| -> bool { node.key_count() > idx },
                post_callback
            ) {
                let (parent, idx) =
                    grand_parent.find_child_branch(pre_height, grand_idx + 1, true, Some(self));
                if self.buffer_pos() == 0 {
                    return Some((parent, idx));
                } else {
                    // continue to move right
                    self._push(parent, idx);
                }
            } else {
                return None;
            }
        }
        None
    }

    #[inline(always)]
    fn peek_parent(&self) -> Option<(InterNode<K>, u32)> {
        self.assert_center();
        let (parent, idx) = self.last()?;
        Some((parent.clone(), idx))
    }

    /// iter backward through cache internal stack, without changing the cache,
    /// return None if reaches root
    #[inline(always)]
    fn peek_ancestor<FC>(&self, cond: FC) -> Option<(InterNode<K>, u32)>
    where
        FC: Fn(&InterNode<K>, u32) -> bool,
    {
        self.fix_path_center();
        let iter = self.iter();
        // For dropping scenario, cannot move further, reach the end at root
        for (grand_parent, idx) in iter {
            if cond(grand_parent, idx) {
                return Some((grand_parent.clone(), idx));
            }
        }
        // grand_parent idx reach the end, will not visit again
        None
    }

    /// pop cache until `cond` condition is met.
    /// return None if reaches root
    #[inline(always)]
    fn move_path_to_ancestor<FC, FP>(
        &self, cond: FC, post_callback: FP,
    ) -> Option<(InterNode<K>, u32)>
    where
        FC: Fn(&InterNode<K>, u32) -> bool,
        FP: Fn(InterNode<K>),
    {
        // Self::pop() will detect pos and fix position
        _move_to_ancestor!(self, pop_path, cond, post_callback)
    }

    /// For moving the Entry position
    #[inline(always)]
    fn move_path_left(&self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        if self.buffer_pos() > i8::MIN {
        } else {
            self._fix_center_from_left();
        }
        self.move_pos(-1);
    }

    /// For moving the Entry position
    #[inline(always)]
    fn move_path_right(&self) {
        // We delay the cache adjustment until pop because may not need to visit the parent
        if self.buffer_pos() < i8::MAX {
        } else {
            self._fix_center_from_right();
        }
        self.move_pos(1);
    }

    #[inline(always)]
    fn _fix_center_from_left(&self) {
        debug_assert!(self.buffer_pos() < 0);
        if let Some((parent, idx)) = self._move_left_and_pop(dummy_post_callback::<K>) {
            self._push(parent, idx);
        }
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline(always)]
    fn _fix_center_from_right(&self) {
        debug_assert!(self.buffer_pos() > 0);
        if let Some((parent, idx)) = self._move_right_and_pop(dummy_post_callback::<K>) {
            self._push(parent, idx);
        }
        debug_assert_eq!(self.buffer_pos(), 0);
    }

    #[inline(always)]
    fn fix_path_center(&self) {
        let pos = self.buffer_pos();
        if pos == 0 { // most frequent path
        } else if pos > 0 {
            self._fix_center_from_right();
        } else {
            debug_assert!(pos < 0);
            self._fix_center_from_left();
        }
    }

    #[inline(always)]
    fn push_path(&self, inter: InterNode<K>, idx: u32) {
        self.assert_center();
        self._push(inter, idx);
    }

    /// pop parent and its idx from cache, if we need new_root, return None
    #[inline(always)]
    fn pop_path(&self) -> Option<(InterNode<K>, u32)> {
        let pos = self.buffer_pos();
        if pos == 0 {
            self._pop()
        } else if pos > 0 {
            self._move_right_and_pop(dummy_post_callback::<K>)
        } else {
            debug_assert!(pos < 0);
            self._move_left_and_pop(dummy_post_callback::<K>)
        }
    }

    // for dropping the tree, post order visit, `post_callback` should dealloc on the node
    #[inline(always)]
    fn move_path_right_and_pop_l1<F>(&self, post_callback: F) -> Option<(InterNode<K>, u32)>
    where
        F: Fn(InterNode<K>) + Clone,
    {
        if self.buffer_pos() < i8::MAX {
        } else {
            self._fix_center_from_right();
        }
        self.move_pos(1);
        self._move_right_and_pop(post_callback)
    }

    // for dropping the tree, post order visit in reversed order, `post_callback` should dealloc on the node
    #[inline(always)]
    fn move_path_left_and_pop_l1<F>(&self, post_callback: F) -> Option<(InterNode<K>, u32)>
    where
        F: Fn(InterNode<K>) + Clone,
    {
        if self.buffer_pos() > i8::MIN {
        } else {
            self._fix_center_from_left();
        }
        self.move_pos(-1);
        self._move_left_and_pop(post_callback)
    }

    #[cfg(test)]
    fn to_vec(&self) -> alloc::vec::Vec<(InterNode<K>, u32)> {
        let mut v = alloc::vec::Vec::new();
        for (parent, idx) in self.iter() {
            v.push((parent.clone(), idx));
        }
        v
    }
}

impl<'b, K: Ord, T: PathBuffer<K> + Sized> PathBuffer<K> for &'b T {
    type Iter<'a>
        = T::Iter<'a>
    where
        Self: 'a,
        K: 'a;

    // --- stats method begins ---
    // methods should belong to Stats, but we put here due to borrow checker issues

    fn inc_leaf_count(&self) {
        T::inc_leaf_count(self)
    }

    fn dec_leaf_count(&self) {
        T::dec_leaf_count(self)
    }

    fn inc_inter_count(&self) {
        T::inc_inter_count(self)
    }

    fn dec_inter_count(&self) {
        T::dec_inter_count(self)
    }

    // --- stats method ends ---

    /// The count of current level items cotains by the PathBuffer
    fn buffer_len(&self) -> u8 {
        T::buffer_len(self)
    }

    fn ensure_cap(&self, height: u8) {
        T::ensure_cap(self, height)
    }

    fn buffer_pos(&self) -> i8 {
        T::buffer_pos(self)
    }

    /// The delta position of current entry to the PathBuffer.
    /// < 0 for left, > 0 for right, ==0 for center
    fn move_pos(&self, delta: i8) {
        T::move_pos(self, delta)
    }

    /// Push one entry onto the cache stack, growing the buffer if needed.
    fn _push(&self, inter: InterNode<K>, idx: u32) {
        T::_push(self, inter, idx)
    }

    /// Pop the top entry from the cache stack.
    fn _pop(&self) -> Option<(InterNode<K>, u32)> {
        T::_pop(self)
    }

    /// Reverse (top → bottom) iterator over the stack without consuming it.
    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        T::iter(self)
    }

    /// Peek at the top of the stack (equivalent to `Various::last`).
    fn last(&self) -> Option<(&InterNode<K>, u32)> {
        T::last(self)
    }
}
