use super::*;
use core::mem::MaybeUninit;
use core::ptr::null;
use pointers::Pointer;

// TODO IntoIter

pub struct AvlDrain<'a, P: Pointer, Tag>
where
    P::Target: AvlItem<Tag>,
{
    tree: &'a mut AvlTree<P, Tag>,
    parent: *const P::Target,
    dir: Option<AvlDirection>,
}

impl<'a, P: Pointer, Tag> AvlDrain<'a, P, Tag>
where
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub(super) fn new(tree: &'a mut AvlTree<P, Tag>) -> Self {
        Self { tree, parent: null(), dir: None }
    }
}

unsafe impl<'a, P, Tag> Send for AvlDrain<'a, P, Tag>
where
    P: Pointer + Send,
    P::Target: AvlItem<Tag>,
{
}

impl<'a, P: Pointer, Tag> Iterator for AvlDrain<'a, P, Tag>
where
    P::Target: AvlItem<Tag>,
{
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tree.root.is_null() {
            return None;
        }

        let mut node: *const P::Target;
        let parent: *const P::Target;

        if self.dir.is_none() && self.parent.is_null() {
            // Initial call: find the leftmost node
            let mut curr = self.tree.root;
            while unsafe { !(*curr).get_node().left.is_null() } {
                curr = unsafe { (*curr).get_node().left };
            }
            node = curr;
        } else {
            parent = self.parent;
            if parent.is_null() {
                // Should not happen if root was nulled
                return None;
            }

            let child_dir = self.dir.unwrap();
            // child_dir child of parent was just nulled in previous call?
            // NO, we null it in THIS call.

            if child_dir == AvlDirection::Right || unsafe { (*parent).get_node().right.is_null() } {
                node = parent;
            } else {
                // Finished left, go to right sibling
                node = unsafe { (*parent).get_node().right };
                while unsafe { !(*node).get_node().left.is_null() } {
                    node = unsafe { (*node).get_node().left };
                }
            }
        }

        // Goto check_right_side logic
        if unsafe { !(*node).get_node().right.is_null() } {
            // It has a right child, so we must yield that first (in post-order)
            // Note: in AVL, if left is null, right must be a leaf.
            node = unsafe { (*node).get_node().right };
        }

        // Determine next state
        let next_parent = unsafe { (*node).get_node().parent };
        if next_parent.is_null() {
            self.tree.root = null();
            self.parent = null();
            self.dir = Some(AvlDirection::Left);
        } else {
            self.parent = next_parent;
            self.dir = Some(self.tree.parent_direction(node, next_parent));
            // Unlink from parent NOW
            unsafe { (*next_parent).get_node().set_child(self.dir.unwrap(), null()) };
        }

        self.tree.count -= 1;
        unsafe {
            (*node).get_node().detach();
            Some(P::from_raw(node))
        }
    }
}

pub struct AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    tree: &'a AvlTree<P, Tag>,
    cur: Option<NonNull<P::Target>>,
    dir: AvlDirection,
    temp: MaybeUninit<P>,
}

/// A lending iterator for AvlTree
///
/// NOTE: If you use the [Iterator] interface (for iteration), you only get &P::Target.
///
/// you can use next_ref() to get &P
impl<'a, P, Tag> AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub(crate) fn new(
        tree: &'a AvlTree<P, Tag>, init: Option<NonNull<P::Target>>, dir: AvlDirection,
    ) -> Self {
        Self { tree, cur: init, dir, temp: MaybeUninit::uninit() }
    }

    /// Return a reference of P (you can P.clone() of P has Clone)
    ///
    /// NOTE: this is a lending iterator.
    /// Unfortunately rust Iterator trait don't let us do this because of lifetime limitation
    ///
    /// # Example
    ///
    /// ```rust
    /// use embed_avl::{AvlTree, AvlItem, AvlNode};
    /// use core::cell::UnsafeCell;
    /// use core::cmp::Ordering;
    /// extern crate alloc;
    /// use alloc::sync::Arc;
    ///
    /// struct MyNode {
    ///     value: i32,
    ///     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
    /// }
    ///
    /// unsafe impl AvlItem<()> for MyNode {
    ///
    ///     type Key = i32;
    ///
    ///     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
    ///         unsafe { &mut *self.avl_node.get() }
    ///     }
    ///
    ///     fn borrow_key(&self) -> &Self::Key {
    ///         &self.value
    ///     }
    /// }
    ///
    /// let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
    ///
    /// let new_node = | n: i32| {
    ///     Arc::new(MyNode { value: n, avl_node: UnsafeCell::new(Default::default()) })
    /// };
    /// tree.add(new_node(1));
    /// tree.add(new_node(2));
    /// tree.add(new_node(3));
    /// assert_eq!(tree.len(), 3);
    ///
    /// let mut iter = tree.iter_rev();
    /// let mut all_nodes_rev = Vec::with_capacity(tree.len());
    /// while let Some(node) = iter.next_ref() {
    ///     all_nodes_rev.push(node.clone());
    /// }
    /// ```
    #[inline]
    pub fn next_ref(&mut self) -> Option<&P> {
        let cur: NonNull<P::Target> = self.cur.take()?;
        self.temp.write(unsafe { P::from_raw(cur.as_ptr()) });
        let p = self.tree.walk_dir(cur, self.dir);
        self.cur = p;
        Some(unsafe { self.temp.assume_init_ref() })
    }
}

unsafe impl<'a, P, Tag> Send for AvlIter<'a, P, Tag>
where
    P: Pointer + Send,
    P::Target: AvlItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    type Item = &'a P::Target;

    fn next(&mut self) -> Option<Self::Item> {
        let cur: NonNull<P::Target> = self.cur.take()?;
        let p = self.tree.walk_dir(cur, self.dir);
        self.cur = p;
        Some(unsafe { cur.as_ref() })
    }
}
