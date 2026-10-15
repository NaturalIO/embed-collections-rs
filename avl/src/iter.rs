use super::*;
use core::ptr::null_mut;
use pointers::Pointer;

// TODO IntoIter

pub struct AvlDrain<'a, P: Pointer, Tag>
where
    P::Target: AvlItem<Tag>,
{
    tree: &'a mut AvlTree<P, Tag>,
    parent: *mut P::Target,
    dir: Option<Dir>,
}

impl<'a, P: Pointer, Tag> AvlDrain<'a, P, Tag>
where
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub(super) fn new(tree: &'a mut AvlTree<P, Tag>) -> Self {
        Self { tree, parent: null_mut(), dir: None }
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

        let mut node: *mut P::Target;
        let parent: *mut P::Target;

        if self.dir.is_none() && self.parent.is_null() {
            // Initial call: find the leftmost node
            let mut curr = self.tree.root;
            loop {
                let left = unsafe { (*curr).get_node().left() };
                if !left.is_null() {
                    curr = left;
                } else {
                    break;
                }
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

            if child_dir == DIR_RIGHT || unsafe { (*parent).get_node().right().is_null() } {
                node = parent;
            } else {
                // Finished left, go to right sibling
                node = unsafe { (*parent).get_node().right() };
                loop {
                    let left = unsafe { (*node).get_node().left() };
                    if !left.is_null() {
                        node = left;
                    } else {
                        break;
                    }
                }
            }
        }
        let right = unsafe { (*node).get_node().right() };

        // Goto check_right_side logic
        if !right.is_null() {
            // It has a right child, so we must yield that first (in post-order)
            // Note: in AVL, if left is null, right must be a leaf.
            node = right;
        }

        // Determine next state
        let next_parent = unsafe { (*node).get_node().parent };
        if next_parent.is_null() {
            self.tree.root = null_mut();
            self.parent = null_mut();
            self.dir = Some(DIR_LEFT);
        } else {
            self.parent = next_parent;
            let next_parent_node = unsafe { (*next_parent).get_node() };
            let _dir = next_parent_node._child_direction(node);
            // Unlink from parent NOW
            next_parent_node.set_child(_dir, null_mut());
            self.dir = Some(_dir);
        }

        self.tree.count -= 1;
        unsafe {
            (*node).get_node().detach();
            Some(P::from_raw(node))
        }
    }
}

/// Return a reference of P (you can P.clone() of P has Clone)
///
/// # Example
///
/// ```rust
/// use embed_avl::{AvlTree, AvlItem, AvlNode, impl_ord_with_borrow};
/// use core::cell::UnsafeCell;
/// use core::cmp::Ordering;
/// use core::borrow::Borrow;
/// extern crate alloc;
/// use alloc::sync::Arc;
///
/// #[derive(format_attr::DebugAttr)]
/// #[fmt("MyNode {value}")]
/// struct MyNode {
///     value: i32,
///     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
/// }
///
/// impl Borrow<i32> for MyNode {
///     fn borrow(&self) -> &i32 {
///         &self.value
///     }
/// }
///
/// unsafe impl AvlItem<()> for MyNode {
///     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
///         unsafe { &mut *self.avl_node.get() }
///     }
/// }
/// impl_ord_with_borrow!(MyNode, i32);
///
/// let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
///
/// let new_node = | n: i32| {
///     Arc::new(MyNode { value: n, avl_node: UnsafeCell::new(Default::default()) })
/// };
/// tree.add(new_node(1)).expect("add");
/// tree.add(new_node(2)).expect("add");
/// tree.add(new_node(3)).expect("add");
/// assert_eq!(tree.len(), 3);
///
/// let mut iter = tree.iter_rev();
/// let mut all_nodes_rev = Vec::with_capacity(tree.len());
/// while let Some(node) = iter.next() {
///     all_nodes_rev.push(node.clone_ref());
/// }
/// ```
pub struct AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    tree: &'a AvlTree<P, Tag>,
    cur: Option<NonNull<P::Target>>,
    dir: Dir,
    left: usize,
}

/// A lending iterator for AvlTree
///
/// The iterator yield [NodeRef], so that you can clone the reference if it's `Arc`
impl<'a, P, Tag> AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub(crate) fn new(
        tree: &'a AvlTree<P, Tag>, init: Option<NonNull<P::Target>>, dir: Dir,
    ) -> Self {
        Self { tree, cur: init, dir, left: tree.len() }
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
    type Item = NodeRef<'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        let cur: NonNull<P::Target> = self.cur.take()?;
        self.left -= 1;
        self.cur = self.tree._walk_dir(cur, self.dir);
        Some(NodeRef::<'a, P>::new(cur.as_ptr()))
    }
}

impl<'a, P, Tag> ExactSizeIterator for AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    fn len(&self) -> usize {
        self.left
    }
}
