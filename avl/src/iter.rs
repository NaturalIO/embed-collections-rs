use super::*;
use core::marker::PhantomData;
use core::ptr::null_mut;
use pointers::Pointer;

pub struct AvlIntoIter<P: Pointer, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    node: *mut P::Target,
    dir: Dir,
    _phan: PhantomData<fn(&Tag)>,
}

impl<P, Tag> AvlIntoIter<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    pub(crate) fn new(root: *mut P::Target, dir: Dir) -> Self {
        Self { node: root, dir, _phan: Default::default() }
    }
}

impl<P, Tag> Iterator for AvlIntoIter<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    type Item = P;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if !self.node.is_null() {
            unsafe {
                // self.node was the parent of last visited node
                let item =
                    AvlTree::<P, Tag>::bottom_child(NonNull::new_unchecked(self.node), self.dir);
                let _node = item.as_ref().get_node();
                let right_child = _node.get_child(self.dir.reverse());
                let parent = _node.get_parent();
                _node.detach();
                if !parent.is_null() {
                    if right_child.is_null() {
                        (*parent).get_node().set_child(self.dir, null_mut());
                        self.node = parent;
                    } else {
                        (*parent).get_node().set_child2::<P>(self.dir, right_child, parent);
                        self.node = right_child;
                    }
                } else {
                    // I'm the root
                    if !right_child.is_null() {
                        self.node = right_child;
                        (*right_child).get_node().parent = null_mut();
                    } else {
                        self.node = null_mut();
                    }
                }
                Some(P::from_raw(item.as_ptr()))
            }
        } else {
            None
        }
    }
}

impl<P, Tag> Drop for AvlIntoIter<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    fn drop(&mut self) {
        if self.node.is_null() {
            return;
        }
        for _node in self.by_ref() {}
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
    cur: Option<NonNull<P::Target>>,
    dir: Dir,
    left: usize,
    _phan: PhantomData<fn(&'a P, &'a Tag)>,
}

/// A lending iterator for AvlTree
///
/// The iterator yield [AvlNodeRef], so that you can clone the reference if it's `Arc`
impl<'a, P, Tag> AvlIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub(crate) fn new(
        tree: &'a AvlTree<P, Tag>, init: Option<NonNull<P::Target>>, dir: Dir,
    ) -> Self {
        Self { cur: init, dir, left: tree.len(), _phan: Default::default() }
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
    type Item = AvlNodeRef<'a, P>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let cur: NonNull<P::Target> = self.cur.take()?;
        self.left -= 1;
        self.cur = AvlTree::<P, Tag>::_walk_dir(cur, self.dir);
        Some(AvlNodeRef::<'a, P>::new(cur.as_ptr()))
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
