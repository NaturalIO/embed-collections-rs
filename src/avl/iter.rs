use super::*;
use crate::Pointer;
use core::ptr::null;

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
