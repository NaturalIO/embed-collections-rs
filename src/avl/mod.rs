//! An intrusive AVL tree implementation.
//!
//! The algorithm origin from open-zfs
//!
//! # Examples
//!
//! ## Using `Box` to search and remove by key
//!
//! ```rust
//! use embed_collections::avl::{AvlTree, AvlItem, AvlNode};
//! use core::cell::UnsafeCell;
//! use core::cmp::Ordering;
//!
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! let mut tree = AvlTree::<Box<MyNode>, ()>::new();
//! tree.add(Box::new(MyNode { value: 10, avl_node: UnsafeCell::new(Default::default()) }), |a, b| a.value.cmp(&b.value));
//!
//! // Search and remove
//! if let Some(node) = tree.remove_by_key(&10, |key, node| key.cmp(&node.value)) {
//!     assert_eq!(node.value, 10);
//! }
//! ```
//!
//! ## Using `Arc` for multiple ownership
//!
//! remove_ref only available to `Arc` and `Rc`
//!
//! ```rust
//! use embed_collections::avl::{AvlTree, AvlItem, AvlNode};
//! use core::cell::UnsafeCell;
//! use std::sync::Arc;
//!
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
//! let node = Arc::new(MyNode { value: 42, avl_node: UnsafeCell::new(Default::default()) });
//!
//! tree.add(node.clone(), |a, b| a.value.cmp(&b.value));
//! assert_eq!(tree.get_count(), 1);
//!
//! // Remove by reference (detach from avl tree)
//! tree.remove_ref(&node);
//! assert_eq!(tree.get_count(), 0);
//! ```
//!

mod iter;
pub use iter::*;
#[cfg(test)]
mod tests;

use crate::Pointer;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::{
    cmp::{Ordering, PartialEq},
    fmt, mem,
    ptr::{NonNull, null},
};

/// A trait to return internal mutable AvlNode for specified list.
///
/// The tag is used to distinguish different AvlNodes within the same item,
/// allowing an item to belong to multiple lists simultaneously.
/// For only one ownership, you can use `()`.
///
/// # Safety
///
/// Implementors must ensure `get_node` returns a valid reference to the `AvlNode`
/// embedded within `Self`. Users must use `UnsafeCell` to hold `AvlNode` to support
/// interior mutability required by list operations.
pub unsafe trait AvlItem<Tag>: Sized {
    fn get_node(&self) -> &mut AvlNode<Self, Tag>;
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum AvlDirection {
    Left = 0,
    Right = 1,
}

impl AvlDirection {
    #[inline(always)]
    fn reverse(self) -> AvlDirection {
        match self {
            AvlDirection::Left => AvlDirection::Right,
            AvlDirection::Right => AvlDirection::Left,
        }
    }
}

macro_rules! avlchild_to_balance {
    ( $dir: expr ) => {
        match $dir {
            AvlDirection::Left => -1,
            AvlDirection::Right => 1,
        }
    };
}

pub struct AvlNode<T: Sized, Tag> {
    pub left: *const T,
    pub right: *const T,
    pub parent: *const T,
    pub balance: i8,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T, Tag> Send for AvlNode<T, Tag> {}

impl<T: AvlItem<Tag>, Tag> AvlNode<T, Tag> {
    #[inline(always)]
    pub fn detach(&mut self) {
        self.left = null();
        self.right = null();
        self.parent = null();
        self.balance = 0;
    }

    #[inline(always)]
    fn get_child(&self, dir: AvlDirection) -> *const T {
        match dir {
            AvlDirection::Left => self.left,
            AvlDirection::Right => self.right,
        }
    }

    #[inline(always)]
    fn set_child(&mut self, dir: AvlDirection, child: *const T) {
        match dir {
            AvlDirection::Left => self.left = child,
            AvlDirection::Right => self.right = child,
        }
    }

    #[inline(always)]
    fn get_parent(&self) -> *const T {
        self.parent
    }

    // Swap two node but not there value
    #[inline(always)]
    pub fn swap(&mut self, other: &mut AvlNode<T, Tag>) {
        mem::swap(&mut self.left, &mut other.left);
        mem::swap(&mut self.right, &mut other.right);
        mem::swap(&mut self.parent, &mut other.parent);
        mem::swap(&mut self.balance, &mut other.balance);
    }
}

impl<T, Tag> Default for AvlNode<T, Tag> {
    fn default() -> Self {
        Self { left: null(), right: null(), parent: null(), balance: 0, _phan: Default::default() }
    }
}

#[allow(unused_must_use)]
impl<T: AvlItem<Tag>, Tag> fmt::Debug for AvlNode<T, Tag> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;

        if !self.left.is_null() {
            write!(f, "left: {:p}", self.left)?;
        } else {
            write!(f, "left: none ")?;
        }

        if !self.right.is_null() {
            write!(f, "right: {:p}", self.right)?;
        } else {
            write!(f, "right: none ")?;
        }
        write!(f, ")")
    }
}

pub type AvlCmpFunc<K, T> = fn(&K, &T) -> Ordering;

/// An intrusive AVL tree (balanced binary search tree).
///
/// Elements in the tree must implement the [`AvlItem`] trait.
/// The tree supports various pointer types (`Box`, `Arc`, `Rc`, etc.) through the [`Pointer`] trait.
pub struct AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    pub root: *const P::Target,
    count: i64,
    _phan: PhantomData<fn(P, &Tag)>,
}

/// Result of a search operation in an [`AvlTree`].
///
/// An `AvlSearchResult` identifies either:
/// 1. An exact match: `direction` is `None` and `node` points to the matching item.
/// 2. An insertion point: `direction` is `Some(dir)` and `node` points to the parent
///    where a new node should be attached as the `dir` child.
///
/// The lifetime `'a` ties the search result to the tree's borrow, ensuring safety.
/// However, this lifetime often prevents further mutable operations on the tree
/// (e.g., adding a node while holding the search result). Use [`detach`](Self::detach)
/// to de-couple the result from the tree's lifetime when necessary.
pub struct AvlSearchResult<'a, P: Pointer> {
    /// The matching node or the parent for insertion.
    pub node: *const P::Target,
    /// `None` if exact match found, or `Some(direction)` indicating insertion point.
    pub direction: Option<AvlDirection>,
    _phan: PhantomData<&'a P::Target>,
}

impl<P: Pointer> Default for AvlSearchResult<'_, P> {
    fn default() -> Self {
        AvlSearchResult { node: null(), direction: Some(AvlDirection::Left), _phan: PhantomData }
    }
}

impl<'a, P: Pointer> AvlSearchResult<'a, P> {
    /// Returns a reference to the matching node if the search was an exact match.
    #[inline(always)]
    pub fn get_node_ref(&self) -> Option<&'a P::Target> {
        if self.is_exact() { unsafe { self.node.as_ref() } } else { None }
    }

    /// Returns `true` if the search result is an exact match.
    #[inline(always)]
    pub fn is_exact(&self) -> bool {
        self.direction.is_none() && !self.node.is_null()
    }

    /// De-couple the lifetime of the search result from the tree.
    ///
    /// This method is essential for performing mutable operations on the tree
    /// using search results. In Rust, a search result typically borrows the tree
    /// immutably. If you need to modify the tree (e.g., call `insert` or `remove`)
    /// based on that result, the borrow checker would normally prevent it.
    ///
    /// `detach` effectively "erases" the lifetime `'a`, returning a result with
    /// an unbounded lifetime `'b`.
    ///
    /// # Examples
    ///
    /// Used in `RangeTree::add`:
    /// ```ignore
    /// let result = self.root.find(&rs_key, range_tree_segment_cmp);
    /// // result is AvlSearchResult<'a, ...> and borrows self.root
    ///
    /// let detached = unsafe { result.detach() };
    /// // detached has no lifetime bound to self.root
    ///
    /// self.space += size; // Mutable operation on self permitted
    /// self.merge_seg(start, end, detached); // Mutation on tree permitted
    /// ```
    ///
    /// # Safety
    /// This is an unsafe operation. The compiler no longer protects the validity
    /// of the internal pointer via lifetimes. You must ensure that the tree
    /// structure is not modified in a way that invalidates `node` (e.g., the
    /// parent node being removed) before using the detached result.
    #[inline(always)]
    pub unsafe fn detach<'b>(&'a self) -> AvlSearchResult<'b, P> {
        AvlSearchResult { node: self.node, direction: self.direction, _phan: PhantomData }
    }

    /// Return the nearest node in the search result
    #[inline(always)]
    pub fn get_nearest(&self) -> Option<&P::Target> {
        if self.node.is_null() { None } else { unsafe { self.node.as_ref() } }
    }
}

impl<'a, T> AvlSearchResult<'a, Arc<T>> {
    /// Returns the matching Arc node if this is an exact match.
    pub fn get_exact(&self) -> Option<Arc<T>> {
        if self.is_exact() {
            unsafe {
                Arc::increment_strong_count(self.node);
                Some(Arc::from_raw(self.node))
            }
        } else {
            None
        }
    }
}

impl<'a, T> AvlSearchResult<'a, Rc<T>> {
    /// Returns the matching Rc node if this is an exact match.
    pub fn get_exact(&self) -> Option<Rc<T>> {
        if self.is_exact() {
            unsafe {
                Rc::increment_strong_count(self.node);
                Some(Rc::from_raw(self.node))
            }
        } else {
            None
        }
    }
}

macro_rules! return_end {
    ($tree: expr, $dir: expr) => {{ if $tree.root.is_null() { null() } else { $tree.bottom_child_ref($tree.root, $dir) } }};
}

macro_rules! balance_to_child {
    ($balance: expr) => {
        match $balance {
            0 | 1 => AvlDirection::Left,
            _ => AvlDirection::Right,
        }
    };
}

impl<P, Tag> AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    /// Creates a new, empty `AvlTree`.
    pub fn new() -> Self {
        AvlTree { count: 0, root: null(), _phan: Default::default() }
    }

    /// Returns an iterator that removes all elements from the tree in post-order.
    ///
    /// This is an optimized, non-recursive, and stack-less traversal that preserves
    /// tree invariants during destruction.
    #[inline]
    pub fn drain(&mut self) -> AvlDrain<'_, P, Tag> {
        AvlDrain::new(self)
    }

    pub fn get_count(&self) -> i64 {
        self.count
    }

    pub fn first(&self) -> Option<&P::Target> {
        unsafe { return_end!(self, AvlDirection::Left).as_ref() }
    }

    #[inline]
    pub fn last(&self) -> Option<&P::Target> {
        unsafe { return_end!(self, AvlDirection::Right).as_ref() }
    }

    /// Inserts a new node into the tree at the location specified by a search result.
    ///
    /// This is typically used after a [`find`](Self::find) operation didn't find an exact match.
    ///
    /// # Safety
    ///
    /// Once the tree structure changed, previous search result is not safe to use anymore.
    ///
    /// You should [detach()](AvlSearchResult::detach) the result before calling insert,
    /// to avoid the borrowing issue.
    ///
    /// # Panics
    /// Panics if the search result is an exact match (i.e. node already exists).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use embed_collections::avl::{AvlTree, AvlItem, AvlNode};
    /// use core::cell::UnsafeCell;
    /// use std::sync::Arc;
    ///
    /// struct MyNode {
    ///     value: i32,
    ///     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
    /// }
    ///
    /// unsafe impl AvlItem<()> for MyNode {
    ///     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
    ///         unsafe { &mut *self.avl_node.get() }
    ///     }
    /// }
    ///
    /// let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
    /// let key = 42;
    /// let result = tree.find(&key, |k, n| k.cmp(&n.value));
    ///
    /// if !result.is_exact() {
    ///     let new_node = Arc::new(MyNode {
    ///         value: key,
    ///         avl_node: UnsafeCell::new(Default::default()),
    ///     });
    ///     tree.insert(new_node, unsafe{result.detach()});
    /// }
    /// ```
    #[inline]
    pub fn insert(&mut self, new_data: P, w: AvlSearchResult<'_, P>) {
        debug_assert!(w.direction.is_some());
        self._insert(new_data, w.node, w.direction.unwrap());
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn _insert(
        &mut self,
        new_data: P,
        here: *const P::Target, // parent
        mut which_child: AvlDirection,
    ) {
        let mut new_balance: i8;
        let new_ptr = new_data.into_raw();

        if here.is_null() {
            if self.count > 0 {
                panic!("insert into a tree size {} with empty where.node", self.count);
            }
            self.root = new_ptr;
            self.count += 1;
            return;
        }

        let parent = unsafe { &*here };
        let node = unsafe { (*new_ptr).get_node() };
        let parent_node = parent.get_node();
        node.parent = here;
        parent_node.set_child(which_child, new_ptr);
        self.count += 1;

        /*
         * Now, back up the tree modifying the balance of all nodes above the
         * insertion point. If we get to a highly unbalanced ancestor, we
         * need to do a rotation.  If we back out of the tree we are done.
         * If we brought any subtree into perfect balance (0), we are also done.
         */
        let mut data: *const P::Target = here;
        loop {
            let node = unsafe { (*data).get_node() };
            let old_balance = node.balance;
            new_balance = old_balance + avlchild_to_balance!(which_child);
            if new_balance == 0 {
                node.balance = 0;
                return;
            }
            if old_balance != 0 {
                self.rotate(data, new_balance);
                return;
            }
            node.balance = new_balance;
            let parent_ptr = node.get_parent();
            if parent_ptr.is_null() {
                return;
            }
            which_child = self.parent_direction(data, parent_ptr);
            data = parent_ptr;
        }
    }

    /// Insert "new_data" in "tree" in the given "direction" either after or
    /// before AvlDirection::After, AvlDirection::Before) the data "here".
    ///
    /// Insertions can only be done at empty leaf points in the tree, therefore
    /// if the given child of the node is already present we move to either
    /// the AVL_PREV or AVL_NEXT and reverse the insertion direction. Since
    /// every other node in the tree is a leaf, this always works.
    ///
    /// # Safety
    ///
    /// Once the tree structure changed, previous search result is not safe to use anymore.
    ///
    /// You should [detach()](AvlSearchResult::detach) the result before calling insert,
    /// to avoid the borrowing issue.
    pub unsafe fn insert_here(
        &mut self, new_data: P, here: AvlSearchResult<P>, direction: AvlDirection,
    ) {
        let mut dir_child = direction;
        assert!(!here.node.is_null());
        let here_node = here.node;
        let child = unsafe { (*here_node).get_node().get_child(dir_child) };
        if !child.is_null() {
            dir_child = dir_child.reverse();
            let node = self.bottom_child_ref(child, dir_child);
            self._insert(new_data, node, dir_child);
        } else {
            self._insert(new_data, here_node, dir_child);
        }
    }

    // set child and both child's parent
    #[inline(always)]
    fn set_child2(
        &mut self, node: &mut AvlNode<P::Target, Tag>, dir: AvlDirection, child: *const P::Target,
        parent: *const P::Target,
    ) {
        if !child.is_null() {
            unsafe { (*child).get_node().parent = parent };
        }
        node.set_child(dir, child);
    }

    #[inline(always)]
    fn parent_direction(&self, data: *const P::Target, parent: *const P::Target) -> AvlDirection {
        if !parent.is_null() {
            let parent_node = unsafe { (*parent).get_node() };
            if parent_node.left == data {
                return AvlDirection::Left;
            }
            if parent_node.right == data {
                return AvlDirection::Right;
            }
            panic!("invalid avl tree, node {:p}, parent {:p}", data, parent);
        }
        // this just follow zfs
        AvlDirection::Left
    }

    #[inline(always)]
    fn parent_direction2(&self, data: *const P::Target) -> AvlDirection {
        let node = unsafe { (*data).get_node() };
        let parent = node.get_parent();
        if !parent.is_null() {
            return self.parent_direction(data, parent);
        }
        // this just follow zfs
        AvlDirection::Left
    }

    #[inline]
    fn rotate(&mut self, data: *const P::Target, balance: i8) -> bool {
        let dir = if balance < 0 { AvlDirection::Left } else { AvlDirection::Right };
        let node = unsafe { (*data).get_node() };

        let parent = node.get_parent();
        let dir_inverse = dir.reverse();
        let left_heavy = balance >> 1;
        let right_heavy = -left_heavy;

        let child = node.get_child(dir);
        let child_node = unsafe { (*child).get_node() };
        let mut child_balance = child_node.balance;

        let which_child = self.parent_direction(data, parent);

        // node is overly left heavy, the left child is balanced or also left heavy.
        if child_balance != right_heavy {
            child_balance += right_heavy;

            let c_right = child_node.get_child(dir_inverse);
            self.set_child2(node, dir, c_right, data);
            // move node to be child's right child
            node.balance = -child_balance;

            node.parent = child;
            child_node.set_child(dir_inverse, data);
            // update the pointer into this subtree

            child_node.balance = child_balance;
            if !parent.is_null() {
                child_node.parent = parent;
                unsafe { (*parent).get_node() }.set_child(which_child, child);
            } else {
                child_node.parent = null();
                self.root = child;
            }
            return child_balance == 0;
        }
        // When node is left heavy, but child is right heavy we use
        // a different rotation.

        let g_child = child_node.get_child(dir_inverse);
        let g_child_node = unsafe { (*g_child).get_node() };
        let g_left = g_child_node.get_child(dir);
        let g_right = g_child_node.get_child(dir_inverse);

        self.set_child2(node, dir, g_right, data);
        self.set_child2(child_node, dir_inverse, g_left, child);

        /*
         * move child to left child of gchild and
         * move node to right child of gchild and
         * fixup parent of all this to point to gchild
         */

        let g_child_balance = g_child_node.balance;
        if g_child_balance == right_heavy {
            child_node.balance = left_heavy;
        } else {
            child_node.balance = 0;
        }
        child_node.parent = g_child;
        g_child_node.set_child(dir, child);

        if g_child_balance == left_heavy {
            node.balance = right_heavy;
        } else {
            node.balance = 0;
        }
        g_child_node.balance = 0;

        node.parent = g_child;
        g_child_node.set_child(dir_inverse, data);

        if !parent.is_null() {
            g_child_node.parent = parent;
            unsafe { (*parent).get_node() }.set_child(which_child, g_child);
        } else {
            g_child_node.parent = null();
            self.root = g_child;
        }
        true
    }

    /*
    fn replace(&mut self, old: *const P::Target, node: P) {
        let old_node = unsafe { (*old).get_node() };
        let new_ptr = node.into_raw();
        let new_node = unsafe { (*new_ptr).get_node() };

        let left = old_node.get_child(AvlDirection::Left);
        if !left.is_null() {
            self.set_child2(new_node, AvlDirection::Left, left, new_ptr);
        }
        let right = old_node.get_child(AvlDirection::Right);
        if !right.is_null() {
            self.set_child2(new_node, AvlDirection::Right, right, new_ptr);
        }

        new_node.balance = old_node.balance;
        old_node.balance = 0;
        let parent = old_node.get_parent();
        if !parent.is_null() {
            let dir = self.parent_direction(old, parent);
            self.set_child2(unsafe { (*parent).get_node() }, dir, new_ptr, parent);
            old_node.parent = null();
        } else {
            debug_assert_eq!(self.root, old);
            self.root = new_ptr;
        }
    }
    */

    /// Requires `del` to be a valid pointer to a node in this tree.
    ///
    /// # Safety
    ///
    /// It does not drop the node data, only unlinks it.
    /// Caller is responsible for re-taking ownership (e.g. via from_raw) and dropping if needed.
    ///
    /// For Arc/Rc, use [Self::remove_ref()] instead.
    ///
    pub unsafe fn remove(&mut self, del: *const P::Target) {
        /*
         * Deletion is easiest with a node that has at most 1 child.
         * We swap a node with 2 children with a sequentially valued
         * neighbor node. That node will have at most 1 child. Note this
         * has no effect on the ordering of the remaining nodes.
         *
         * As an optimization, we choose the greater neighbor if the tree
         * is right heavy, otherwise the left neighbor. This reduces the
         * number of rotations needed.
         */
        if self.count == 0 {
            return;
        }
        if self.count == 1 && self.root == del {
            self.root = null();
            self.count = 0;
            unsafe { (*del).get_node().detach() };
            return;
        }
        let mut which_child: AvlDirection;

        // Use reference directly to get node, avoiding unsafe dereference of raw pointer
        let del_node = unsafe { (*del).get_node() };

        let node_swap_flag = !del_node.left.is_null() && !del_node.right.is_null();

        if node_swap_flag {
            let dir: AvlDirection = balance_to_child!(del_node.balance + 1);
            let child_temp = del_node.get_child(dir);

            let dir_inverse: AvlDirection = dir.reverse();
            let child = self.bottom_child_ref(child_temp, dir_inverse);

            // Fix Miri UB: Avoid calling parent_direction2(child) if child's parent is del,
            // because that would create a aliasing &mut ref to del while we hold del_node.
            let dir_child_temp =
                if child == child_temp { dir } else { self.parent_direction2(child) };

            // Fix Miri UB: Do not call parent_direction2(del) as it creates a new &mut AvlNode
            // alias while we hold del_node. Use del_node to find parent direction.
            let parent = del_node.get_parent();
            let dir_child_del = if !parent.is_null() {
                self.parent_direction(del, parent)
            } else {
                AvlDirection::Left
            };

            let child_node = unsafe { (*child).get_node() };
            child_node.swap(del_node);

            // move 'node' to delete's spot in the tree
            if child_node.get_child(dir) == child {
                // if node(d) left child is node(c)
                child_node.set_child(dir, del);
            }

            let c_dir = child_node.get_child(dir);
            if c_dir == del {
                del_node.parent = child;
            } else if !c_dir.is_null() {
                unsafe { (*c_dir).get_node() }.parent = child;
            }

            let c_inv = child_node.get_child(dir_inverse);
            if c_inv == del {
                del_node.parent = child;
            } else if !c_inv.is_null() {
                unsafe { (*c_inv).get_node() }.parent = child;
            }

            let parent = child_node.get_parent();
            if !parent.is_null() {
                unsafe { (*parent).get_node() }.set_child(dir_child_del, child);
            } else {
                self.root = child;
            }

            // Put tmp where node used to be (just temporary).
            // It always has a parent and at most 1 child.
            let parent = del_node.get_parent();
            unsafe { (*parent).get_node() }.set_child(dir_child_temp, del);
            if !del_node.right.is_null() {
                which_child = AvlDirection::Right;
            } else {
                which_child = AvlDirection::Left;
            }
            let child = del_node.get_child(which_child);
            if !child.is_null() {
                unsafe { (*child).get_node() }.parent = del;
            }
            which_child = dir_child_temp;
        } else {
            // Fix Miri UB here as well
            let parent = del_node.get_parent();
            if !parent.is_null() {
                which_child = self.parent_direction(del, parent);
            } else {
                which_child = AvlDirection::Left;
            }
        }

        // Here we know "delete" is at least partially a leaf node. It can
        // be easily removed from the tree.
        let parent: *const P::Target = del_node.get_parent();

        let imm_data: *const P::Target =
            if !del_node.left.is_null() { del_node.left } else { del_node.right };

        // Connect parent directly to node (leaving out delete).
        if !imm_data.is_null() {
            let imm_node = unsafe { (*imm_data).get_node() };
            imm_node.parent = parent;
        }

        if !parent.is_null() {
            assert!(self.count > 0);
            self.count -= 1;

            let parent_node = unsafe { (*parent).get_node() };
            parent_node.set_child(which_child, imm_data);

            //Since the subtree is now shorter, begin adjusting parent balances
            //and performing any needed rotations.
            let mut node_data: *const P::Target = parent;
            let mut old_balance: i8;
            let mut new_balance: i8;
            loop {
                // Move up the tree and adjust the balance.
                // Capture the parent and which_child values for the next
                // iteration before any rotations occur.
                let node = unsafe { (*node_data).get_node() };
                old_balance = node.balance;
                new_balance = old_balance - avlchild_to_balance!(which_child);

                //If a node was in perfect balance but isn't anymore then
                //we can stop, since the height didn't change above this point
                //due to a deletion.
                if old_balance == 0 {
                    node.balance = new_balance;
                    break;
                }

                let parent = node.get_parent();
                which_child = self.parent_direction(node_data, parent);

                //If the new balance is zero, we don't need to rotate
                //else
                //need a rotation to fix the balance.
                //If the rotation doesn't change the height
                //of the sub-tree we have finished adjusting.
                if new_balance == 0 {
                    node.balance = new_balance;
                } else if !self.rotate(node_data, new_balance) {
                    break;
                }

                if !parent.is_null() {
                    node_data = parent;
                    continue;
                }
                break;
            }
        } else if !imm_data.is_null() {
            assert!(self.count > 0);
            self.count -= 1;
            self.root = imm_data;
        }
        if self.root.is_null() && self.count > 0 {
            panic!("AvlTree {} nodes left after remove but tree.root == nil", self.count);
        }
        del_node.detach();
    }

    /// Removes a node from the tree by key.
    ///
    /// The `cmp_func` should compare the key `K` with the elements in the tree.
    /// Returns `Some(P)` if an exact match was found and removed, `None` otherwise.
    #[inline]
    pub fn remove_by_key<K>(&mut self, val: &K, cmp_func: AvlCmpFunc<K, P::Target>) -> Option<P> {
        let result = self.find(val, cmp_func);
        self.remove_with(unsafe { result.detach() })
    }

    /// remove with a previous search result
    ///
    /// - If the result is exact match, return the removed element ownership
    /// - If the result is not exact match, return None
    ///
    /// # Safety
    ///
    /// Once the tree structure changed, previous search result is not safe to use anymore.
    ///
    /// You should [detach()](AvlSearchResult::detach) the result before calling insert,
    /// to avoid the borrowing issue.
    #[inline]
    pub fn remove_with(&mut self, result: AvlSearchResult<'_, P>) -> Option<P> {
        if result.is_exact() {
            unsafe {
                let p = result.node;
                self.remove(p);
                Some(P::from_raw(p))
            }
        } else {
            None
        }
    }

    /// Searches for an element in the tree.
    ///
    /// The `cmp_func` should compare the key `K` with the elements in the tree.
    /// Returns an [`AvlSearchResult`] which indicates if an exact match was found,
    /// or where a new element should be inserted.
    #[inline]
    pub fn find<'a, K>(
        &'a self, val: &K, cmp_func: AvlCmpFunc<K, P::Target>,
    ) -> AvlSearchResult<'a, P> {
        if self.root.is_null() {
            return AvlSearchResult::default();
        }
        let mut node_data = self.root;
        loop {
            let diff = cmp_func(val, unsafe { &*node_data });
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult {
                        node: node_data,
                        direction: None,
                        _phan: PhantomData,
                    };
                }
                Ordering::Less => {
                    let node = unsafe { (*node_data).get_node() };
                    let left = node.get_child(AvlDirection::Left);
                    if left.is_null() {
                        return AvlSearchResult {
                            node: node_data,
                            direction: Some(AvlDirection::Left),
                            _phan: PhantomData,
                        };
                    }
                    node_data = left;
                }
                Ordering::Greater => {
                    let node = unsafe { (*node_data).get_node() };
                    let right = node.get_child(AvlDirection::Right);
                    if right.is_null() {
                        return AvlSearchResult {
                            node: node_data,
                            direction: Some(AvlDirection::Right),
                            _phan: PhantomData,
                        };
                    }
                    node_data = right;
                }
            }
        }
    }

    // for range tree, val may overlap multiple range(node), ensure return the smallest
    #[inline]
    pub fn find_contained<'a, K>(
        &'a self, val: &K, cmp_func: AvlCmpFunc<K, P::Target>,
    ) -> Option<&'a P::Target> {
        if self.root.is_null() {
            return None;
        }
        let mut node_data = self.root;
        let mut result_node: *const P::Target = null();
        loop {
            let diff = cmp_func(val, unsafe { &*node_data });
            match diff {
                Ordering::Equal => {
                    let node = unsafe { (*node_data).get_node() };
                    let left = node.get_child(AvlDirection::Left);
                    result_node = node_data;
                    if left.is_null() {
                        break;
                    } else {
                        node_data = left;
                    }
                }
                Ordering::Less => {
                    let node = unsafe { (*node_data).get_node() };
                    let left = node.get_child(AvlDirection::Left);
                    if left.is_null() {
                        break;
                    }
                    node_data = left;
                }
                Ordering::Greater => {
                    let node = unsafe { (*node_data).get_node() };
                    let right = node.get_child(AvlDirection::Right);
                    if right.is_null() {
                        break;
                    }
                    node_data = right;
                }
            }
        }
        if result_node.is_null() { None } else { unsafe { result_node.as_ref() } }
    }

    // for slab, return any block larger or equal than search param
    #[inline]
    pub fn find_larger_eq<'a, K>(
        &'a self, val: &K, cmp_func: AvlCmpFunc<K, P::Target>,
    ) -> AvlSearchResult<'a, P> {
        if self.root.is_null() {
            return AvlSearchResult::default();
        }
        let mut node_data = self.root;
        loop {
            let diff = cmp_func(val, unsafe { &*node_data });
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult {
                        node: node_data,
                        direction: None,
                        _phan: PhantomData,
                    };
                }
                Ordering::Less => {
                    return AvlSearchResult {
                        node: node_data,
                        direction: None,
                        _phan: PhantomData,
                    };
                }
                Ordering::Greater => {
                    let right = unsafe { (*node_data).get_node() }.get_child(AvlDirection::Right);
                    if right.is_null() {
                        return AvlSearchResult {
                            node: null(),
                            direction: None,
                            _phan: PhantomData,
                        };
                    }
                    node_data = right;
                }
            }
        }
    }

    /// For range tree
    #[inline]
    pub fn find_nearest<'a, K>(
        &'a self, val: &K, cmp_func: AvlCmpFunc<K, P::Target>,
    ) -> AvlSearchResult<'a, P> {
        if self.root.is_null() {
            return AvlSearchResult::default();
        }

        let mut node_data = self.root;
        let mut nearest_node = null();
        loop {
            let diff = cmp_func(val, unsafe { &*node_data });
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult {
                        node: node_data,
                        direction: None,
                        _phan: PhantomData,
                    };
                }
                Ordering::Less => {
                    nearest_node = node_data;
                    let left = unsafe { (*node_data).get_node() }.get_child(AvlDirection::Left);
                    if left.is_null() {
                        break;
                    }
                    node_data = left;
                }
                Ordering::Greater => {
                    let right = unsafe { (*node_data).get_node() }.get_child(AvlDirection::Right);
                    if right.is_null() {
                        break;
                    }
                    node_data = right;
                }
            }
        }
        AvlSearchResult { node: nearest_node, direction: None, _phan: PhantomData }
    }

    #[inline(always)]
    fn bottom_child_ref(&self, mut data: *const P::Target, dir: AvlDirection) -> *const P::Target {
        loop {
            let child = unsafe { (*data).get_node() }.get_child(dir);
            if !child.is_null() {
                data = child;
            } else {
                return data;
            }
        }
    }

    pub fn walk<F: Fn(&P::Target)>(&self, cb: F) {
        let mut node = self.first();
        while let Some(n) = node {
            cb(n);
            node = self.next(n);
        }
    }

    #[inline]
    pub fn next<'a>(&'a self, data: &'a P::Target) -> Option<&'a P::Target> {
        if let Some(p) = self.walk_dir(data, AvlDirection::Right) {
            Some(unsafe { p.as_ref() })
        } else {
            None
        }
    }

    #[inline]
    pub fn prev<'a>(&'a self, data: &'a P::Target) -> Option<&'a P::Target> {
        if let Some(p) = self.walk_dir(data, AvlDirection::Left) {
            Some(unsafe { p.as_ref() })
        } else {
            None
        }
    }

    #[inline]
    fn walk_dir(
        &self, mut data_ptr: *const P::Target, dir: AvlDirection,
    ) -> Option<NonNull<P::Target>> {
        let dir_inverse = dir.reverse();
        let node = unsafe { (*data_ptr).get_node() };
        let temp = node.get_child(dir);
        if !temp.is_null() {
            unsafe {
                Some(NonNull::new_unchecked(
                    self.bottom_child_ref(temp, dir_inverse) as *mut P::Target
                ))
            }
        } else {
            let mut parent = node.parent;
            if parent.is_null() {
                return None;
            }
            loop {
                let pdir = self.parent_direction(data_ptr, parent);
                if pdir == dir_inverse {
                    return Some(unsafe { NonNull::new_unchecked(parent as *mut P::Target) });
                }
                data_ptr = parent;
                parent = unsafe { (*parent).get_node() }.parent;
                if parent.is_null() {
                    return None;
                }
            }
        }
    }

    #[inline]
    fn validate_node(&self, data: *const P::Target, cmp_func: AvlCmpFunc<P::Target, P::Target>) {
        let node = unsafe { (*data).get_node() };
        let left = node.left;
        if !left.is_null() {
            assert!(cmp_func(unsafe { &*left }, unsafe { &*data }) != Ordering::Greater);
            assert_eq!(unsafe { (*left).get_node() }.get_parent(), data);
        }
        let right = node.right;
        if !right.is_null() {
            assert!(cmp_func(unsafe { &*right }, unsafe { &*data }) != Ordering::Less);
            assert_eq!(unsafe { (*right).get_node() }.get_parent(), data);
        }
    }

    #[inline]
    pub fn nearest<'a>(
        &'a self, current: &AvlSearchResult<'a, P>, direction: AvlDirection,
    ) -> AvlSearchResult<'a, P> {
        if !current.node.is_null() {
            if current.direction.is_some() && current.direction != Some(direction) {
                return AvlSearchResult { node: current.node, direction: None, _phan: PhantomData };
            }
            if let Some(node) = self.walk_dir(current.node, direction) {
                return AvlSearchResult {
                    node: node.as_ptr(),
                    direction: None,
                    _phan: PhantomData,
                };
            }
        }
        AvlSearchResult::default()
    }

    pub fn validate(&self, cmp_func: AvlCmpFunc<P::Target, P::Target>) {
        let c = {
            #[cfg(feature = "std")]
            {
                ((self.get_count() + 10) as f32).log2() as usize
            }
            #[cfg(not(feature = "std"))]
            {
                100
            }
        };
        let mut stack: Vec<*const P::Target> = Vec::with_capacity(c);
        if self.root.is_null() {
            assert_eq!(self.count, 0);
            return;
        }
        let mut data = self.root;
        let mut visited = 0;
        loop {
            if !data.is_null() {
                let left = {
                    let node = unsafe { (*data).get_node() };
                    node.get_child(AvlDirection::Left)
                };
                if !left.is_null() {
                    stack.push(data);
                    data = left;
                    continue;
                }
                visited += 1;
                self.validate_node(data, cmp_func);
                data = unsafe { (*data).get_node() }.get_child(AvlDirection::Right);
            } else if !stack.is_empty() {
                let _data = stack.pop().unwrap();
                self.validate_node(_data, cmp_func);
                visited += 1;
                let node = unsafe { (*_data).get_node() };
                data = node.get_child(AvlDirection::Right);
            } else {
                break;
            }
        }
        assert_eq!(visited, self.count);
    }

    /// Adds a new element to the tree， takes the ownership of P.
    ///
    /// The `cmp_func` should compare two elements to determine their relative order.
    /// Returns `true` if the element was added, `false` if an equivalent element
    /// already exists (in which case the provided `node` is dropped).
    #[inline]
    pub fn add(&mut self, node: P, cmp_func: AvlCmpFunc<P::Target, P::Target>) -> bool {
        if self.count == 0 && self.root.is_null() {
            self.root = node.into_raw();
            self.count = 1;
            return true;
        }

        let w = self.find(node.as_ref(), cmp_func);
        if w.direction.is_none() {
            // To prevent memory leak, we must drop the node.
            // But since we took ownership, we have to convert it back to P and drop it.
            drop(node);
            return false;
        }

        // Safety: We need to decouple the lifetime of 'w' from 'self' to call 'insert'.
        // We extract the pointers and reconstruct the result.
        let w_node = w.node;
        let w_dir = w.direction;

        let w_detached = AvlSearchResult { node: w_node, direction: w_dir, _phan: PhantomData };

        self.insert(node, w_detached);
        true
    }
}

impl<P, Tag> Drop for AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    fn drop(&mut self) {
        if mem::needs_drop::<P>() {
            for _ in self.drain() {}
        }
    }
}

impl<T, Tag> AvlTree<Arc<T>, Tag>
where
    T: AvlItem<Tag>,
{
    pub fn remove_ref(&mut self, node: &Arc<T>) {
        let p = Arc::as_ptr(node);
        unsafe { self.remove(p) };
        unsafe { drop(Arc::from_raw(p)) };
    }
}

impl<T, Tag> AvlTree<Rc<T>, Tag>
where
    T: AvlItem<Tag>,
{
    pub fn remove_ref(&mut self, node: &Rc<T>) {
        let p = Rc::as_ptr(node);
        unsafe { self.remove(p) };
        unsafe { drop(Rc::from_raw(p)) };
    }
}
