#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]
//! An intrusive AVL tree implementation.
//!
//! The algorithm origin from open-zfs
//!
//! The ordering of avl tree is defined by [AvlItem] trait. There're two scenario:
//! - borrow field as key from the node struct
//! - impl Ord for struct itself
//!
//! Refer to the example of [AvlItem] document.
//!
//! # Examples
//!
//! ## Using `Box` to search and remove by key
//!
//! ```rust
//! use embed_avl::{AvlTree, AvlItem, AvlNode, Entry, impl_ord_with_borrow};
//! use core::cell::UnsafeCell;
//! use core::cmp::{Ordering, Ord};
//! use core::borrow::Borrow;
//! extern crate format_attr;
//! extern crate alloc;
//! use alloc::sync::Arc;
//! use core::fmt;
//!
//! #[derive(format_attr::DebugAttr)]
//! #[fmt("MyNode {value}")]
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
//! }
//!
//! impl Borrow<i32> for MyNode {
//!     fn borrow(&self) -> &i32 {
//!         &self.value
//!     }
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! impl_ord_with_borrow!(MyNode, i32);
//!
//! // A boxed example
//!
//! let mut tree = AvlTree::<Box<MyNode>, ()>::new();
//! tree.add(Box::new(MyNode { value: 10, avl_node: UnsafeCell::new(Default::default()) })).expect("add ok");
//!
//! // Search and remove
//! if let Some(node) = tree.remove_by_key::<i32>(&10i32) {
//!     assert_eq!(node.value, 10);
//! }
//! assert!(tree.is_empty());
//!
//! // Using `Arc` for multiple ownership
//! // remove_ref only available to `Arc` and `Rc`
//!
//! let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
//! let node = Arc::new(MyNode { value: 42, avl_node: UnsafeCell::new(Default::default()) });
//!
//! // Alternative way of insert
//! if let Entry::Vacant(ent) = tree.entry(node.value) {
//!     ent.insert_node(node.clone());
//! } else {
//!     unreachable!();
//! }
//! assert_eq!(tree.len(), 1);
//!
//! // Remove by reference (detach from avl tree)
//! tree.remove(&node);
//! assert_eq!(tree.len(), 0);
//! ```

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

mod entry;
mod iter;
pub use entry::*;
pub use iter::*;
#[cfg(test)]
mod tests;

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::{
    borrow::Borrow,
    cmp::{Ordering, PartialEq},
    fmt,
    mem::{self, ManuallyDrop},
    ops::Deref,
    ptr::{NonNull, null_mut},
};
use pointers::Pointer;

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
///
/// # Example (struct field as key)
///
/// ```
/// use embed_avl::{AvlItem, AvlNode, impl_ord_with_borrow};
/// extern crate format_attr;
/// use core::borrow::Borrow;
/// use core::cell::UnsafeCell;
///
/// #[derive(format_attr::DebugAttr)]
/// #[fmt("IntAvlNode {value}")]
/// pub struct IntAvlNode {
///     pub value: i64,
///     pub node: UnsafeCell<AvlNode<Self, ()>>,
/// }
///
/// unsafe impl AvlItem<()> for IntAvlNode {
///     fn get_node(&self) -> &mut AvlNode<Self, ()> {
///         unsafe { &mut *self.node.get() }
///     }
/// }
///
/// impl Borrow<i64> for IntAvlNode {
///     fn borrow(&self) -> &i64 {
///         &self.value
///     }
/// }
///
/// impl_ord_with_borrow!(IntAvlNode, i64);
/// ```
///
/// # Example (impl Ord for struct)
///
/// ```
/// use embed_avl::{AvlItem, AvlNode};
/// use core::cell::{Cell, UnsafeCell};
/// use core::cmp::Ordering;
///
/// pub struct RangeSeg {
///     node: UnsafeCell<AvlNode<Self, ()>>,
///     pub start: Cell<u64>,
///     pub end: Cell<u64>,
/// }
///
/// impl PartialOrd for RangeSeg {
///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
///         Some(Ord::cmp(self, other))
///     }
/// }
/// impl PartialEq for RangeSeg {
///     fn eq(&self, other: &Self) -> bool {
///         Ord::cmp(self, other) == Ordering::Equal
///     }
/// }
/// impl Eq for RangeSeg {}
///
/// impl Ord for RangeSeg {
///     fn cmp(&self, other: &Self) -> Ordering {
///         if self.end.get() <= other.start.get() {
///             Ordering::Less
///         } else if self.start.get() >= other.end.get() {
///             Ordering::Greater
///         } else {
///             // intersection
///             Ordering::Equal
///         }
///     }
/// }
/// unsafe impl Send for RangeSeg {}
/// unsafe impl AvlItem<()> for RangeSeg {
///     fn get_node(&self) -> &mut AvlNode<Self, ()> {
///         unsafe { &mut *self.node.get() }
///     }
/// }
/// ```
pub unsafe trait AvlItem<Tag>: Sized {
    fn get_node(&self) -> &mut AvlNode<Self, Tag>;
}

/// Implement Ord with `Borrow<K>`
///
/// # Arguments
/// - cls: struct name
/// - key_type: `cls: Borrow<$key_type>`
#[macro_export]
macro_rules! impl_ord_with_borrow {
    ($cls: ty, $key_type: ty) => {
        impl PartialOrd for $cls {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(Ord::cmp(self, other))
            }
        }
        impl PartialEq for $cls {
            fn eq(&self, other: &Self) -> bool {
                Borrow::<$key_type>::borrow(self) == Borrow::<$key_type>::borrow(other)
            }
        }
        impl Eq for $cls {}

        impl Ord for $cls {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                Borrow::<$key_type>::borrow(self).cmp(Borrow::<$key_type>::borrow(other))
            }
        }
    };
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Direction {
    Left = 0,
    Right = 1,
}

impl Direction {
    #[inline(always)]
    fn reverse(self) -> Direction {
        match self {
            Direction::Left => Direction::Right,
            Direction::Right => Direction::Left,
        }
    }
}

macro_rules! avlchild_to_balance {
    ( $dir: expr ) => {
        match $dir {
            Direction::Left => -1,
            Direction::Right => 1,
        }
    };
}

pub struct AvlNode<T: AvlItem<Tag>, Tag> {
    pub left: *mut T,
    pub right: *mut T,
    pub parent: *mut T,
    pub balance: i8,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T: AvlItem<Tag> + Send, Tag> Send for AvlNode<T, Tag> {}

impl<T: AvlItem<Tag>, Tag> AvlNode<T, Tag> {
    #[inline(always)]
    pub fn detach(&mut self) {
        self.left = null_mut();
        self.right = null_mut();
        self.parent = null_mut();
        self.balance = 0;
    }

    #[inline(always)]
    fn get_child(&self, dir: Direction) -> *mut T {
        match dir {
            Direction::Left => self.left,
            Direction::Right => self.right,
        }
    }

    #[inline(always)]
    fn set_child(&mut self, dir: Direction, child: *mut T) {
        match dir {
            Direction::Left => self.left = child,
            Direction::Right => self.right = child,
        }
    }

    #[inline(always)]
    fn get_parent(&self) -> *mut T {
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

impl<T: AvlItem<Tag>, Tag> Default for AvlNode<T, Tag> {
    fn default() -> Self {
        Self {
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
            balance: 0,
            _phan: Default::default(),
        }
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

/// An intrusive AVL tree (balanced binary search tree).
///
/// Elements in the tree must implement the [`AvlItem`] trait.
/// The tree supports various pointer types (`Box`, `Arc`, `Rc`, etc.) through the [`Pointer`] trait.
pub struct AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    root: *mut P::Target,
    count: usize,
    _phan: PhantomData<fn(P, &Tag)>,
}

unsafe impl<P, Tag> Send for AvlTree<P, Tag>
where
    P: Pointer + Send,
    P::Target: AvlItem<Tag>,
{
}

unsafe impl<P, Tag> Sync for AvlTree<P, Tag>
where
    P: Pointer + Send,
    P::Target: AvlItem<Tag>,
{
}

macro_rules! balance_to_child {
    ($balance: expr) => {
        if $balance <= 1 { Direction::Left } else { Direction::Right }
    };
}

impl<P, Tag> AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    /// Creates a new, empty `AvlTree`.
    #[inline]
    pub fn new() -> Self {
        AvlTree { count: 0, root: null_mut(), _phan: Default::default() }
    }

    /// Returns an iterator that removes all elements from the tree in post-order.
    ///
    /// This is an optimized, non-recursive, and stack-less traversal that preserves
    /// tree invariants during destruction.
    #[inline]
    pub fn drain(&mut self) -> AvlDrain<'_, P, Tag> {
        AvlDrain::new(self)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Adds a new node to the tree
    ///
    /// - Returns `Ok(())` if the node was added, takes the ownership of P.
    /// - Err(P) if an equivalent node already exists
    #[inline]
    pub fn add(&mut self, node: P) -> Result<(), P>
    where
        P::Target: Ord,
    {
        if !self.root.is_null() {
            let mut parent = self.root;
            unsafe {
                loop {
                    match node.as_ref().cmp((&*parent).as_ref()) {
                        Ordering::Less => {
                            let left = (*parent).get_node().get_child(Direction::Left);
                            if left.is_null() {
                                self._insert(node, parent, Direction::Left);
                                return Ok(());
                            }
                            parent = left;
                        }
                        Ordering::Greater => {
                            let right = (*parent).get_node().get_child(Direction::Right);
                            if right.is_null() {
                                self._insert(node, parent, Direction::Right);
                                return Ok(());
                            }
                            parent = right;
                        }
                        Ordering::Equal => {
                            return Err(node);
                        }
                    }
                }
            }
        } else {
            debug_assert_eq!(self.count, 0);
            self.root = node.into_raw() as *mut P::Target;
            self.count = 1;
            Ok(())
        }
    }

    /// remove a node from the tree (need P::Target to impl Borrow)
    #[inline]
    pub fn remove_by_key<K>(&mut self, key: &K) -> Option<P>
    where
        P::Target: Borrow<K>,
        K: Ord,
    {
        let _cmp = |_key: &&K, node: &P::Target| -> Ordering { _key.cmp(&node.borrow()) };
        if let Entry::Occupied(ent) = unsafe { self.entry_with::<&K, _>(&key, _cmp) } {
            Some(ent.remove())
        } else {
            None
        }
    }

    /// remove a node from the tree (useful if P is multiple ownership)
    #[inline]
    pub fn remove(&mut self, node: &P)
    where
        P::Target: Ord,
    {
        let _cmp = |_cur: &&P::Target, node: &P::Target| -> Ordering { _cur.cmp(&node.borrow()) };
        if let Entry::Occupied(ent) =
            unsafe { self.entry_with::<&P::Target, _>(node.as_ref(), _cmp) }
        {
            ent.remove();
        }
    }

    /// Searches for an element in the tree with `key`, requires P::Target can borrow to `K` type,
    /// and have a total ordering by `K`.
    ///
    /// Returns an [`AvlSearchResult`] which indicates if an exact match was found,
    /// or where a new element should be inserted.
    #[inline]
    pub fn entry<'a, K>(&'a mut self, key: K) -> Entry<'a, P, Tag, K>
    where
        P::Target: Borrow<K>,
        K: Ord,
    {
        unsafe { self.entry_with(key, |_key: &K, node: &P::Target| _key.cmp(node.borrow())) }
    }

    /// Searches for an element in the tree with `key` and custom compare function.
    ///
    /// Returns an [`AvlSearchResult`] which indicates if an exact match was found,
    /// or where a new element should be inserted.
    #[inline]
    pub unsafe fn entry_with<'a, K, F>(&'a mut self, key: K, cmp_f: F) -> Entry<'a, P, Tag, K>
    where
        F: Fn(&K, &P::Target) -> Ordering,
    {
        if !self.root.is_null() {
            let mut parent = self.root;
            unsafe {
                loop {
                    match cmp_f(&key, (&*parent).as_ref()) {
                        Ordering::Equal => {
                            return Entry::Occupied(OccupiedEntry {
                                node: NonNull::new_unchecked(parent as *mut P::Target),
                                tree: self,
                            });
                        }
                        Ordering::Less => {
                            let left = (*parent).get_node().get_child(Direction::Left);
                            if left.is_null() {
                                return Entry::Vacant(VacantEntry {
                                    node: parent,
                                    direction: Direction::Left,
                                    tree: self,
                                    key,
                                });
                            }
                            parent = left;
                        }
                        Ordering::Greater => {
                            let right = (*parent).get_node().get_child(Direction::Right);
                            if right.is_null() {
                                return Entry::Vacant(VacantEntry {
                                    node: parent,
                                    direction: Direction::Right,
                                    tree: self,
                                    key,
                                });
                            }
                            parent = right;
                        }
                    }
                }
            }
        } else {
            return Entry::Vacant(VacantEntry {
                node: null_mut(),
                direction: Direction::Right,
                tree: self,
                key,
            });
        }
    }

    #[inline]
    pub fn get<'a, K>(&'a self, key: &K) -> Option<NodeRef<'a, P>>
    where
        P::Target: Borrow<K>,
        K: Ord,
    {
        self.get_with(|node| key.cmp(node.borrow()))
    }

    pub fn get_with<'a, F>(&'a self, cmp_f: F) -> Option<NodeRef<'a, P>>
    where
        F: Fn(&P::Target) -> Ordering,
    {
        unsafe {
            if !self.root.is_null() {
                let mut node_data = self.root;
                loop {
                    match cmp_f((&*node_data).as_ref()) {
                        Ordering::Equal => {
                            return Some(NodeRef::from(node_data));
                        }
                        Ordering::Less => {
                            let node = (*node_data).get_node();
                            let left = node.get_child(Direction::Left);
                            if left.is_null() {
                                return None;
                            }
                            node_data = left;
                        }
                        Ordering::Greater => {
                            let node = (*node_data).get_node();
                            let right = node.get_child(Direction::Right);
                            if right.is_null() {
                                return None;
                            }
                            node_data = right;
                        }
                    }
                }
            } else {
                None
            }
        }
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn _insert(
        &mut self,
        new_data: P,
        parent: *mut P::Target, // parent
        mut which_child: Direction,
    ) {
        let mut new_balance: i8;
        let new_ptr = new_data.into_raw() as *mut P::Target;

        if parent.is_null() {
            if self.count > 0 {
                panic!("insert into a tree size {} with empty where.node", self.count);
            }
            self.root = new_ptr;
            self.count += 1;
            return;
        }

        let node = unsafe { (*new_ptr).get_node() };
        let parent_node = unsafe { (*parent).get_node() };
        node.parent = parent;
        parent_node.set_child(which_child, new_ptr);
        self.count += 1;

        /*
         * Now, back up the tree modifying the balance of all nodes above the
         * insertion point. If we get to a highly unbalanced ancestor, we
         * need to do a rotation.  If we back out of the tree we are done.
         * If we brought any subtree into perfect balance (0), we are also done.
         */
        let mut data: *mut P::Target = parent;
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
    /// before Direction::After, Direction::Before) the data "here".
    ///
    /// For range-tree scenario
    ///
    /// Insertions can only be done at empty leaf points in the tree, therefore
    /// if the given child of the node is already present we move to either
    /// the AVL_PREV or AVL_NEXT and reverse the insertion direction. Since
    /// every other node in the tree is a leaf, this always works.
    unsafe fn _insert_here(&mut self, new_data: P, here: NonNull<P::Target>, direction: Direction) {
        let mut dir_child = direction;
        unsafe {
            let child = here.as_ref().get_node().get_child(dir_child);
            let parent;
            if child.is_null() {
                parent = here;
            } else {
                dir_child = dir_child.reverse();
                parent = self.bottom_child(NonNull::new_unchecked(child), dir_child);
            }
            self._insert(new_data, parent.as_ptr(), dir_child);
        }
    }

    // set child and both child's parent
    #[inline(always)]
    fn set_child2(
        &mut self, node: &mut AvlNode<P::Target, Tag>, dir: Direction, child: *mut P::Target,
        parent: *mut P::Target,
    ) {
        if !child.is_null() {
            unsafe { (*child).get_node().parent = parent };
        }
        node.set_child(dir, child);
    }

    #[inline(always)]
    fn parent_direction(&self, data: *mut P::Target, parent: *mut P::Target) -> Direction {
        if !parent.is_null() {
            let parent_node = unsafe { (*parent).get_node() };
            if parent_node.left == data {
                return Direction::Left;
            }
            if parent_node.right == data {
                return Direction::Right;
            }
            panic!("invalid avl tree, node {:p}, parent {:p}", data, parent);
        }
        // this just follow zfs
        Direction::Left
    }

    #[inline(always)]
    fn parent_direction2(&self, data: *mut P::Target) -> Direction {
        let node = unsafe { (*data).get_node() };
        let parent = node.get_parent();
        if !parent.is_null() {
            return self.parent_direction(data, parent);
        }
        // this just follow zfs
        Direction::Left
    }

    #[inline]
    fn rotate(&mut self, data: *mut P::Target, balance: i8) -> bool {
        /* when balance = -2, left will be 0 */
        let dir = if balance < 0 { Direction::Left } else { Direction::Right };
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
                child_node.parent = null_mut();
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
            g_child_node.parent = null_mut();
            self.root = g_child;
        }
        true
    }

    /// Requires `del` to be a valid pointer to a node in this tree.
    ///
    /// # Safety
    ///
    /// It does not drop the node data, only unlinks it.
    /// Caller is responsible for re-taking ownership (e.g. via from_raw) and dropping if needed.
    ///
    /// For Arc/Rc, use [Self::remove_ref()] instead.
    ///
    pub(crate) unsafe fn _remove(&mut self, del: *mut P::Target) {
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
            self.root = null_mut();
            self.count = 0;
            unsafe { (*del).get_node().detach() };
            return;
        }
        let mut which_child: Direction;

        // Use reference directly to get node, avoiding unsafe dereference of raw pointer
        let del_node = unsafe { (*del).get_node() };

        let node_swap_flag = !del_node.left.is_null() && !del_node.right.is_null();

        if node_swap_flag {
            let dir: Direction = balance_to_child!(del_node.balance + 1);
            let child_temp = del_node.get_child(dir);

            let dir_inverse: Direction = dir.reverse();
            let child = self
                .bottom_child(unsafe { NonNull::new_unchecked(child_temp) }, dir_inverse)
                .as_ptr();

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
                Direction::Left
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
                which_child = Direction::Right;
            } else {
                which_child = Direction::Left;
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
                which_child = Direction::Left;
            }
        }

        // Here we know "delete" is at least partially a leaf node. It can
        // be easily removed from the tree.
        let parent: *mut P::Target = del_node.get_parent();

        let imm_data: *mut P::Target =
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
            let mut node_data: *mut P::Target = parent;
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
            debug_assert!(self.count > 0);
            self.count -= 1;
            self.root = imm_data;
        }
        if self.root.is_null() && self.count > 0 {
            panic!("AvlTree {} nodes left after remove but tree.root == nil", self.count);
        }
        del_node.detach();
    }

    #[inline(always)]
    fn bottom_child(&self, mut data: NonNull<P::Target>, dir: Direction) -> NonNull<P::Target> {
        loop {
            unsafe {
                let child = data.as_ref().get_node().get_child(dir);
                if !child.is_null() {
                    data = NonNull::new_unchecked(child as *mut P::Target);
                } else {
                    return data;
                }
            }
        }
    }

    /// return a iterator to get the reference
    ///
    /// NOTE: If you use the [Iterator] interface (for iteration), you only get &P::Target.
    ///
    /// you can use [AvlIter::next_ref()] to get &P.
    #[inline]
    pub fn iter(&self) -> AvlIter<'_, P, Tag> {
        let first_p = if !self.root.is_null() {
            Some(self.bottom_child(
                unsafe { NonNull::new_unchecked(self.root as *mut P::Target) },
                Direction::Left,
            ))
        } else {
            None
        };
        AvlIter::new(self, first_p, Direction::Right)
    }

    /// return a reversed iterator to get the reference.
    ///
    ///
    /// NOTE: If you use the [Iterator] interface (for iteration), you only get &P::Target.
    ///
    /// you can use [AvlIter::next_ref()] to get &P.
    #[inline]
    pub fn iter_rev(&self) -> AvlIter<'_, P, Tag> {
        let last_p = if !self.root.is_null() {
            Some(self.bottom_child(
                unsafe { NonNull::new_unchecked(self.root as *mut P::Target) },
                Direction::Right,
            ))
        } else {
            None
        };
        AvlIter::new(self, last_p, Direction::Left)
    }

    #[inline]
    pub fn prev<'a>(&'a self, data: &'a P::Target) -> Option<NodeRef<'a, P>> {
        if let Some(p) = self._walk_dir(data.into(), Direction::Left) {
            Some(NodeRef::from(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn next<'a>(&'a self, data: &'a P::Target) -> Option<NodeRef<'a, P>> {
        if let Some(p) = self._walk_dir(data.into(), Direction::Right) {
            Some(NodeRef::from(p.as_ptr()))
        } else {
            None
        }
    }

    fn _walk_dir(
        &self, mut data_ptr: NonNull<P::Target>, dir: Direction,
    ) -> Option<NonNull<P::Target>> {
        let dir_inverse = dir.reverse();
        let node = unsafe { data_ptr.as_ref().get_node() };
        let temp = node.get_child(dir);
        if !temp.is_null() {
            unsafe {
                Some(self.bottom_child(NonNull::new_unchecked(temp as *mut P::Target), dir_inverse))
            }
        } else {
            let mut parent = node.parent;
            if parent.is_null() {
                return None;
            }
            loop {
                let pdir = self.parent_direction(data_ptr.as_ptr(), parent);
                if pdir == dir_inverse {
                    return Some(unsafe { NonNull::new_unchecked(parent as *mut P::Target) });
                }
                let data_ptr_raw = parent as *mut P::Target;
                parent = unsafe { (*parent).get_node() }.parent;
                if parent.is_null() {
                    return None;
                }
                unsafe {
                    data_ptr = NonNull::new_unchecked(data_ptr_raw);
                }
            }
        }
    }

    #[inline]
    pub fn first<'a>(&'a self) -> Option<NodeRef<'a, P>> {
        if !self.root.is_null() {
            let p = self.bottom_child(
                unsafe { NonNull::new_unchecked(self.root as *mut P::Target) },
                Direction::Left,
            );
            Some(NodeRef::<'a, P>::from(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn last<'a>(&'a self) -> Option<NodeRef<'a, P>> {
        if !self.root.is_null() {
            let p = self.bottom_child(
                unsafe { NonNull::new_unchecked(self.root as *mut P::Target) },
                Direction::Right,
            );
            Some(NodeRef::<'a, P>::from(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn validate(&self)
    where
        P::Target: Ord,
    {
        self.validate_with(P::Target::cmp)
    }

    pub fn validate_with<F>(&self, cmp_f: F)
    where
        F: Fn(&P::Target, &P::Target) -> Ordering,
    {
        let validate_node = |data: *mut P::Target| unsafe {
            let node = (*data).get_node();
            let left = node.left;
            if !left.is_null() {
                assert!(cmp_f(&*left, &*data) != Ordering::Greater);
                assert_eq!((*left).get_node().get_parent(), data);
            }
            let right = node.right;
            if !right.is_null() {
                assert!(cmp_f(&*right, &*data) != Ordering::Less);
                assert_eq!((*right).get_node().get_parent(), data);
            }
        };
        let c = {
            #[cfg(feature = "std")]
            {
                ((self.len() + 10) as f32).log2() as usize
            }
            #[cfg(not(feature = "std"))]
            {
                100
            }
        };
        let mut stack: Vec<*mut P::Target> = Vec::with_capacity(c);
        if self.root.is_null() {
            assert_eq!(self.count, 0);
            return;
        }
        let mut data = self.root;
        let mut visited = 0;
        loop {
            if !data.is_null() {
                let left = unsafe { (*data).get_node() }.get_child(Direction::Left);
                if !left.is_null() {
                    stack.push(data);
                    data = left;
                    continue;
                }
            } else if !stack.is_empty() {
                data = stack.pop().unwrap();
            } else {
                break;
            }
            validate_node(data);
            visited += 1;
            data = unsafe { (*data).get_node() }.get_child(Direction::Right);
        }
        assert_eq!(visited, self.count);
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

/// A Reference to `P` recover from raw pointer
pub struct NodeRef<'a, P> {
    node: ManuallyDrop<P>,
    _phan: PhantomData<&'a P>,
}

impl<'a, P> AsRef<P> for NodeRef<'a, P> {
    #[inline(always)]
    fn as_ref(&self) -> &P {
        self.node.deref()
    }
}

impl<'a, P: Pointer> Deref for NodeRef<'a, P> {
    type Target = P;

    #[inline(always)]
    fn deref(&self) -> &P {
        &self.node
    }
}

impl<'a, P: Pointer> From<*mut P::Target> for NodeRef<'a, P> {
    #[inline]
    fn from(p: *mut P::Target) -> Self {
        Self { node: ManuallyDrop::new(unsafe { P::from_raw(p) }), _phan: Default::default() }
    }
}
