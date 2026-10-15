#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]
//! An intrusive AVL tree implementation.
//!
//! The algorithm origin from open-zfs
//!
//! benchmarks: <https://github.com/NaturalIO/embed-collections-rs/wiki>
//!
//! The ordering of avl tree is defined by [AvlItem] trait. There're two usage:
//! - borrow field as key from the node struct
//! - impl Ord for struct itself
//!
//! We provide Entry API to achieve `CursorMut` like ability, you can use the following combination:
//! - [AvlTree::entry], [AvlTree::first_entry], [AvlTree::last_entry]
//! - [OccupiedEntry::peek_prev], [OccupiedEntry::peek_next]
//! - [OccupiedEntry::move_prev], [OccupiedEntry::move_next]
//! - [OccupiedEntry::insert_prev_unchecked], [OccupiedEntry::insert_next_unchecked]  ( does not change current `OccupiedEntry`)
//! - [OccupiedEntry::insert_move_prev_unchecked], OccupiedEntry::insert_move_next_unchecked] (return the newlly inserted OccupiedEntry, reduce additional seek cost)
//! - [OccupiedEntry::remove_prev] , [OccupiedEntry::remove_next] (does not change current `OccupiedEntry`)
//!
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
    fmt, mem,
    ops::Deref,
    ptr::{NonNull, null_mut},
};
use pointers::{CloneablePointer, Pointer};

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

/// logging macro for development
#[macro_export(local_inner_macros)]
macro_rules! trace_log {
    ($($arg:tt)+)=>{
        #[cfg(feature="trace_log")]
        {
            log::debug!($($arg)+);
        }
    };
}

pub(crate) const DIR_LEFT: Dir = Dir(false);
pub(crate) const DIR_RIGHT: Dir = Dir(true);

#[derive(PartialEq, Debug, Copy, Clone)]
pub(crate) struct Dir(bool);

impl Dir {
    #[inline(always)]
    const fn to_usize(&self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    const fn reverse(&self) -> Self {
        Self(!self.0)
    }

    #[inline(always)]
    fn to_balance(&self) -> i8 {
        if *self == DIR_LEFT { -1 } else { 1 }
    }
}

impl From<i8> for Dir {
    #[inline(always)]
    fn from(i: i8) -> Self {
        Self(i != 0)
    }
}

impl From<bool> for Dir {
    #[inline(always)]
    fn from(i: bool) -> Self {
        Self(i)
    }
}

macro_rules! balance_to_child {
    ($balance: expr) => {{ ($balance > 1).into() }};
}

pub struct AvlNode<T: AvlItem<Tag>, Tag> {
    pub parent: *mut T,
    pub children: [*mut T; 2],
    pub balance: i8,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T: AvlItem<Tag> + Send, Tag> Send for AvlNode<T, Tag> {}

impl<T: AvlItem<Tag>, Tag> AvlNode<T, Tag> {
    #[inline(always)]
    pub fn detach(&mut self) {
        self.children = [null_mut(), null_mut()];
        self.parent = null_mut();
        self.balance = 0;
    }

    #[inline(always)]
    fn get_child(&self, dir: Dir) -> *mut T {
        unsafe { *self.children.get_unchecked(dir.to_usize()) }
    }

    #[inline(always)]
    fn set_child(&mut self, dir: Dir, child: *mut T) {
        self.children[dir.to_usize()] = child;
    }

    #[inline(always)]
    fn left(&self) -> *mut T {
        self.children[0]
    }

    #[inline(always)]
    fn right(&self) -> *mut T {
        self.children[1]
    }

    // set child and both child's parent
    #[inline(always)]
    fn set_child2<P: Pointer<Target = T>>(
        &mut self, dir: Dir, child: *mut P::Target, parent: *mut P::Target,
    ) {
        if !child.is_null() {
            unsafe { (*child).get_node().parent = parent };
        }
        self.set_child(dir, child);
    }

    #[inline(always)]
    fn get_parent(&self) -> *mut T {
        self.parent
    }

    #[inline(always)]
    fn _child_direction(&self, child_p: *mut T) -> Dir {
        // this is AvlTree::parent_direction in previous version
        let is_right = self.children[1] == child_p;
        #[cfg(debug_assertions)]
        {
            if !is_right {
                debug_assert!(self.children[0] == child_p);
            }
        }
        is_right.into()
    }

    #[inline(always)]
    fn child_direction(parent: *mut T, child_p: *mut T) -> Dir {
        if !parent.is_null() {
            unsafe { (*parent).get_node() }._child_direction(child_p)
        } else {
            DIR_LEFT
        }
    }

    #[inline(always)]
    fn parent_direction(node: *mut T) -> Dir {
        // this is AvlTree::parent_direction2 in previous version
        let parent = unsafe { (*node).get_node() }.get_parent();
        Self::child_direction(parent, node)
    }

    // Swap two node but not there value
    #[inline(always)]
    pub fn swap(&mut self, other: &mut AvlNode<T, Tag>) {
        mem::swap(self, other);
    }
}

impl<T: AvlItem<Tag>, Tag> Default for AvlNode<T, Tag> {
    fn default() -> Self {
        Self {
            children: [null_mut(), null_mut()],
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
        if !self.left().is_null() {
            write!(f, "left: {:p}", self.left())?;
        } else {
            write!(f, "left: none ")?;
        }

        if !self.right().is_null() {
            write!(f, "right: {:p}", self.right())?;
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

impl<P, Tag> fmt::Debug for AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag> + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let _ = write!(f, "AvlTree{{");
        if self.count > 0 {
            let mut iter = self.iter();
            loop {
                let node = iter.next().unwrap();
                let _ = write!(f, "{:?}", node.as_ref().as_ref());
                if iter.len() > 0 {
                    let _ = write!(f, ", ");
                } else {
                    break;
                }
            }
        }
        write!(f, "}}")
    }
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

    /// Adds a new node to the tree, requires P::Target has `Ord`.
    ///
    /// (If you want more freedom of Ordering, see also [Self::entry_with])
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
                    // match is actually better optimized than if-else or table mapping
                    let dir = match node.as_ref().cmp((&*parent).as_ref()) {
                        Ordering::Greater => DIR_RIGHT,
                        Ordering::Less => DIR_LEFT,
                        Ordering::Equal => return Err(node),
                    };
                    let child = (*parent).get_node().get_child(dir);
                    if !child.is_null() {
                        parent = child;
                    } else {
                        self._insert(node.into_raw() as *mut P::Target, parent, dir);
                        return Ok(());
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
        if let Entry::Occupied(ent) = self.entry_with::<&K, _>(key, _cmp) {
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
        if let Entry::Occupied(ent) = self.entry_with::<&P::Target, _>(node.as_ref(), _cmp) {
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
        self.entry_with(key, |_key: &K, node: &P::Target| _key.cmp(node.borrow()))
    }

    /// Searches for an element in the tree with `key` and custom compare function.
    #[inline]
    pub fn entry_with<'a, K, F>(&'a mut self, key: K, cmp_f: F) -> Entry<'a, P, Tag, K>
    where
        F: Fn(&K, &P::Target) -> Ordering,
    {
        if !self.root.is_null() {
            let mut parent = self.root;
            loop {
                // match is actually better optimized than if-else or table mapping
                let dir = match cmp_f(&key, unsafe { &*parent }.as_ref()) {
                    Ordering::Greater => DIR_RIGHT,
                    Ordering::Less => DIR_LEFT,
                    Ordering::Equal => {
                        return Entry::Occupied(OccupiedEntry {
                            node: unsafe { NonNull::new_unchecked(parent) },
                            tree: self,
                        });
                    }
                };
                let child = unsafe { (*parent).get_node() }.get_child(dir);
                if !child.is_null() {
                    parent = child;
                } else {
                    return Entry::Vacant(VacantEntry {
                        node: parent,
                        direction: dir,
                        tree: self,
                        key,
                    });
                }
            }
        } else {
            Entry::Vacant(VacantEntry { node: null_mut(), direction: DIR_RIGHT, tree: self, key })
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
        if !self.root.is_null() {
            let mut node = self.root;
            loop {
                // match is actually better optimized than if-else or table mapping
                let dir = match cmp_f(unsafe { &*node }.as_ref()) {
                    Ordering::Greater => DIR_RIGHT,
                    Ordering::Less => DIR_LEFT,
                    Ordering::Equal => return Some(NodeRef::new(node)),
                };
                let child = unsafe { (*node).get_node() }.get_child(dir);
                if !child.is_null() {
                    node = child;
                } else {
                    return None;
                }
            }
        } else {
            None
        }
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[inline]
    pub(crate) fn _insert(
        &mut self,
        new_ptr: *mut P::Target,
        parent: *mut P::Target, // parent
        mut which_child: Dir,
    ) {
        if !parent.is_null() {
            let mut new_balance: i8;
            unsafe { (*new_ptr).get_node() }.parent = parent;
            let parent_node = unsafe { (*parent).get_node() };
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
                new_balance = old_balance + which_child.to_balance();
                if new_balance == 0 {
                    node.balance = 0;
                    return;
                }
                if old_balance != 0 {
                    break;
                }
                node.balance = new_balance;
                let parent_ptr = node.get_parent();
                if parent_ptr.is_null() {
                    return;
                }
                which_child = unsafe { (*parent_ptr).get_node() }._child_direction(data);
                data = parent_ptr;
            }
            self.rotate(data, new_balance);
        } else {
            debug_assert_eq!(self.count, 0);
            self.root = new_ptr;
            self.count += 1;
        }
    }

    /// Insert `new_ptr` in `tree` in the given `direction` against the node `here`.
    ///
    /// For range-tree scenario
    ///
    /// Insertions can only be done at empty leaf points in the tree, therefore
    /// if the given child of the node is already present we move to either
    /// the AVL_PREV or AVL_NEXT and reverse the insertion direction. Since
    /// every other node in the tree is a leaf, this always works.
    unsafe fn _insert_here(
        &mut self, new_ptr: *mut P::Target, here: NonNull<P::Target>, direction: Dir,
    ) {
        crate::trace_log!("_insert_here {new_ptr:p} here {here:p} dir {direction:?}");
        let mut dir_child = direction;
        unsafe {
            let child = here.as_ref().get_node().get_child(dir_child);
            let parent;
            if child.is_null() {
                crate::trace_log!("direct at here {here:p}");
                parent = here;
            } else {
                dir_child = dir_child.reverse();
                parent = self.bottom_child(NonNull::new_unchecked(child), dir_child);
                crate::trace_log!("find bottom {parent:p}");
            }
            self._insert(new_ptr, parent.as_ptr(), dir_child);
        }
    }

    #[inline]
    fn rotate(&mut self, data: *mut P::Target, balance: i8) -> bool {
        /* when balance = -2, left will be 0 */
        //let dir = if balance < 0 { DIR_LEFT } else { DIR_RIGHT };
        let dir: Dir = (balance >= 0).into();
        let node = unsafe { (*data).get_node() };

        let parent = node.get_parent();
        let dir_inverse = dir.reverse();
        let left_heavy = balance >> 1;
        let right_heavy = -left_heavy;

        let child = node.get_child(dir);
        let child_node = unsafe { (*child).get_node() };
        let mut child_balance = child_node.balance;

        let which_child = AvlNode::<P::Target, Tag>::child_direction(parent, data);

        // node is overly left heavy, the left child is balanced or also left heavy.
        if child_balance != right_heavy {
            child_balance += right_heavy;

            let c_right = child_node.get_child(dir_inverse);
            node.set_child2::<P>(dir, c_right, data);
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

        node.set_child2::<P>(dir, g_right, data);
        child_node.set_child2::<P>(dir_inverse, g_left, child);

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
        let mut which_child: Dir;

        // Use reference directly to get node, avoiding unsafe dereference of raw pointer
        let del_node = unsafe { (*del).get_node() };

        let node_swap_flag = !del_node.left().is_null() && !del_node.right().is_null();

        if node_swap_flag {
            let dir: Dir = balance_to_child!(del_node.balance + 1);
            let child_temp = del_node.get_child(dir);

            let dir_inverse: Dir = dir.reverse();
            let child = self
                .bottom_child(unsafe { NonNull::new_unchecked(child_temp) }, dir_inverse)
                .as_ptr();

            // Fix Miri UB: Avoid calling parent_direction(child) if child's parent is del,
            // because that would create a aliasing &mut ref to del while we hold del_node.
            let dir_child_temp = if child == child_temp {
                dir
            } else {
                AvlNode::<P::Target, Tag>::parent_direction(child)
            };

            // Fix Miri UB: Do not call parent_direction(del) as it creates a new &mut AvlNode
            // alias while we hold del_node. Use del_node to find parent direction.
            let parent = del_node.get_parent();
            let dir_child_del = AvlNode::<P::Target, Tag>::child_direction(parent, del);

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
            // if right exist, go to right
            which_child = Dir(!del_node.right().is_null());
            let child = del_node.get_child(which_child);
            if !child.is_null() {
                unsafe { (*child).get_node() }.parent = del;
            }
            which_child = dir_child_temp;
        } else {
            let parent = del_node.get_parent();
            which_child = AvlNode::<P::Target, Tag>::child_direction(parent, del);
        }

        // Here we know "delete" is at least partially a leaf node. It can
        // be easily removed from the tree.
        let parent: *mut P::Target = del_node.get_parent();

        let mut imm_data: *mut P::Target = del_node.left();
        if !imm_data.is_null() {
            let imm_node = unsafe { (*imm_data).get_node() };
            imm_node.parent = parent;
        } else {
            imm_data = del_node.right();
            if !imm_data.is_null() {
                let imm_node = unsafe { (*imm_data).get_node() };
                imm_node.parent = parent;
            }
        }
        // Connect parent directly to node (leaving out delete).

        if !parent.is_null() {
            assert!(self.count > 0);
            self.count -= 1;

            let parent_node = unsafe { (*parent).get_node() };
            parent_node.set_child(which_child, imm_data);

            //Since the subtree is now shorter, begin adjusting parent balances
            //and performing any needed rotations.
            let mut node_data: *mut P::Target = parent;
            loop {
                // Move up the tree and adjust the balance.
                // Capture the parent and which_child values for the next
                // iteration before any rotations occur.
                let node = unsafe { (*node_data).get_node() };
                let balance_delta = -which_child.to_balance();
                let old_balance = node.balance;

                //If a node was in perfect balance but isn't anymore then
                //we can stop, since the height didn't change above this point
                //due to a deletion.
                if old_balance == 0 {
                    node.balance = balance_delta;
                    break;
                }
                let new_balance = old_balance + balance_delta;

                let parent = node.get_parent();
                which_child = AvlNode::<P::Target, Tag>::child_direction(parent, node_data);

                //If the new balance is zero, we don't need to rotate
                //else
                //need a rotation to fix the balance.
                //If the rotation doesn't change the height
                //of the sub-tree we have finished adjusting.
                if new_balance == 0 {
                    node.balance = 0;
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
    fn bottom_child(&self, mut data: NonNull<P::Target>, dir: Dir) -> NonNull<P::Target> {
        loop {
            unsafe {
                let child = data.as_ref().get_node().get_child(dir);
                if !child.is_null() {
                    data = NonNull::new_unchecked(child);
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
            Some(self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT))
        } else {
            None
        };
        AvlIter::new(self, first_p, DIR_RIGHT)
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
            Some(self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT))
        } else {
            None
        };
        AvlIter::new(self, last_p, DIR_LEFT)
    }

    #[inline]
    pub fn prev<'a>(&'a self, data: &'a P::Target) -> Option<NodeRef<'a, P>> {
        self._walk_dir(data.into(), DIR_LEFT).map(|p| NodeRef::new(p.as_ptr()))
    }

    #[inline]
    pub fn next<'a>(&'a self, data: &'a P::Target) -> Option<NodeRef<'a, P>> {
        self._walk_dir(data.into(), DIR_RIGHT).map(|p| NodeRef::new(p.as_ptr()))
    }

    fn _walk_dir(&self, mut data_ptr: NonNull<P::Target>, dir: Dir) -> Option<NonNull<P::Target>> {
        let dir_inverse = dir.reverse();
        let node = unsafe { data_ptr.as_ref().get_node() };
        let temp = node.get_child(dir);
        if !temp.is_null() {
            unsafe { Some(self.bottom_child(NonNull::new_unchecked(temp), dir_inverse)) }
        } else {
            let mut parent = node.parent;
            if parent.is_null() {
                return None;
            }
            loop {
                let pdir = AvlNode::<P::Target, Tag>::child_direction(parent, data_ptr.as_ptr());
                if pdir == dir_inverse {
                    return Some(unsafe { NonNull::new_unchecked(parent) });
                }
                let data_ptr_raw = parent;
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
            let p = self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT);
            Some(NodeRef::<'a, P>::new(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn last<'a>(&'a self) -> Option<NodeRef<'a, P>> {
        if !self.root.is_null() {
            let p = self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT);
            Some(NodeRef::<'a, P>::new(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn first_entry<'a>(&'a mut self) -> Option<OccupiedEntry<'a, P, Tag>> {
        if !self.root.is_null() {
            let p = self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT);
            Some(OccupiedEntry { node: p, tree: self })
        } else {
            None
        }
    }

    #[inline]
    pub fn last_entry<'a>(&'a mut self) -> Option<OccupiedEntry<'a, P, Tag>> {
        if !self.root.is_null() {
            let p = self.bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT);
            Some(OccupiedEntry { node: p, tree: self })
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
            let left = node.left();
            if !left.is_null() {
                assert!(cmp_f(&*left, &*data) != Ordering::Greater);
                assert_eq!((*left).get_node().get_parent(), data);
            }
            let right = node.right();
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
                let left = unsafe { (*data).get_node() }.get_child(DIR_LEFT);
                if !left.is_null() {
                    crate::trace_log!("validate: push {data:p}");
                    stack.push(data);
                    data = left;
                    continue;
                }
            } else if !stack.is_empty() {
                data = stack.pop().unwrap();
            } else {
                break;
            }
            crate::trace_log!("validate: {data:p}");
            validate_node(data);
            visited += 1;
            data = unsafe { (*data).get_node() }.get_child(DIR_RIGHT);
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

/// A Reference to `P`
pub struct NodeRef<'a, P: Pointer> {
    node: NonNull<P::Target>,
    _phan: PhantomData<&'a P>,
}

impl<'a, P: Pointer> AsRef<P::Target> for NodeRef<'a, P> {
    #[inline(always)]
    fn as_ref(&self) -> &P::Target {
        unsafe { self.node.as_ref() }
    }
}

impl<'a, P: Pointer> Deref for NodeRef<'a, P> {
    type Target = P::Target;

    #[inline(always)]
    fn deref(&self) -> &P::Target {
        unsafe { self.node.as_ref() }
    }
}

impl<'a, P: Pointer> NodeRef<'a, P> {
    #[inline]
    fn new(p: *mut P::Target) -> Self {
        Self { node: unsafe { NonNull::new_unchecked(p) }, _phan: Default::default() }
    }
}

impl<'a, P: CloneablePointer> NodeRef<'a, P> {
    /// If P is `Rc`/`Arc`, you can clone the reference out
    #[inline]
    pub fn clone_ref(&self) -> P {
        unsafe { CloneablePointer::from_raw_and_clone(self.node.as_ptr()) }
    }
}
