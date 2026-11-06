#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]
//! An intrusive AVL tree implementation.
//!
//! The algorithm take reference from open-zfs, with optimization in struct fields, removal and rotation.
//!
//! benchmarks: <https://github.com/NaturalIO/embed-collections-rs/wiki>
//!
//! The ordering of avl tree is defined by [AvlItem] trait. There're two usage:
//! - borrow field as key from the node struct
//! - impl Ord for struct itself
//!
//! Refer to the example of [AvlItem] document.
//!
//! ## Duplicated value or unique value
//!
//! Whether or not a tree support duplicated value, depends on the `Ord` implementation.
//! You decide whether or not taking the node address into comparison.
//!
//! Summary of behavior differences:
//!
//! - [add()](AvlTree::add) will return `Err()` when Ord return cmp::Ordering::Equal, ensuring a unique tree.
//!   - Use macro [impl_ord_with_borrow_unique] To restrict unique value in a tree,
//!   - Use macro [impl_ord_with_borrow_and_addr] to allow duplicate value in a tree
//!     - which implement `Ord` for `P::Target` to compare the address when value is equal.
//! - [remove()](AvlTree::remove), will remove node by reference, regardless whether there's same
//!   value.
//! - [remove_by_key()](AvlTree::remove_by_key), will match any value equals to key, but execute only once.
//! - [get()](AvlTree::get), [get_with](AvlTree::get_with) will find the first node with value match the key
//! - [entry()](AvlTree::entry), [entry_with](AvlTree::entry_with) will find the first node with value match
//!   the key
//!
//! ## Internal mutability of value
//!
//! When it's possible one or multiple nodes value changed after inserted, making the tree out of order.
//! The only valid usage is [removing](AvlTree::remove) all of the changed nodes by reference, before any further lookups or insertions.
//!
//! ## Entry API
//!
//! We provide Entry API to achieve `CursorMut` like ability, you can use the following combination:
//! - [AvlTree::entry], [AvlTree::first_entry], [AvlTree::last_entry]
//! - [OccupiedEntry::peek_prev], [OccupiedEntry::peek_next]
//! - [OccupiedEntry::move_prev], [OccupiedEntry::move_next]
//! - [OccupiedEntry::insert_prev_unchecked], [OccupiedEntry::insert_next_unchecked]  ( does not change current `OccupiedEntry`)
//! - [OccupiedEntry::insert_move_prev_unchecked], OccupiedEntry::insert_move_next_unchecked] (return the newlly inserted OccupiedEntry, reduce additional seek cost)
//! - [OccupiedEntry::remove_prev] , [OccupiedEntry::remove_next] (does not change current `OccupiedEntry`)
//!
//! # Examples
//!
//! ## Using `Box` to search and remove by key
//!
//! ```rust
//! use embed_avl::{AvlTree, AvlItem, AvlNode, Entry, impl_ord_with_borrow_unique};
//! use core::cell::UnsafeCell;
//! use core::borrow::Borrow;
//! extern crate format_attr;
//!
//! #[derive(format_attr::DebugAttr)]
//! #[fmt("MyNode {value}")]
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<()>>,
//! }
//!
//! impl Borrow<i32> for MyNode {
//!     fn borrow(&self) -> &i32 {
//!         &self.value
//!     }
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! impl_ord_with_borrow_unique!(MyNode, i32);
//!
//! let mut tree = AvlTree::<Box<MyNode>, ()>::new();
//! tree.add(Box::new(MyNode { value: 10, avl_node: UnsafeCell::new(Default::default()) })).expect("adding");
//!
//! // Search and remove
//! if let Some(node) = tree.remove_by_key::<i32>(&10i32) {
//!     assert_eq!(node.value, 10);
//! }
//! assert!(tree.is_empty());
//! ```
//!
//! ## using `Arc` on a tree with duplicated value
//!
//! ```rust
//! use embed_avl::{AvlTree, AvlItem, AvlNode, Entry, impl_ord_with_borrow_and_addr};
//! use core::cell::UnsafeCell;
//! use core::borrow::Borrow;
//! extern crate format_attr;
//! extern crate alloc;
//! use alloc::sync::Arc;
//!
//! #[derive(format_attr::DebugAttr)]
//! #[fmt("MyNode {value}")]
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<()>>,
//! }
//!
//! impl Borrow<i32> for MyNode {
//!     fn borrow(&self) -> &i32 {
//!         &self.value
//!     }
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! impl_ord_with_borrow_and_addr!(MyNode, i32);
//!
//! let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
//! let node = Arc::new(MyNode { value: 42, avl_node: UnsafeCell::new(Default::default()) });
//!
//! tree.add(node.clone()).expect("adding");
//!
//! let node_dupl = Arc::new(MyNode { value: 42, avl_node: UnsafeCell::new(Default::default()) });
//! tree.add(node_dupl.clone()).expect("adding");
//! assert_eq!(tree.len(), 2);
//!
//! // Remove by reference (detach from avl tree)
//! tree.remove(&node);
//! assert_eq!(tree.len(), 1);
//! tree.remove(&node_dupl);
//! assert_eq!(tree.len(), 0);
//! ```
//!
//! ## Efficient bulk insertion
//!
//! ```rust
//! use embed_avl::{AvlTree, AvlItem, AvlNode, Entry};
//! use core::cell::UnsafeCell;
//! use core::borrow::Borrow;
//! extern crate format_attr;
//!
//! #[derive(format_attr::DebugAttr)]
//! #[fmt("MyNode {value}")]
//! struct MyNode {
//!     value: i32,
//!     avl_node: UnsafeCell<AvlNode<()>>,
//! }
//!
//! impl Borrow<i32> for MyNode {
//!     fn borrow(&self) -> &i32 {
//!         &self.value
//!     }
//! }
//!
//! unsafe impl AvlItem<()> for MyNode {
//!     fn get_node(&self) -> &mut AvlNode<()> {
//!         unsafe { &mut *self.avl_node.get() }
//!     }
//! }
//!
//! let mut tree = AvlTree::<Box<MyNode>, ()>::new();
//! let mut ent = tree.last_entry();
//!
//! // For bulk insertion, we don't need the Ord.
//! // produce a tree with duplicated value.
//! for i in 0..100 {
//!     ent = unsafe{ent.append_unchecked(
//!         Box::new(MyNode { value: i, avl_node: UnsafeCell::new(Default::default()) })
//!     )};
//!     ent = unsafe{ent.append_unchecked(
//!         Box::new(MyNode { value: i, avl_node: UnsafeCell::new(Default::default()) })
//!     )};
//! }
//! tree.validate_with(|this, other|{
//!     this.value.cmp(&other.value)
//! });
//!
//! // Search
//! if let Some(node) = tree.get::<i32>(&10) {
//!     assert_eq!(node.value, 10);
//! }
//! assert_eq!(tree.len(), 200);
//!
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

use alloc::collections::vec_deque::VecDeque;
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
/// use embed_avl::{AvlItem, AvlNode, impl_ord_with_borrow_unique};
/// extern crate format_attr;
/// use core::borrow::Borrow;
/// use core::cell::UnsafeCell;
///
/// #[derive(format_attr::DebugAttr)]
/// #[fmt("IntAvlNode {value}")]
/// pub struct IntAvlNode {
///     pub value: i64,
///     pub node: UnsafeCell<AvlNode<()>>,
/// }
///
/// unsafe impl AvlItem<()> for IntAvlNode {
///     fn get_node(&self) -> &mut AvlNode<()> {
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
/// impl_ord_with_borrow_unique!(IntAvlNode, i64);
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
///     node: UnsafeCell<AvlNode<()>>,
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
///     fn get_node(&self) -> &mut AvlNode<()> {
///         unsafe { &mut *self.node.get() }
///     }
/// }
/// ```
pub unsafe trait AvlItem<Tag>: Sized {
    fn get_node(&self) -> &mut AvlNode<Tag>;

    /// # Safety
    ///
    /// This is just map from raw pointer to `&mut AvlNode<Tag>`.
    ///
    /// You only have to implement this when using custom pointer type with abnormal address.
    #[allow(unsafe_op_in_unsafe_fn)]
    #[inline(always)]
    unsafe fn get_node_from_ptr<'a>(p: *mut u8) -> &'a mut AvlNode<Tag>
    where
        Self: 'a,
    {
        debug_assert!(!p.is_null());
        (*(p as *const Self)).get_node()
    }
}

/// Implement Ord with `Borrow<K>`
///
/// # Arguments
/// - cls: struct name
/// - key_type: `cls: Borrow<$key_type>`
#[macro_export]
macro_rules! impl_ord_with_borrow_unique {
    ($cls: ty, $key_type: ty) => {
        impl PartialOrd for $cls {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(Ord::cmp(self, other))
            }
        }
        impl PartialEq for $cls {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                Borrow::<$key_type>::borrow(self) == Borrow::<$key_type>::borrow(other)
            }
        }
        impl Eq for $cls {}

        impl Ord for $cls {
            #[inline]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                Borrow::<$key_type>::borrow(self).cmp(Borrow::<$key_type>::borrow(other))
            }
        }
    };
}

/// Implement Ord with `Borrow<K>`
///
/// # Arguments
/// - cls: struct name
/// - key_type: `cls: Borrow<$key_type>`
#[macro_export]
macro_rules! impl_ord_with_borrow_and_addr {
    ($cls: ty, $key_type: ty) => {
        impl PartialOrd for $cls {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(Ord::cmp(self, other))
            }
        }
        impl PartialEq for $cls {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                core::ptr::eq(self, other)
            }
        }
        impl Eq for $cls {}

        impl Ord for $cls {
            #[inline]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                let r = Borrow::<$key_type>::borrow(self).cmp(Borrow::<$key_type>::borrow(other));
                if r != core::cmp::Ordering::Equal {
                    r
                } else {
                    let this_addr = self as *const $cls as usize;
                    let other_addr = other as *const $cls as usize;
                    this_addr.cmp(&other_addr)
                }
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
    fn to_balance(&self) -> u8 {
        2 - (self.0 as u8)
    }
}

impl From<u8> for Dir {
    #[inline(always)]
    fn from(i: u8) -> Self {
        Self(i != 0)
    }
}

impl From<bool> for Dir {
    #[inline(always)]
    fn from(i: bool) -> Self {
        Self(i)
    }
}

macro_rules! get_node_t {
    ($p: expr, $T: ty, $Tag: ty) => {{ unsafe { <T as AvlItem<$Tag>>::get_node_from_ptr($p) } }};
}

macro_rules! get_node_p {
    ($p: expr, $P: ty, $Tag: ty) => {{
        #[allow(unused_unsafe)]
        unsafe {
            <<$P>::Target as AvlItem<$Tag>>::get_node_from_ptr($p)
        }
    }};
}

macro_rules! assert_balance {
    ($balance: expr) => {{
        debug_assert!((0..=2).contains(&$balance), "balance {} out of range", $balance);
    }};
}

pub(crate) use get_node_p;

pub struct AvlNode<Tag> {
    // on 64bit system, 8bit can be spared by pointer alignment,
    //   we pack parent direction and balance with parent pointer;
    // on 32bit system, only 4bit can be spared, we only pack balance.
    parent: usize,
    children: [*mut u8; 2],
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<Tag> Send for AvlNode<Tag> {}

const DIR_MASK: usize = 0x4usize;
#[cfg(target_pointer_width = "64")]
const POINTER_MASK: usize = !0x7;
#[cfg(not(target_pointer_width = "64"))]
const POINTER_MASK: usize = !0x3;

const BALANCE_MASK: usize = 0x3;

impl<Tag> AvlNode<Tag> {
    #[inline(always)]
    fn detach(&mut self) {
        *self = Self::default();
    }

    #[inline(always)]
    fn get_child(&self, dir: Dir) -> *mut u8 {
        unsafe { *self.children.get_unchecked(dir.to_usize()) }
    }

    #[inline(always)]
    fn get_balance(&self) -> u8 {
        (self.parent & BALANCE_MASK) as u8
    }

    #[inline(always)]
    fn set_balance(&mut self, balance: u8) {
        self.parent = (self.parent & (POINTER_MASK | DIR_MASK)) | (balance as usize);
    }

    #[inline(always)]
    fn set_child(&mut self, dir: Dir, child: *mut u8) {
        self.children[dir.to_usize()] = child;
    }

    #[inline(always)]
    fn left(&self) -> *mut u8 {
        self.children[0]
    }

    #[inline(always)]
    fn right(&self) -> *mut u8 {
        self.children[1]
    }

    // set child and both child's parent
    //
    // # Arguments:
    // - `parent`: this pointer to this node (we don't know the offset here)
    #[inline(always)]
    fn set_child2<T: AvlItem<Tag>>(&mut self, dir: Dir, child: *mut u8, parent: *mut u8) {
        if !child.is_null() {
            get_node_t!(child, T, Tag).set_parent(parent, dir);
        }
        self.set_child(dir, child);
    }

    // set child and both child's parent
    //
    // # Arguments:
    // - `parent`: this pointer to this node (we don't know the offset here)
    #[inline(always)]
    fn set_child2_not_null<T: AvlItem<Tag>>(&mut self, dir: Dir, child: *mut u8, parent: *mut u8) {
        debug_assert!(!child.is_null());
        get_node_t!(child, T, Tag).set_parent(parent, dir);
        self.set_child(dir, child);
    }

    #[inline(always)]
    fn get_parent(&self) -> *mut u8 {
        (self.parent & POINTER_MASK) as *mut u8
    }

    #[inline(always)]
    fn set_parent(&mut self, parent: *mut u8, _parent_dir: Dir) {
        #[cfg(target_pointer_width = "64")]
        {
            self.parent =
                (self.parent & BALANCE_MASK) | (parent as usize) | _parent_dir.to_usize() << 2;
        }
        #[cfg(not(target_pointer_width = "64"))]
        {
            self.parent = (self.parent & BALANCE_MASK) | parent as usize;
        }
    }

    #[inline(always)]
    fn clear_parent(&mut self) {
        self.parent &= BALANCE_MASK;
    }

    /// When parent is null, return DIR_LEFT (according of child_direction in previous code)
    ///
    /// this is AvlTree::parent_direction2 in previous version
    #[allow(clippy::extra_unused_type_parameters)]
    #[inline(always)]
    fn parent_direction<T: AvlItem<Tag>>(&self, _child_p: *mut u8) -> Dir {
        #[cfg(target_pointer_width = "64")]
        {
            ((self.parent & DIR_MASK) != 0).into()
        }
        #[cfg(not(target_pointer_width = "64"))]
        {
            let p = self.get_parent();
            if !p.is_null() {
                let parent_node = unsafe { <T as AvlItem<Tag>>::get_node_from_ptr(p) };
                let is_right = parent_node.children[1] == _child_p;
                {
                    #[cfg(debug_assertions)]
                    if !is_right {
                        debug_assert!(
                            parent_node.children[0] == _child_p,
                            "{self:?} find child {_child_p:p}"
                        );
                    }
                }
                is_right.into()
            } else {
                DIR_LEFT
            }
        }
    }

    // Swap two node but not there value
    #[inline(always)]
    pub fn swap(&mut self, other: &mut AvlNode<Tag>) {
        mem::swap(self, other);
    }
}

impl<Tag> Default for AvlNode<Tag> {
    fn default() -> Self {
        Self { children: [null_mut(), null_mut()], parent: 0, _phan: Default::default() }
    }
}

#[allow(unused_must_use)]
impl<Tag> fmt::Debug for AvlNode<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "( {:p} parent: {:p} balance: {}", self, self.get_parent(), self.get_balance())?;
        if !self.left().is_null() {
            write!(f, " left: {:p}", self.left())?;
        } else {
            write!(f, " left: none")?;
        }

        if !self.right().is_null() {
            write!(f, " right: {:p}", self.right())?;
        } else {
            write!(f, " right: none")?;
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
    root: *mut u8,
    count: usize,
    _phan: PhantomData<fn(P, &Tag)>,
}

impl<P, Tag> Default for AvlTree<P, Tag>
where
    P: Pointer + Send,
    P::Target: AvlItem<Tag>,
{
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
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

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Adds a new node to the tree, requires P::Target has `Ord`.
    /// It may allow duplicated values,
    /// as long is your `Ord` implementation takes the address of P into comparison.
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
                    let r = node.as_ref().cmp(&*(parent as *const P::Target));
                    if r != Ordering::Equal {
                        let dir = (r == Ordering::Greater).into();
                        let child = get_node_p!(parent, P, Tag).get_child(dir);
                        if !child.is_null() {
                            parent = child;
                        } else {
                            self._insert(node.into_raw() as *mut u8, parent, dir);
                            return Ok(());
                        }
                    } else {
                        return Err(node);
                    };
                }
            }
        } else {
            debug_assert_eq!(self.count, 0);
            self.root = node.into_raw() as *mut u8;
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

    /// remove a node from the tree directly (if P is multiple ownership)
    ///
    /// # Safety
    ///
    /// This function check `node` must already in this AVL tree, otherwise it will panic.
    ///
    /// When it's possible one or multiple nodes value changed, making the tree out of order,
    /// the only valid operation is removing all of the changed nodes, before any further insertion.
    #[inline]
    pub fn remove(&mut self, node: &P::Target)
    where
        P::Target: Ord,
    {
        unsafe {
            let this_p: *mut u8 = (node as *const P::Target) as *mut u8;
            // Safety:
            // Miri won't let us destroy *const P::Target as long is &P::Target is valid,
            // we get the pointer from parent node.
            let del_node = get_node_p!(this_p, P, Tag);
            let old_parent = del_node.get_parent();
            let del_dir = del_node.parent_direction::<P::Target>(this_p);
            let del_p = if !old_parent.is_null() {
                get_node_p!(old_parent, P, Tag).get_child(del_dir)
            } else {
                self.root
            };
            assert_eq!(del_p, this_p, "delete a node not in the tree {:p}", node);
            self._remove(del_node, old_parent, del_dir);
            let _ = P::from_raw(del_p as *const P::Target);
        }
    }

    /// Searches for an element in the tree with `key`, requires P::Target can borrow to `K` type,
    /// and have a total ordering by `K`.
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
                let r = cmp_f(&key, unsafe { &*(parent as *const P::Target) });
                let dir = if r != Ordering::Equal {
                    (r == Ordering::Greater).into()
                } else {
                    return Entry::Occupied(OccupiedEntry {
                        node: unsafe { NonNull::new_unchecked(parent) },
                        tree: self,
                    });
                };
                let child = get_node_p!(parent, P, Tag).get_child(dir);
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
    pub fn get<'a, K>(&'a self, key: &K) -> Option<AvlNodeRef<'a, P>>
    where
        P::Target: Borrow<K>,
        K: Ord,
    {
        self.get_with(|node| key.cmp(node.borrow()))
    }

    pub fn get_with<'a, F>(&'a self, cmp_f: F) -> Option<AvlNodeRef<'a, P>>
    where
        F: Fn(&P::Target) -> Ordering,
    {
        if !self.root.is_null() {
            let mut node = self.root;
            loop {
                // match is actually better optimized than if-else or table mapping
                let r = cmp_f(unsafe { &*(node as *const P::Target) });
                let dir = if r != Ordering::Equal {
                    (r == Ordering::Greater).into()
                } else {
                    return Some(AvlNodeRef::new(node));
                };
                let child = get_node_p!(node, P, Tag).get_child(dir);
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
    pub(crate) fn _insert(&mut self, new_ptr: *mut u8, parent: *mut u8, mut which_child: Dir) {
        debug_assert!(!new_ptr.is_null());
        if !parent.is_null() {
            let parent_node = get_node_p!(parent, P, Tag);
            parent_node.set_child2_not_null::<P::Target>(which_child, new_ptr, parent);
            self.count += 1;
            /*
             * Now, back up the tree modifying the balance of all nodes above the
             * insertion point. If we get to a highly unbalanced ancestor, we
             * need to do a rotation.  If we back out of the tree we are done.
             * If we brought any subtree into perfect balance (0), we are also done.
             */
            let mut data: *mut u8 = parent;
            loop {
                let node = get_node_p!(data, P, Tag);
                let old_balance = node.get_balance();
                let which_heavy = which_child.to_balance();
                if old_balance == 0 {
                    node.set_balance(which_heavy);
                    let parent_ptr = node.get_parent();
                    if !parent_ptr.is_null() {
                        which_child = node.parent_direction::<P::Target>(data);
                        data = parent_ptr;
                    } else {
                        return;
                    }
                } else if old_balance != which_heavy {
                    debug_assert!(old_balance != 0);
                    node.set_balance(0);
                    return;
                } else {
                    let parent_ptr = node.get_parent();
                    let parent_dir = node.parent_direction::<P::Target>(data);
                    self.rotate(data, which_child, parent_ptr, parent_dir);
                    return;
                }
            }
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
    unsafe fn _insert_here(&mut self, new_ptr: *mut u8, here: NonNull<u8>, direction: Dir) {
        crate::trace_log!("_insert_here {new_ptr:p} here {here:p} dir {direction:?}");
        let mut dir_child = direction;
        unsafe {
            let child = get_node_p!(here.as_ptr(), P, Tag).get_child(dir_child);
            let parent;
            if child.is_null() {
                crate::trace_log!("direct at here {here:p}");
                parent = here;
            } else {
                dir_child = dir_child.reverse();
                parent = Self::bottom_child(NonNull::new_unchecked(child), dir_child);
                crate::trace_log!("find bottom {parent:p}");
            }
            self._insert(new_ptr, parent.as_ptr(), dir_child);
        }
    }

    /// `dir`: the direction of the `data` node, data node is not balanced
    ///
    /// return whether balance after rotation
    #[inline]
    fn rotate(&mut self, data: *mut u8, dir: Dir, parent: *mut u8, parent_dir: Dir) -> bool {
        debug_assert!(!data.is_null());
        let dir_inverse = dir.reverse();
        let dir_bal = dir.to_balance();
        let inv_bal = dir_inverse.to_balance();
        debug_assert_eq!(dir_bal + inv_bal, 3);
        let node = get_node_p!(data, P, Tag);
        debug_assert_eq!(node.get_balance(), dir_bal);

        let child = node.get_child(dir);
        let child_node = get_node_p!(child, P, Tag);
        let child_balance = child_node.get_balance();
        assert_balance!(child_balance);

        if child_balance != inv_bal {
            crate::trace_log!(
                "rotate: case1 {data:p} {node:?} heavy_dir: {dir:?}  child {child_node:?}"
            );

            // child is balance, or the same heavy
            // we do single rotation.

            /*
             **case 1**: child_balance == dir_bal

               LL, RR, tree height reduce

               Before (LL, insert into A):

               node (bal=2 or 1, left heavy)
               /                     \
               child (bal=2 or 1)             D
               /       \              (h=c_h)
               A         c
               (c_h+1)   (c_h)

               After rotate RIGHT about node:

               child (bal=0)
               /          \
               A            node (bal=0)
               (c_h+1)       /          \
               c            D
               (c_h)        (c_h)

               height: c_h+2 → c_h+2 (decreased 1 relative to post-insert),
               continue rotate with parent.

            **case2**:  child_balance != dir_bal (child_balance == 0);

                    Before (delete from D, node over-left-heavy):
                            node (stored bal=2)
                            /                 \
                        child (bal=0)         D (h=c_h-1)
                        /       \
                        A         c
                    (c_h)     (c_h)

                After rotate RIGHT:
                        child (bal=1, right heavy)
                        /             \
                    A               node (bal=2, left heavy)
                    (c_h)            /             \
                                    c               D
                                    (c_h)          (c_h-1)

                height unchanged, stop iteration.
            */
            let is_diff = child_balance != dir_bal;
            //if is_diff {
            //    // child_balance == 0, dir_bal = 1, inv_bal = 2
            //    // child_balance == 0, dir_bal == 2, inv_bal = 1
            //    node.set_balance(dir_bal);
            //    child_node.set_balance(inv_bal);
            //} else {
            //    // child_balance == 1, dir_bal = 1, inv_bal = 2
            //    // child_balance == 2, dir_bal == 2, inv_bal = 1
            //    //node.set_balance(0);
            //    child_node.set_balance(0);
            //}
            node.set_balance(child_balance ^ dir_bal);
            child_node.set_balance(inv_bal & (-(is_diff as i8)) as u8);

            // move "cright" to be node's heavy child
            let c_right = child_node.get_child(dir_inverse);
            // move node to be child's right child
            child_node.set_child2_not_null::<P::Target>(dir_inverse, data, child);
            node.set_child2::<P::Target>(dir, c_right, data);

            // update the pointer into this subtree
            if !parent.is_null() {
                get_node_p!(parent, P, Tag)
                    .set_child2_not_null::<P::Target>(parent_dir, child, parent);
                return is_diff;
            } else {
                child_node.clear_parent();
                self.root = child;
                return true;
            }
        }
        crate::trace_log!(
            "rotate: case2 {data:p} {node:?} heavy_dir: {dir:?}  child {child_node:?}"
        );

        /* case 2 : When node is left heavy, but child is right heavy we use
        * a different rotation.
           Before (LR, insert into gL):
                node (bal=2, left heavy)
                /            \
           child (bal=1, right heavy)      D
             /         \
            A        g_child (bal=2)
                   /            \
                  gL            gR

           After rotate:  child RIGHT, then node LEFT  (gchild becomes root of subtree)

                g_child (bal=0)
                /              \
           child (bal=0)        node (bal=1, right heavy)
            /      \             /             \
           A        gL          gR              D

        Case3:  g_child = node = 0
                         g_child (bal=0)
                /              \
           child (bal=2, left heavy)    node (bal=0)
            /      \                    /             \
           A        gL                 gR              D
        */

        debug_assert_eq!(child_balance, inv_bal);
        // move gright to left child of node and
        // move gleft to right child of node
        let g_child = child_node.get_child(dir_inverse);
        debug_assert!(!g_child.is_null());
        let g_child_node = get_node_p!(g_child, P, Tag);

        let g_left = g_child_node.get_child(dir);
        let g_right = g_child_node.get_child(dir_inverse);
        let g_old_bal = g_child_node.get_balance();

        let child_new_bal = if g_old_bal == inv_bal { dir_bal } else { 0 };
        let node_new_bal = if g_old_bal == dir_bal { inv_bal } else { 0 };
        //let node_new_bal = 0u8.wrapping_sub((g_old_bal == dir_bal) as u8) & inv_bal;
        //let child_new_bal = 0u8.wrapping_sub((g_old_bal == inv_bal) as u8) & dir_bal;
        node.set_child2::<P::Target>(dir, g_right, data);
        node.set_balance(node_new_bal);
        child_node.set_child2::<P::Target>(dir_inverse, g_left, child);
        child_node.set_balance(child_new_bal);

        /*
         * move child to left child of gchild and
         * move node to right child of gchild and
         * fixup parent of all this to point to gchild
         */
        g_child_node.set_balance(0);
        g_child_node.set_child2_not_null::<P::Target>(dir, child, g_child);
        g_child_node.set_child2_not_null::<P::Target>(dir_inverse, data, g_child);
        if !parent.is_null() {
            get_node_p!(parent, P, Tag)
                .set_child2_not_null::<P::Target>(parent_dir, g_child, parent);
            false
        } else {
            g_child_node.clear_parent();
            self.root = g_child;
            true
        }
    }

    /// # Safety
    ///
    /// It does not drop the node data, only unlinks it.
    /// Caller is responsible for re-taking ownership (e.g. via from_raw) and dropping if needed.
    pub(crate) unsafe fn _remove(
        &mut self, del_node: &mut AvlNode<Tag>, old_parent: *mut u8, mut del_dir: Dir,
    ) {
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

        let mut imm_parent = old_parent;
        let del_left = del_node.left();
        let del_right = del_node.right();
        if del_left.is_null() || del_right.is_null() {
            // one of the child is empty, or all of them empty
            let dir_child = (!del_right.is_null()).into();
            let imm_child = del_node.get_child(dir_child);
            if !imm_parent.is_null() {
                crate::trace_log!(
                    "del {del_node:?} direct with dir {dir_child:?} child {imm_child:p} parent {imm_parent:p}"
                );
                get_node_p!(imm_parent, P, Tag)
                    .set_child2::<P::Target>(del_dir, imm_child, imm_parent);
            } else {
                self.root = imm_child;
                if !imm_child.is_null() {
                    get_node_p!(imm_child, P, Tag).clear_parent();
                }
                crate::trace_log!("del {del_node:?} direct root replace {imm_child:?}");
            }
        } else {
            // node has two child, to the swap
            // balance == 1, choose right, otherwise choose left
            // The child we choose to swap is logical next, it always has a parent and at most 1 child.
            let dir_child: Dir = (del_node.get_balance() == 1).into();
            let dir_child_inverse: Dir = dir_child.reverse();
            let child_temp = del_node.get_child(dir_child);
            let child = Self::bottom_child(
                unsafe { NonNull::new_unchecked(child_temp) },
                dir_child_inverse,
            )
            .as_ptr();
            if !old_parent.is_null() {
                // hookup parent and the swap node
                get_node_p!(old_parent, P, Tag).set_child(del_dir, child);
            } else {
                self.root = child;
            }
            if child != child_temp {
                // del & child is not direct parenthold
                // if we choose right, when the node swap must have no left child

                // keep the parent direction of `child`, after swap it become the parent directonly del_node.
                let child_node = get_node_p!(child, P, Tag);
                let parent_dir_child = child_node.parent_direction::<P::Target>(child);
                imm_parent = child_node.get_parent();
                crate::trace_log!(
                    "del {:?} swap with indirect child dir {:?} {:?} which parent_dir: {:?}",
                    del_node,
                    dir_child,
                    child_node,
                    parent_dir_child
                );
                debug_assert!(child_node.get_child(dir_child_inverse).is_null());

                // change the parent of delete's old child;
                child_node.swap(del_node);
                get_node_p!(del_left, P, Tag).set_parent(child, DIR_LEFT);
                get_node_p!(del_right, P, Tag).set_parent(child, DIR_RIGHT);

                // we can forget old_parent now
                del_dir = parent_dir_child;
                let imm_child = del_node.get_child(dir_child);
                debug_assert!(!imm_parent.is_null());
                get_node_p!(imm_parent, P, Tag)
                    .set_child2::<P::Target>(del_dir, imm_child, imm_parent);
                debug_assert!(del_node.get_child(dir_child_inverse).is_null());
            } else {
                let child_node = get_node_p!(child, P, Tag);
                // the child is already leaf
                // Directly replace del with child, swap del_node's other child to the child at the
                // same direction
                crate::trace_log!(
                    "del {:?} swap with direct child {:?} at {:?}",
                    del_node,
                    child_node,
                    dir_child
                );
                child_node.set_parent(old_parent, del_dir);
                child_node.set_balance(del_node.get_balance());
                let other_child = del_node.get_child(dir_child_inverse);
                debug_assert!(!other_child.is_null());
                child_node.set_child2_not_null::<P::Target>(dir_child_inverse, other_child, child);
                del_dir = dir_child;
                imm_parent = child;
            }
        }
        self.count -= 1;
        del_node.detach();
        if !imm_parent.is_null() {
            self._post_remove(imm_parent, del_dir);
        }
    }

    /// update balance & rotate
    #[inline]
    fn _post_remove(&mut self, mut parent: *mut u8, mut which_child: Dir) {
        debug_assert!(!parent.is_null());
        // Connect parent directly to node (leaving out delete).
        //Since the subtree is now shorter, begin adjusting parent balances
        //and performing any needed rotations.
        loop {
            let node_data = parent;
            // Move up the tree and adjust the balance.
            // Capture the parent and which_child values for the next
            // iteration before any rotations occur.
            let node = get_node_p!(node_data, P, Tag);
            let old_balance = node.get_balance();
            let which_child_inv = which_child.reverse();
            let balance_delta = which_child_inv.to_balance();
            parent = node.get_parent();
            if balance_delta != old_balance {
                if old_balance != 0 {
                    //If the new balance is zero, we don't need to rotate
                    crate::trace_log!("{node:?} update balance dir{which_child:?} 0");
                    node.set_balance(0);
                    if !parent.is_null() {
                        which_child = node.parent_direction::<P::Target>(node_data);
                    } else {
                        break;
                    }
                } else {
                    //If a node was in perfect balance but isn't anymore then
                    //we can stop, since the height didn't change above this point
                    //due to a deletion.
                    crate::trace_log!("{node:?} update balance dir{which_child:?} {balance_delta}");
                    node.set_balance(balance_delta);
                    break;
                }
            } else {
                let parent_dir = node.parent_direction::<P::Target>(node_data);
                crate::trace_log!("_post_remove: node parent {node:?} which {:?}", which_child);
                if self.rotate(node_data, which_child_inv, parent, parent_dir) {
                    //If the rotation doesn't change the height
                    //of the sub-tree we have finished adjusting.
                    break;
                }
                which_child = parent_dir;
            }
            crate::trace_log!("move up {parent:?} for dir{which_child:?}");
        }
        #[cfg(debug_assertions)]
        {
            if self.root.is_null() && self.count > 0 {
                panic!("AvlTree {} nodes left after remove but tree.root == nil", self.count);
            }
        }
    }

    #[inline(always)]
    fn bottom_child(mut data: NonNull<u8>, dir: Dir) -> NonNull<u8> {
        loop {
            unsafe {
                let child = get_node_p!(data.as_ptr(), P, Tag).get_child(dir);
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
    /// NOTE: The iterator yield [AvlNodeRef], so that you can clone the reference if it's `Arc`
    #[inline]
    pub fn iter(&self) -> AvlIter<'_, P, Tag> {
        let first_p = if !self.root.is_null() {
            Some(Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT))
        } else {
            None
        };
        AvlIter::new(self, first_p, DIR_RIGHT)
    }

    /// return a reversed iterator to get the reference.
    ///
    /// NOTE: The iterator yield [AvlNodeRef], so that you can clone the reference if it's `Arc`
    #[inline]
    pub fn iter_rev(&self) -> AvlIter<'_, P, Tag> {
        let last_p = if !self.root.is_null() {
            Some(Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT))
        } else {
            None
        };
        AvlIter::new(self, last_p, DIR_LEFT)
    }

    /// Into reversed order iterator that consume the items
    #[inline]
    pub fn into_iter_rev(self) -> AvlIntoIter<P, Tag> {
        let node = self.root;
        core::mem::forget(self);
        AvlIntoIter::<P, Tag>::new(node, DIR_RIGHT)
    }

    /// Get previous node if there's any
    ///
    /// # Safety
    ///
    /// `data` must already in this AvlTree.
    #[inline]
    pub unsafe fn prev<'a>(&'a self, data: &'a P::Target) -> Option<AvlNodeRef<'a, P>> {
        let p = unsafe { NonNull::new_unchecked(data as *const P::Target as *mut u8) };
        Self::_walk_dir(p, DIR_LEFT).map(|p| AvlNodeRef::new(p.as_ptr()))
    }

    /// Get next node if there's any
    ///
    /// # Safety
    ///
    /// `data` must already in this AvlTree.
    #[inline]
    pub unsafe fn next<'a>(&'a self, data: &'a P::Target) -> Option<AvlNodeRef<'a, P>> {
        let p = unsafe { NonNull::new_unchecked(data as *const P::Target as *mut u8) };
        Self::_walk_dir(p, DIR_RIGHT).map(|p| AvlNodeRef::new(p.as_ptr()))
    }

    fn _walk_dir(data_ptr: NonNull<u8>, dir: Dir) -> Option<NonNull<u8>> {
        let dir_inverse = dir.reverse();
        let node = get_node_p!(data_ptr.as_ptr(), P, Tag);
        let temp = node.get_child(dir);
        if !temp.is_null() {
            unsafe { Some(Self::bottom_child(NonNull::new_unchecked(temp), dir_inverse)) }
        } else {
            let mut parent = node.get_parent();
            let mut pdir = node.parent_direction::<P::Target>(data_ptr.as_ptr());
            while !parent.is_null() {
                if pdir == dir_inverse {
                    return Some(unsafe { NonNull::new_unchecked(parent) });
                }
                // move to upper parent
                let parent_node = get_node_p!(parent, P, Tag);
                pdir = parent_node.parent_direction::<P::Target>(parent);
                parent = parent_node.get_parent();
            }
            // reach root
            debug_assert!(parent.is_null());
            None
        }
    }

    #[inline]
    pub fn first<'a>(&'a self) -> Option<AvlNodeRef<'a, P>> {
        if !self.root.is_null() {
            let p = Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT);
            Some(AvlNodeRef::<'a, P>::new(p.as_ptr()))
        } else {
            None
        }
    }

    #[inline]
    pub fn last<'a>(&'a self) -> Option<AvlNodeRef<'a, P>> {
        if !self.root.is_null() {
            let p = Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT);
            Some(AvlNodeRef::<'a, P>::new(p.as_ptr()))
        } else {
            None
        }
    }

    /// Get the last entry
    ///
    /// You can use [Entry::prepend] or [Entry::prepend_unchecked] on it to batch insert
    #[inline]
    pub fn first_entry<'a>(&'a mut self) -> Entry<'a, P, Tag, First> {
        if !self.root.is_null() {
            let p = Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_LEFT);
            Entry::Occupied(OccupiedEntry { node: p, tree: self })
        } else {
            Entry::Vacant(VacantEntry {
                node: null_mut(),
                tree: self,
                direction: DIR_LEFT,
                key: First(),
            })
        }
    }

    /// Get the last entry
    ///
    /// You can use [Entry::append] or [Entry::append_unchecked] on it to batch insert
    #[inline]
    pub fn last_entry<'a>(&'a mut self) -> Entry<'a, P, Tag, Last> {
        if !self.root.is_null() {
            let p = Self::bottom_child(unsafe { NonNull::new_unchecked(self.root) }, DIR_RIGHT);
            Entry::Occupied(OccupiedEntry { node: p, tree: self })
        } else {
            Entry::Vacant(VacantEntry {
                node: null_mut(),
                tree: self,
                direction: DIR_RIGHT,
                key: Last(),
            })
        }
    }

    pub fn dump<F>(&self, print_cb: F)
    where
        F: Fn(&P::Target, usize),
    {
        let mut to_visit_stack: VecDeque<(*mut u8, usize)> = VecDeque::with_capacity(100);
        if self.root.is_null() {
            return;
        }
        to_visit_stack.push_front((self.root, 0));
        while let Some((data, level)) = to_visit_stack.pop_front() {
            unsafe {
                let node = get_node_p!(data, P, Tag);
                let left = node.left();
                if !left.is_null() {
                    to_visit_stack.push_back((left, level + 1));
                }
                let right = node.right();
                if !right.is_null() {
                    to_visit_stack.push_back((right, level + 1));
                }
                print_cb(&*(data as *const P::Target), level);
            }
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
        use alloc::collections::BTreeMap;
        let mut height_map = BTreeMap::<*mut u8, usize>::new();
        let mut visited_stack: Vec<*mut u8> = Vec::with_capacity(100);
        let mut to_visit_stack: Vec<*mut u8> = Vec::with_capacity(100);
        let mut visit_count = 0;
        if self.root.is_null() {
            assert_eq!(self.count, 0);
            return;
        }
        let mut push_stack =
            |data: *mut u8,
             _to_visit: &mut Vec<*mut u8>,
             _visited: &mut Vec<*mut u8>,
             _height_map: &mut BTreeMap<*mut u8, usize>| {
                unsafe {
                    let node = get_node_p!(data, P, Tag);
                    let left = node.left();
                    let mut has_child = false;
                    if !left.is_null() {
                        has_child = true;
                        assert!(
                            cmp_f(&*(left as *const P::Target), &*(data as *const P::Target))
                                != Ordering::Greater,
                            "node {node:?} left not smaller"
                        );
                        assert_eq!(
                            get_node_p!(left, P, Tag).get_parent(),
                            data,
                            "node {node:?} left parent not match"
                        );
                        _to_visit.push(left);
                    }
                    let right = node.right();
                    if !right.is_null() {
                        has_child = true;
                        assert!(
                            cmp_f(&*(right as *const P::Target), &*(data as *const P::Target))
                                != Ordering::Less,
                            "node {node:?} right not larger"
                        );
                        assert_eq!(
                            get_node_p!(right, P, Tag).get_parent(),
                            data,
                            "node {node:?} right parent not match"
                        );
                        _to_visit.push(right);
                    }
                    if !has_child {
                        // leaf
                        if let Some(_old) = _height_map.insert(data, 1) {
                            panic!("duplicate node {node:?} on level {_old}");
                        }
                        assert_eq!(
                            node.get_balance(),
                            0,
                            "leaf node {node:?} balance is not zero as leaf"
                        );
                    } else {
                        _visited.push(data);
                    }
                }
                visit_count += 1;
            };
        push_stack(self.root, &mut to_visit_stack, &mut visited_stack, &mut height_map);
        while let Some(data) = to_visit_stack.pop() {
            push_stack(data, &mut to_visit_stack, &mut visited_stack, &mut height_map);
        }
        while let Some(data) = visited_stack.pop() {
            let node = get_node_p!(data, P, Tag);
            let left = node.left();
            let mut balance: isize = 0;
            let mut my_height = 0;
            if !left.is_null() {
                let left_height = *height_map.get(&left).unwrap();
                balance = left_height as isize;
                my_height = left_height;
            }
            let right = node.right();
            if !right.is_null() {
                let right_height = *height_map.get(&right).unwrap();
                balance -= right_height as isize;
                if my_height < right_height {
                    my_height = right_height;
                }
            }
            if let Some(_old) = height_map.insert(data, my_height + 1) {
                panic!("duplicate node {node:?} at level {_old}");
            }

            assert!(
                (-1..=1).contains(&balance),
                "non-leaf node {node:?} balance wrong, height_delta={balance}"
            );
            let _balance: u8 = if balance == 1 {
                2
            } else if balance == -1 {
                1
            } else {
                0
            };
            assert_eq!(node.get_balance(), _balance, "non-leaf node {node:?} balance wrong");
        }
        assert_eq!(visit_count, self.count);
    }
}

impl<P, Tag> Drop for AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    fn drop(&mut self) {
        // It's intrusive, use standard into_iter to cleanup the AvlNode by resetting pointers
        let mut iter = AvlIntoIter::<P, Tag>::new(self.root, DIR_LEFT);
        for _node in iter.by_ref() {}
        core::mem::forget(iter);
    }
}

impl<'a, P, Tag> core::iter::IntoIterator for &'a AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    type Item = AvlNodeRef<'a, P>;
    type IntoIter = AvlIter<'a, P, Tag>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P, Tag> core::iter::IntoIterator for AvlTree<P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    type Item = P;
    type IntoIter = AvlIntoIter<P, Tag>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let node = self.root;
        core::mem::forget(self);
        AvlIntoIter::<P, Tag>::new(node, DIR_LEFT)
    }
}

/// A Reference to `P::Target`
pub struct AvlNodeRef<'a, P: Pointer> {
    // Because we might save prev()/next() at the same time,
    // we cannot use MaybeUninit<P> because of miri stack borrow rule.
    // see test int_avl_tree_random.
    node: NonNull<P::Target>,
    _phan: PhantomData<&'a P>,
}

impl<'a, P: Pointer> fmt::Debug for AvlNodeRef<'a, P>
where
    P::Target: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<'a, P: Pointer> AsRef<P::Target> for AvlNodeRef<'a, P> {
    #[inline(always)]
    fn as_ref(&self) -> &P::Target {
        unsafe { self.node.as_ref() }
    }
}

impl<'a, P: Pointer> Deref for AvlNodeRef<'a, P> {
    type Target = P::Target;

    #[inline(always)]
    fn deref(&self) -> &P::Target {
        unsafe { self.node.as_ref() }
    }
}

impl<'a, P: Pointer> AvlNodeRef<'a, P> {
    #[inline]
    fn new(p: *mut u8) -> Self {
        Self {
            node: unsafe { NonNull::new_unchecked(p as *mut P::Target) },
            _phan: Default::default(),
        }
    }
}

impl<'a, P: CloneablePointer> AvlNodeRef<'a, P> {
    /// If P is `Rc`/`Arc`, you can clone the reference out
    #[inline]
    pub fn clone_ref(&self) -> P {
        unsafe { CloneablePointer::from_raw_and_clone(self.node.as_ptr()) }
    }
}
