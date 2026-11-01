#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]

//! An intrusive singly linked list implementation.
//!
//! This module provides `SLinkedList`, a singly linked list optimized for FIFO (First-In, First-Out)
//! queue-like behavior. Elements embed the list nodes themselves, offering memory efficiency
//! and explicit control over allocation.
//!
//! # Features
//! - O(1) push to back and pop from front.
//! - Generic over pointer types (`Box`, `Arc`, `NonNull`, raw pointers).
//!
//! # Example
//!
//! ```rust
//! use embed_slist::{SLinkedList, SListItem, SListNode};
//! use core::cell::UnsafeCell;
//! use std::sync::Arc;
//! use core::ptr::NonNull;
//!
//! struct MyTask {
//!     priority: u8,
//!     description: String,
//!     node: UnsafeCell<SListNode<()>>,
//! }
//!
//! impl MyTask {
//!     fn new(priority: u8, desc: &str) -> Self {
//!         MyTask {
//!             priority,
//!             description: desc.to_string(),
//!             node: UnsafeCell::new(SListNode::default()),
//!         }
//!     }
//! }
//!
//! unsafe impl SListItem<()> for MyTask {
//!     fn get_node(&self) -> &mut SListNode<()> {
//!         unsafe { &mut *self.node.get() }
//!     }
//! }
//!
//! // Using Box<T> (owned pointers)
//! {
//!     let mut task_queue = SLinkedList::<Box<MyTask>, ()>::new();
//!     task_queue.push_back(Box::new(MyTask::new(1, "Handle user login")));
//!     task_queue.push_back(Box::new(MyTask::new(2, "Process analytics data")));
//!     task_queue.push_back(Box::new(MyTask::new(1, "Send welcome email")));
//!     assert_eq!(task_queue.len(), 3);
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Handle user login");
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Process analytics data");
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Send welcome email");
//!     assert!(task_queue.is_empty());
//! }
//!
//! // Using Arc<T> (shared ownership)
//! {
//!     let mut task_queue = SLinkedList::<Arc<MyTask>, ()>::new();
//!     task_queue.push_back(Arc::new(MyTask::new(1, "Handle user login")));
//!     task_queue.push_back(Arc::new(MyTask::new(2, "Process analytics data")));
//!     task_queue.push_back(Arc::new(MyTask::new(1, "Send welcome email")));
//!     assert_eq!(task_queue.len(), 3);
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Handle user login");
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Process analytics data");
//!     assert_eq!(task_queue.pop_front().unwrap().description, "Send welcome email");
//!     assert!(task_queue.is_empty());
//! }
//!
//! // Using NonNull<T> (raw pointers without ownership)
//! {
//!     let mut task_queue = SLinkedList::<NonNull<MyTask>, ()>::new();
//!     let task1 = Box::into_raw(Box::new(MyTask::new(1, "Handle user login")));
//!     let task2 = Box::into_raw(Box::new(MyTask::new(2, "Process analytics data")));
//!     let task3 = Box::into_raw(Box::new(MyTask::new(1, "Send welcome email")));
//!     task_queue.push_back(unsafe{NonNull::new_unchecked(task1)});
//!     task_queue.push_back(unsafe{NonNull::new_unchecked(task2)});
//!     task_queue.push_back(unsafe{NonNull::new_unchecked(task3)});
//!     assert_eq!(task_queue.len(), 3);
//!     assert_eq!(unsafe { &task_queue.pop_front().unwrap().as_ref().description }, "Handle user login");
//!     assert_eq!(unsafe { &task_queue.pop_front().unwrap().as_ref().description }, "Process analytics data");
//!     assert_eq!(unsafe { &task_queue.pop_front().unwrap().as_ref().description }, "Send welcome email");
//!     assert!(task_queue.is_empty());
//!     unsafe{
//!         let _ = Box::from_raw(task1);
//!         let _ = Box::from_raw(task2);
//!         let _ = Box::from_raw(task3);
//!     }
//! }
//! ```
//!
//! # Mixed Types
//!
//! This example show mixed multiple types (which have the same SListNode field) in one list,
//! with custom pointer type.
//!
//! ```
//! use embed_slist::{SLinkedList, SListItem, SListNode};
//! use pointers::Pointer;
//! use core::cell::UnsafeCell;
//! use std::sync::Arc;
//!
//! enum MixedPointer {
//!     Multi(Arc<ArcNode>),
//!     One(Box<BoxNode>),
//! }
//!
//! impl MixedPointer {
//!
//!     fn as_multi(&self) -> &Arc<ArcNode> {
//!         if let Self::Multi(inner) = self {
//!             inner
//!         } else {
//!             panic!("not Multi")
//!         }
//!     }
//!
//!     fn as_one(&self) -> &Box<BoxNode> {
//!         if let Self::One(inner) = self {
//!             inner
//!         } else {
//!             panic!("not One")
//!         }
//!     }
//! }
//!
//! const IS_ARC: usize = 0x1;
//! const TYPE_MASK: usize = IS_ARC;
//!
//! struct ArcNode {
//!     _node: UnsafeCell<SListNode<()>>,
//!     v: usize,
//! }
//!
//! struct BoxNode {
//!     _node: UnsafeCell<SListNode<()>>,
//!     v: String,
//! }
//!
//! impl ArcNode {
//!     fn new(v: usize) -> Arc<Self> {
//!         Arc::new(Self{
//!             _node: Default::default(),
//!             v,
//!         })
//!     }
//! }
//!
//! impl BoxNode {
//!     fn new(v: String) -> Box<Self> {
//!         Box::new(Self{
//!             _node: Default::default(),
//!             v,
//!         })
//!     }
//! }
//!
//! struct MixedAddr (usize);
//!
//! impl Pointer for MixedPointer {
//!     type Target = MixedAddr;
//!
//!     fn as_ref(&self) -> &MixedAddr {
//!         unreachable!("we don't call as_ref in SLinkedList");
//!     }
//!
//!     /// # Safety
//!     ///
//!     /// just a mock
//!     unsafe fn from_raw(p: *const MixedAddr) -> Self {
//!         let real_p = (p as usize) & (!TYPE_MASK);
//!         debug_assert!(real_p != 0);
//!         let type_flag = (p as usize) & TYPE_MASK;
//!         if type_flag == IS_ARC {
//!             Self::Multi(unsafe{Arc::from_raw(real_p as *mut ArcNode)})
//!         } else {
//!             Self::One(unsafe{Box::from_raw(real_p as *mut BoxNode)})
//!         }
//!     }
//!
//!     /// # Safety
//!     /// the address into_raw cannot be defer directly
//!     fn into_raw(self) -> *const MixedAddr {
//!         let addr: usize = match self {
//!             MixedPointer::Multi(item)=>{Arc::into_raw(item) as usize | IS_ARC},
//!             MixedPointer::One(item)=>{Box::into_raw(item) as usize},
//!         };
//!         addr as *const MixedAddr
//!     }
//! }
//!
//! unsafe impl SListItem<()> for MixedAddr {
//!     
//!     fn get_node(&self) -> &mut SListNode<()> {
//!         unreachable!();
//!     }
//!
//!     unsafe fn get_node_from_ptr<'a>(p: *mut u8) -> &'a mut SListNode<()>
//!     where
//!         Self: 'a,
//!     {
//!         let real_p = (p as usize) & (!TYPE_MASK);
//!         debug_assert!(real_p != 0);
//!         let type_flag = (p as usize) & TYPE_MASK;
//!         if type_flag == IS_ARC {
//!             unsafe{&mut *(*(real_p as *const ArcNode))._node.get()}
//!         } else {
//!             unsafe{&mut *(*(real_p as *const BoxNode))._node.get()}
//!         }
//!     }
//! }
//!
//! // list operation
//! let mut l = SLinkedList::<MixedPointer, ()>::new();
//! l.push_back(MixedPointer::Multi(ArcNode::new(1)));
//! l.push_back(MixedPointer::One(BoxNode::new("box1".to_string())));
//! l.push_back(MixedPointer::One(BoxNode::new("box2".to_string())));
//! l.push_back(MixedPointer::Multi(ArcNode::new(2)));
//!
//! let mut iter = l.iter();
//! assert_eq!(iter.next().unwrap().as_multi().v, 1);
//! assert_eq!(iter.next().unwrap().as_one().v.as_str(), "box1");
//! assert_eq!(iter.next().unwrap().as_one().v.as_str(), "box2");
//! assert_eq!(iter.next().unwrap().as_multi().v, 2);
//! assert!(iter.next().is_none());
//!
//! let mut iter = l.drain();
//! assert_eq!(iter.next().unwrap().as_multi().v, 1);
//! assert_eq!(iter.next().unwrap().as_one().v.as_str(), "box1");
//! assert_eq!(iter.next().unwrap().as_one().v.as_str(), "box2");
//! assert_eq!(iter.next().unwrap().as_multi().v, 2);
//! assert!(iter.next().is_none());
//! ```

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

use core::borrow::BorrowMut;
use core::fmt;
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, null_mut};
use pointers::Pointer;

/// A trait to return internal mutable SListNode for specified list.
///
/// The tag is used to distinguish different SListNodes within the same item.
/// For only one ownership, you can use `()`.
///
/// # Safety
/// Implementors must ensure `get_node` returns a valid reference to the `SListNode`
/// embedded within `Self`. Users must use `UnsafeCell` to hold `SListNode` to support
/// interior mutability required by list operations.
pub unsafe trait SListItem<Tag>: Sized {
    fn get_node(&self) -> &mut SListNode<Tag>;

    /// # Safety
    ///
    /// This is just map from raw pointer to `&mut SListNode`.
    ///
    /// You only have to implement this when using custom pointer type with abnormal address.
    /// Refer to [Mixed Type Example](index.html#mixed-types)
    #[allow(unsafe_op_in_unsafe_fn)]
    #[inline(always)]
    unsafe fn get_node_from_ptr<'a>(p: *mut u8) -> &'a mut SListNode<Tag>
    where
        Self: 'a,
    {
        debug_assert!(!p.is_null());
        (*(p as *const Self)).get_node()
    }
}

/// The node structure that must be embedded in items to be stored in a `SLinkedList`.
///
#[repr(C)]
pub struct SListNode<Tag> {
    next: *mut u8,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<Tag> Send for SListNode<Tag> {}

impl<Tag> Default for SListNode<Tag> {
    #[inline(always)]
    fn default() -> Self {
        Self { next: null_mut(), _phan: Default::default() }
    }
}

impl<Tag> fmt::Debug for SListNode<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        if !self.next.is_null() {
            write!(f, "next: {:p} ", self.next)?;
        } else {
            write!(f, "next: none ")?;
        }
        write!(f, ")")
    }
}

/// A singly linked list with head and tail pointers (FIFO queue).
///
/// Supports O(1) push to back and pop from front.
#[repr(C)]
pub struct SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    length: usize,
    head: *mut u8,
    tail: *mut u8,
    _phan: PhantomData<fn(&P, &Tag)>,
}

unsafe impl<P, Tag> Send for SLinkedList<P, Tag>
where
    P: Pointer + Send,
    P::Target: SListItem<Tag>,
{
}

unsafe impl<P, Tag> Sync for SLinkedList<P, Tag>
where
    P: Pointer + Send,
    P::Target: SListItem<Tag>,
{
}

impl<P: fmt::Debug, Tag> fmt::Debug for SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{ length: {} ", self.length)?;
        if !self.head.is_null() {
            write!(f, "head: {:?} ", self.head)?;
        } else {
            write!(f, "head: none ")?;
        }
        if !self.tail.is_null() {
            write!(f, "tail: {:?} ", self.tail)?;
        } else {
            write!(f, "tail: none ")?;
        }
        write!(f, "}}")
    }
}

impl<P, Tag> SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    /// Creates a new, empty singly linked list.
    #[inline(always)]
    pub fn new() -> Self {
        SLinkedList { length: 0, head: null_mut(), tail: null_mut(), _phan: Default::default() }
    }

    /// Clears the list, dropping all of its elements if the pointer type `P` owns them.
    #[inline]
    pub fn clear(&mut self) {
        // By repeatedly popping from the front, we drop each element.
        // If P is an owned pointer (like Box), the element is dropped.
        // If P is a raw pointer, it's a no-op, but the list is still emptied.
        while self.pop_front().is_some() {}
    }

    /// Returns the length of the list as `usize`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the list contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Appends an element to the back of the list (FIFO: enqueue).
    #[inline]
    pub fn push_back(&mut self, item: P) {
        let ptr = item.into_raw() as *mut u8;
        unsafe {
            let node = <P::Target as SListItem<Tag>>::get_node_from_ptr(ptr);
            node.next = null_mut();
            if !self.tail.is_null() {
                // List is not empty, update current tail's next
                <P::Target as SListItem<Tag>>::get_node_from_ptr(self.tail).next = ptr;
            } else {
                // List is empty
                self.head = ptr;
            }
        }
        self.tail = ptr;
        self.length += 1;
    }

    /// Pushes an element to the front of the list.
    #[inline]
    pub fn push_front(&mut self, item: P) {
        let ptr = item.into_raw() as *mut u8;
        let node = unsafe { <P::Target as SListItem<Tag>>::get_node_from_ptr(ptr) };
        node.next = self.head;
        if !self.head.is_null() {
        } else {
            // List was empty
            self.tail = ptr;
        }
        self.head = ptr;
        self.length += 1;
    }

    /// Removes the first element and returns it (FIFO: dequeue).
    pub fn pop_front(&mut self) -> Option<P> {
        if !self.head.is_null() {
            let head_ptr = self.head;
            let node = unsafe { <P::Target as SListItem<Tag>>::get_node_from_ptr(head_ptr) };
            let next_ptr = node.next;
            node.next = null_mut();
            // Update head to next
            self.head = next_ptr;
            self.length -= 1;
            // If head became null (list empty), update tail to null too
            if !self.head.is_null() {
            } else {
                self.tail = null_mut();
            }
            Some(unsafe { P::from_raw(head_ptr as *const P::Target) })
        } else {
            None
        }
    }

    #[inline]
    pub fn get_front_ptr(&self) -> *const P::Target {
        self.head as *const P::Target
    }

    #[inline]
    pub fn get_back_ptr(&self) -> *const P::Target {
        self.tail as *const P::Target
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn get_front(&self) -> Option<&P::Target> {
        if !self.head.is_null() {
            unsafe { Some(&(*(self.head as *const P::Target))) }
        } else {
            None
        }
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn get_back(&self) -> Option<&P::Target> {
        if !self.tail.is_null() {
            unsafe { Some(&(*(self.tail as *const P::Target))) }
        } else {
            None
        }
    }

    /// Checks if the given node is the head of the list.
    #[inline(always)]
    pub fn is_front(&self, node: &P::Target) -> bool {
        if !self.head.is_null() {
            ptr::eq(self.head, node as *const P::Target as *const u8)
        } else {
            false
        }
    }

    /// Returns an iterator over the list (borrowed).
    ///
    /// # NOTE
    ///
    /// If you plan on turn the raw pointer to owned, use drain instead
    ///
    /// # Safety
    ///
    /// The caller must ensure that the list is not modified in a way that can
    /// invalidate internal pointers (such as removing elements or dropping
    /// items) for the duration of the iterator's use.
    #[inline(always)]
    pub fn iter<'a>(&'a self) -> SLinkedListIter<'a, P, Tag> {
        SLinkedListIter {
            len: self.length,
            next_p: self.head,
            cur: MaybeUninit::uninit(),
            _phan: Default::default(),
        }
    }

    /// Returns a draining iterator that removes items from the list.
    #[inline(always)]
    pub fn drain<'a>(&'a mut self) -> SLinkedListDrainer<'a, P, Tag> {
        SLinkedListDrainer { list: self, _phan: Default::default() }
    }
}

impl<P, Tag> Drop for SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    fn drop(&mut self) {
        if mem::needs_drop::<P>() {
            self.drain().for_each(drop);
        }
    }
}

pub struct SLinkedListIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    next_p: *mut u8,
    cur: MaybeUninit<P>,
    len: usize,
    _phan: PhantomData<&'a SLinkedList<P, Tag>>,
}

unsafe impl<'a, P, Tag> Send for SLinkedListIter<'a, P, Tag>
where
    P: Pointer + Send,
    P::Target: SListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for SLinkedListIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    type Item = &'a P;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if !self.next_p.is_null() {
            let cur = self.next_p;
            unsafe {
                self.next_p = <P::Target as SListItem<Tag>>::get_node_from_ptr(cur).next;
                self.cur.write(P::from_raw(cur as *const P::Target));
                // use transmute to convert lifetime from '_ to 'a
                return Some(mem::transmute::<&P, &P>(self.cur.assume_init_ref()));
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, P, Tag> ExactSizeIterator for SLinkedListIter<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
}

pub type SLinkedListDrainer<'a, P, Tag> = Drainer<&'a mut SLinkedList<P, Tag>, P, Tag>;
pub type SLinkedListIntoIter<P, Tag> = Drainer<SLinkedList<P, Tag>, P, Tag>;

pub struct Drainer<L, P, Tag>
where
    L: BorrowMut<SLinkedList<P, Tag>>,
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    list: L,
    _phan: PhantomData<(P, Tag)>,
}

unsafe impl<L, P, Tag> Send for Drainer<L, P, Tag>
where
    L: BorrowMut<SLinkedList<P, Tag>>,
    P: Pointer + Send,
    P::Target: SListItem<Tag>,
{
}

impl<L, P, Tag> Iterator for Drainer<L, P, Tag>
where
    L: BorrowMut<SLinkedList<P, Tag>>,
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    type Item = P;

    #[inline]
    fn next(&mut self) -> Option<P> {
        self.list.borrow_mut().pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = self.list.borrow().len();
        (l, Some(l))
    }
}

impl<L, P, Tag> ExactSizeIterator for Drainer<L, P, Tag>
where
    L: BorrowMut<SLinkedList<P, Tag>>,
    P: Pointer,
    P::Target: SListItem<Tag>,
{
}

impl<'a, P, Tag> IntoIterator for &'a SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    type Item = &'a P;
    type IntoIter = SLinkedListIter<'a, P, Tag>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P, Tag> IntoIterator for SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    type Item = P;
    type IntoIter = SLinkedListIntoIter<P, Tag>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Drainer { list: self, _phan: Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;
    use std::cell::UnsafeCell;
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct TestTag;

    #[derive(Debug)]
    pub struct TestNode {
        pub value: i64,
        pub node: UnsafeCell<SListNode<TestTag>>,
    }

    static ACTIVE_NODE_COUNT: AtomicUsize = AtomicUsize::new(0);

    impl Drop for TestNode {
        fn drop(&mut self) {
            ACTIVE_NODE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    unsafe impl Send for TestNode {}

    unsafe impl SListItem<TestTag> for TestNode {
        fn get_node(&self) -> &mut SListNode<TestTag> {
            unsafe { &mut *self.node.get() }
        }
    }

    fn new_node(v: i64) -> TestNode {
        ACTIVE_NODE_COUNT.fetch_add(1, Ordering::SeqCst);
        TestNode { value: v, node: UnsafeCell::new(SListNode::default()) }
    }

    #[test]
    fn test_push_back_pop_front_box() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedList::<Box<TestNode>, TestTag>::new();

        let node1 = Box::new(new_node(1));
        l.push_back(node1);

        let node2 = Box::new(new_node(2));
        l.push_back(node2);

        let node3 = Box::new(new_node(3));
        l.push_back(node3);

        assert_eq!(3, l.len());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);

        // Test iterator
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        // Test pop_front (FIFO)
        let n1 = l.pop_front();
        assert!(n1.is_some());
        assert_eq!(n1.unwrap().value, 1);
        assert_eq!(l.len(), 2);

        let n2 = l.pop_front();
        assert!(n2.is_some());
        assert_eq!(n2.unwrap().value, 2);
        assert_eq!(l.len(), 1);

        let n3 = l.pop_front();
        assert!(n3.is_some());
        assert_eq!(n3.unwrap().value, 3);
        assert_eq!(l.len(), 0);

        assert!(l.pop_front().is_none());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_push_front_box() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedList::<Box<TestNode>, TestTag>::new();

        let node1 = Box::new(new_node(1));
        l.push_front(node1); // List: [1]

        let node2 = Box::new(new_node(2));
        l.push_front(node2); // List: [2, 1]

        let node3 = Box::new(new_node(3));
        l.push_front(node3); // List: [3, 2, 1]

        assert_eq!(3, l.len());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);

        // Test iterator (should be 3, 2, 1)
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 3);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 1);
        assert!(iter.next().is_none());

        // Test pop_front (FIFO)
        let n1 = l.pop_front();
        assert!(n1.is_some());
        assert_eq!(n1.unwrap().value, 3);
        assert_eq!(l.len(), 2);

        let n2 = l.pop_front();
        assert!(n2.is_some());
        assert_eq!(n2.unwrap().value, 2);
        assert_eq!(l.len(), 1);

        let n3 = l.pop_front();
        assert!(n3.is_some());
        assert_eq!(n3.unwrap().value, 1);
        assert_eq!(l.len(), 0);

        assert!(l.pop_front().is_none());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_drain() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedList::<Box<TestNode>, TestTag>::new();

        l.push_back(Box::new(new_node(10)));
        l.push_back(Box::new(new_node(20)));
        l.push_back(Box::new(new_node(30)));

        assert_eq!(l.len(), 3);
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 10);
            assert_eq!(drain.next().unwrap().value, 20);
            assert_eq!(drain.next().unwrap().value, 30);
            assert!(drain.next().is_none());
        }

        assert_eq!(l.len(), 0);
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_clear() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedList::<Box<TestNode>, TestTag>::new();

        l.push_back(Box::new(new_node(1)));
        l.push_back(Box::new(new_node(2)));
        assert_eq!(l.len(), 2);
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);

        l.clear();

        assert!(l.is_empty());
        assert_eq!(l.len(), 0);
        assert!(l.get_front().is_none());
        assert!(l.get_back().is_none());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);

        // Can still push to the list
        l.push_back(Box::new(new_node(3)));
        assert_eq!(l.len(), 1);
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 1);
    }
}
