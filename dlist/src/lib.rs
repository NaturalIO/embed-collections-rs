#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]

//! An intrusive doubly linked list implementation.
//!
//! This module provides `DLinkedList`, a doubly linked list where elements
//! embed the list nodes themselves. This design offers memory efficiency
//! and explicit control over allocation, suitable for scenarios like
//! building LRU caches directly within data structures.
//!
//! # Features
//! - O(1) push and pop from both front and back.
//! - Generic over pointer types (`Box`, `Arc`, `NonNull`, raw pointers).
//! - Supports multiple lists for the same item via `Tag`.
//!
//! # Example
//!
//! ```rust
//! use embed_dlist::{DLinkedList, DListItem, DListNode};
//! use core::cell::UnsafeCell;
//! use std::sync::Arc;
//! use core::ptr::NonNull;
//!
//! struct MyTag ();
//!
//! struct MyItem {
//!     id: u32,
//!     data: String,
//!     node: UnsafeCell<DListNode<MyTag>>,
//! }
//!
//! impl MyItem {
//!     fn new(id: u32, data: &str) -> Self {
//!         MyItem {
//!             id,
//!             data: data.to_string(),
//!             node: UnsafeCell::new(DListNode::default()),
//!         }
//!     }
//! }
//!
//! unsafe impl DListItem<MyTag> for MyItem {
//!     fn get_node(&self) -> &mut DListNode<MyTag> {
//!         unsafe { &mut *self.node.get() }
//!     }
//! }
//!
//! // Using Box<T> (owned pointers)
//! {
//!     let mut list = DLinkedList::<Box<MyItem>, MyTag>::new();
//!     list.push_back(Box::new(MyItem::new(1, "First")));
//!     list.push_front(Box::new(MyItem::new(2, "Second")));
//!     list.push_back(Box::new(MyItem::new(3, "Third")));
//!     assert_eq!(list.len(), 3);
//!     assert_eq!(list.pop_front().unwrap().id, 2);
//!     assert_eq!(list.pop_back().unwrap().id, 3);
//!     assert_eq!(list.pop_front().unwrap().id, 1);
//!     assert!(list.is_empty());
//! }
//!
//! // Using Arc<T> (shared ownership)
//! {
//!     let mut list = DLinkedList::<Arc<MyItem>, MyTag>::new();
//!     list.push_back(Arc::new(MyItem::new(1, "First")));
//!     list.push_front(Arc::new(MyItem::new(2, "Second")));
//!     list.push_back(Arc::new(MyItem::new(3, "Third")));
//!     assert_eq!(list.len(), 3);
//!     assert_eq!(list.pop_front().unwrap().id, 2);
//!     assert_eq!(list.pop_back().unwrap().id, 3);
//!     assert_eq!(list.pop_front().unwrap().id, 1);
//!     assert!(list.is_empty());
//! }
//!
//! // Using NonNull<T> (ignore ownership)
//! {
//!     let mut list = DLinkedList::<NonNull<MyItem>, MyTag>::new();
//!     let item1 = Box::into_raw(Box::new(MyItem::new(1, "First")));
//!     let item2 = Box::into_raw(Box::new(MyItem::new(2, "Second")));
//!     let item3 = Box::into_raw(Box::new(MyItem::new(3, "Third")));
//!     list.push_back(unsafe{NonNull::new_unchecked(item1)});
//!     list.push_front(unsafe{NonNull::new_unchecked(item2)});
//!     list.push_back(unsafe{NonNull::new_unchecked(item3)});
//!     assert_eq!(list.len(), 3);
//!     assert_eq!(unsafe { list.pop_front().unwrap().as_ref().id }, 2);
//!     assert_eq!(unsafe { list.pop_back().unwrap().as_ref().id }, 3);
//!     assert_eq!(unsafe { list.pop_front().unwrap().as_ref().id }, 1);
//!     assert!(list.is_empty());
//!     unsafe{
//!         let _ = Box::from_raw(item1);
//!         let _ = Box::from_raw(item2);
//!         let _ = Box::from_raw(item3);
//!     }
//! }
//! ```

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

use core::marker::PhantomData;
use core::{
    fmt,
    mem::{self, MaybeUninit},
    ptr::{self, null_mut},
};
use pointers::Pointer;

/// A trait to return internal mutable DListNode for specified list.
///
/// The tag is used to distinguish different DListNodes within the same item,
/// allowing an item to belong to multiple lists simultaneously.
/// For only one ownership, you can use `()`.
///
/// # Safety
///
/// Implementors must ensure `get_node` returns a valid reference to the `DListNode`
/// embedded within `Self`. Users must use `UnsafeCell` to hold `DListNode` to support
/// interior mutability required by list operations.
pub unsafe trait DListItem<Tag>: Sized {
    fn get_node(&self) -> &mut DListNode<Tag>;

    #[allow(unsafe_op_in_unsafe_fn)]
    #[inline(always)]
    unsafe fn get_node_from_ptr<'a>(p: *mut u8) -> &'a mut DListNode<Tag>
    where
        Self: 'a,
    {
        debug_assert!(!p.is_null());
        (*(p as *const Self)).get_node()
    }
}

/// The node structure that must be embedded in items to be stored in a `DLinkedList`.
#[repr(C)]
pub struct DListNode<Tag> {
    prev: *mut u8,
    next: *mut u8,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<Tag> Send for DListNode<Tag> {}

impl<Tag> Default for DListNode<Tag> {
    #[inline(always)]
    fn default() -> Self {
        Self { prev: null_mut(), next: null_mut(), _phan: Default::default() }
    }
}

impl<Tag> fmt::Debug for DListNode<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        if !self.prev.is_null() {
            write!(f, "prev: {:p} ", self.prev)?;
        } else {
            write!(f, "prev: none ")?;
        }
        if !self.next.is_null() {
            write!(f, "next: {:p} ", self.next)?;
        } else {
            write!(f, "next: none ")?;
        }
        write!(f, ")")
    }
}

/// An intrusive doubly linked list.
///
/// Supports O(1) insertion and removal at both ends.
#[repr(C)]
pub struct DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    length: usize,
    head: *mut u8,
    tail: *mut u8,
    _phan: PhantomData<fn(&P, &Tag)>,
}

unsafe impl<P, Tag> Send for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
}

impl<P: fmt::Debug, Tag> fmt::Debug for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
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

impl<P, Tag> DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    /// Creates a new, empty doubly linked list.
    #[inline(always)]
    pub fn new() -> Self {
        DLinkedList { length: 0, head: null_mut(), tail: null_mut(), _phan: Default::default() }
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

    #[inline(always)]
    fn _remove_node(&mut self, item: *mut u8) -> bool {
        let mut removed = false;
        unsafe {
            let node = <P::Target as DListItem<Tag>>::get_node_from_ptr(item);
            if !node.prev.is_null() {
                <P::Target as DListItem<Tag>>::get_node_from_ptr(node.prev).next = node.next;
                removed = true;
            } else if self.head == item {
                self.head = node.next;
                removed = true;
            }
            if !node.next.is_null() {
                <P::Target as DListItem<Tag>>::get_node_from_ptr(node.next).prev = node.prev;
                removed = true;
            } else if self.tail == item {
                self.tail = node.prev;
                removed = true;
            }
            if removed {
                node.next = null_mut();
                node.prev = null_mut();
                self.length -= 1;
            }
        }
        removed
    }

    /// Remove a node by raw pointer from the middle of the list, and recover P from `item`
    ///
    /// - Return Some if the item is in the list.
    /// - Return None if the item is not in any list.
    ///
    /// NOTE： Due to avoid miri stack borrow rule error, `item` is a raw pointer.
    ///
    /// # Safety
    ///
    /// `item` should point the a valid item. Do not remove item from other list, otherwise will lead to UB.
    ///
    /// # Example
    ///
    /// ```
    ///
    /// use embed_dlist::{DLinkedList, DListItem, DListNode};
    /// use core::cell::UnsafeCell;
    /// extern crate alloc;
    /// use alloc::boxed::Box;
    ///
    /// #[derive(Debug)]
    /// pub struct TestNode {
    ///     pub value: i64,
    ///     pub node: UnsafeCell<DListNode<()>>,
    /// }
    ///
    /// unsafe impl Send for TestNode {}
    ///
    /// unsafe impl DListItem<()> for TestNode {
    ///     fn get_node(&self) -> &mut DListNode<()> {
    ///         unsafe { &mut *self.node.get() }
    ///     }
    /// }
    ///
    /// fn new_node(v: i64) -> TestNode {
    ///     TestNode { value: v, node: UnsafeCell::new(DListNode::default()) }
    /// }
    ///
    /// let mut l = DLinkedList::<Box<TestNode>, ()>::new();
    ///
    /// let node1 = Box::new(new_node(1));
    /// l.push_back(node1);
    /// let node2 = Box::new(new_node(2));
    ///
    /// // NOTE: use `node_p = node2.as_ptr()`  will trigger miri stack borrow rule.
    /// // we use into_raw and then from_raw
    /// let node2_p = Box::into_raw(node2);
    /// l.push_back(unsafe{Box::from_raw(node2_p)});
    ///
    /// let node3 = Box::new(new_node(3));
    /// l.push_back(node3);
    /// assert_eq!(l.len(), 3);
    ///
    /// let node2 = unsafe { l.remove_node(node2_p).unwrap() };
    /// assert_eq!(l.len(), 2);
    /// assert_eq!(node2.value, 2);
    /// ```
    #[inline(always)]
    pub unsafe fn remove_node(&mut self, item: *const P::Target) -> Option<P> {
        unsafe { if self._remove_node(item as *mut u8) { Some(P::from_raw(item)) } else { None } }
    }

    /// Moves a node to the front of the list (e.g., for LRU updates).
    ///
    /// NOTE： Due to avoid miri stack borrow rule error, `item` is a raw pointer.
    ///
    /// # Safety
    ///
    /// The item must be in the list, otherwise will lead to UB.
    #[inline(always)]
    pub unsafe fn peak(&mut self, item: *const P::Target) {
        assert!(!self.head.is_null());
        if !ptr::eq(self.head, item as *mut u8) {
            assert!(self._remove_node(item as *mut u8), "item is not in the list");
            self.push_front_ptr(item);
        }
    }

    /// Pushes an element to the front of the list.
    #[inline]
    pub fn push_front(&mut self, item: P) {
        let ptr = item.into_raw();
        self.push_front_ptr(ptr);
    }

    #[inline]
    fn push_front_ptr(&mut self, ptr: *const P::Target) {
        let node = unsafe { <P::Target as DListItem<Tag>>::get_node_from_ptr(ptr as *mut u8) };
        let head = self.head;
        node.next = head;
        node.prev = null_mut();

        if head.is_null() {
            self.tail = ptr as *mut u8;
        } else {
            unsafe {
                <P::Target as DListItem<Tag>>::get_node_from_ptr(head).prev = ptr as *mut u8;
            }
        }
        self.head = ptr as *mut u8;
        self.length += 1;
    }

    /// Pushes an element to the back of the list.
    #[inline]
    pub fn push_back(&mut self, item: P) {
        let tail = self.tail;
        let ptr = item.into_raw() as *mut u8;
        unsafe {
            let node = <P::Target as DListItem<Tag>>::get_node_from_ptr(ptr);
            node.prev = tail;
            node.next = null_mut();
            if tail.is_null() {
                self.head = ptr;
            } else {
                <P::Target as DListItem<Tag>>::get_node_from_ptr(tail).next = ptr;
            }
        }
        self.tail = ptr;
        self.length += 1;
    }

    /// Removes and returns the element at the front of the list.
    pub fn pop_front(&mut self) -> Option<P> {
        if !self.head.is_null() {
            let head_ptr = self.head;
            unsafe {
                self._remove_node(head_ptr);
                Some(P::from_raw(head_ptr as *const P::Target))
            }
        } else {
            None
        }
    }

    /// Removes and returns the element at the back of the list.
    #[inline]
    pub fn pop_back(&mut self) -> Option<P> {
        if !self.tail.is_null() {
            let tail_ptr = self.tail;
            unsafe {
                self._remove_node(tail_ptr);
                Some(P::from_raw(tail_ptr as *const P::Target))
            }
        } else {
            None
        }
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn get_front(&self) -> Option<&P::Target> {
        unsafe {
            if !self.head.is_null() { Some(&(*(self.head as *const P::Target))) } else { None }
        }
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn get_back(&self) -> Option<&P::Target> {
        unsafe {
            if !self.tail.is_null() { Some(&(*(self.tail as *const P::Target))) } else { None }
        }
    }

    /// Checks if the given node is the head of the list.
    #[inline(always)]
    pub fn is_front(&self, node: &P::Target) -> bool {
        if self.head.is_null() {
            false
        } else {
            // This comparison is tricky because self.head is *mut HrcWrapper<T>
            // and node is &mut DListNode<T>.
            // We need to compare the node address or the wrapper address.
            // Converting head -> node and comparing addresses of DListNode is safer.
            ptr::eq(self.head, node as *const P::Target as *mut u8)
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
    pub fn iter<'a>(&'a self) -> DLinkedListIterator<'a, P, Tag> {
        DLinkedListIterator {
            next_p: self.head,
            _phan: Default::default(),
            cur: MaybeUninit::uninit(),
        }
    }

    /// Returns a draining iterator that removes items from the list.
    /// Crucial for cleaning up lists containing owned pointers (like `Box`).
    ///
    /// # Note
    ///
    /// The iterator removes elements from the **front** of the list (FIFO order),
    #[inline(always)]
    pub fn drain<'a>(&'a mut self) -> DLinkedListDrainer<'a, P, Tag> {
        DLinkedListDrainer { list: self }
    }
}

impl<P, Tag> Drop for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    fn drop(&mut self) {
        // Calling drain will remove all elements from the list and drop them.
        // The DLinkedListDrainer iterator returns P, which will be dropped
        // when the iterator is consumed.
        if mem::needs_drop::<P>() {
            self.drain().for_each(drop);
        }
    }
}

pub struct DLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    next_p: *mut u8,
    cur: MaybeUninit<P>,
    _phan: PhantomData<&'a DLinkedList<P, Tag>>,
}

unsafe impl<'a, P, Tag> Send for DLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for DLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
    Self: 'a,
{
    type Item = &'a P;

    #[inline]
    fn next(&mut self) -> Option<&'a P> {
        if !self.next_p.is_null() {
            let cur = self.next_p;
            unsafe {
                self.next_p = <P::Target as DListItem<Tag>>::get_node_from_ptr(cur).next;
                self.cur.write(P::from_raw(cur as *const P::Target));
                // use transmute to convert lifetime from '_ to 'a
                return Some(mem::transmute::<&P, &P>(self.cur.assume_init_ref()));
            }
        }
        None
    }
}

pub struct DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    list: &'a mut DLinkedList<P, Tag>,
}

unsafe impl<'a, P, Tag> Send for DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: DListItem<Tag>,
{
    type Item = P;

    #[inline]
    fn next(&mut self) -> Option<P> {
        self.list.pop_front()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::boxed::Box;
    use std::cell::UnsafeCell;
    use std::println;
    use std::ptr::NonNull;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct TestTag;

    #[derive(Debug)]
    pub struct TestNode {
        pub value: i64,
        pub node: UnsafeCell<DListNode<TestTag>>,
    }

    static ACTIVE_NODE_COUNT: AtomicUsize = AtomicUsize::new(0);

    impl Drop for TestNode {
        fn drop(&mut self) {
            ACTIVE_NODE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    unsafe impl Send for TestNode {}

    unsafe impl DListItem<TestTag> for TestNode {
        fn get_node(&self) -> &mut DListNode<TestTag> {
            unsafe { &mut *self.node.get() }
        }
    }

    fn new_node(v: i64) -> TestNode {
        ACTIVE_NODE_COUNT.fetch_add(1, Ordering::SeqCst);
        TestNode { value: v, node: UnsafeCell::new(DListNode::default()) }
    }

    #[test]
    fn test_push_back_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

        let node1 = Box::new(new_node(1));
        l.push_back(node1);

        let node2 = Box::new(new_node(2));
        l.push_back(node2);

        let node3 = Box::new(new_node(3));
        l.push_back(node3);

        assert_eq!(3, l.len());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_push_back_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let node1 = Arc::new(new_node(1));
        l.push_back(node1);

        let node2 = Arc::new(new_node(2));
        l.push_back(node2);

        let node3 = Arc::new(new_node(3));
        l.push_back(node3);

        assert_eq!(3, l.len());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_push_front_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

        let node3 = Box::new(new_node(3));
        l.push_front(node3);

        let node2 = Box::new(new_node(2));
        l.push_front(node2);

        let node1 = Box::new(new_node(1));
        l.push_front(node1);

        assert_eq!(3, l.len());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_push_front_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let node3 = Arc::new(new_node(3));
        l.push_front(node3);

        let node2 = Arc::new(new_node(2));
        l.push_front(node2);

        let node1 = Arc::new(new_node(1));
        l.push_front(node1);

        assert_eq!(3, l.len());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_pop_back_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

        let node1 = Box::new(new_node(1));
        l.push_back(node1);

        let node2 = Box::new(new_node(2));
        l.push_back(node2);

        let node3 = Box::new(new_node(3));
        l.push_back(node3);

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        let del_node = l.pop_back();
        assert_eq!(2, l.len());
        assert!(del_node.is_some());
        assert_eq!(del_node.unwrap().value, 3);

        let mut iter_remaining = l.iter();
        assert_eq!(iter_remaining.next().unwrap().value, 1);
        assert_eq!(iter_remaining.next().unwrap().value, 2);
        assert!(iter_remaining.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_pop_back_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let node1 = Arc::new(new_node(1));
        l.push_back(node1);

        let node2 = Arc::new(new_node(2));
        l.push_back(node2);

        let node3 = Arc::new(new_node(3));
        l.push_back(node3);

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        let del_node = l.pop_back();
        assert_eq!(2, l.len());
        assert!(del_node.is_some());
        // Note: The value returned by Arc::from_raw must still be used.
        assert!(del_node.is_some());

        // Check the order of remaining elements
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_pop_front_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let node1 = Arc::new(new_node(1));
        l.push_front(node1);

        let node2 = Arc::new(new_node(2));
        l.push_front(node2);

        let node3 = Arc::new(new_node(3));
        l.push_front(node3);

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 3);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 1);
        assert!(iter.next().is_none());

        let del_node = l.pop_front();
        assert_eq!(2, l.len());
        assert!(del_node.is_some());
        // Note: The value returned by Arc::from_raw must still be used.
        assert!(del_node.is_some());

        // Check the order of remaining elements
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 1);
        assert!(iter.next().is_none());

        {
            assert_eq!(l.pop_front().unwrap().value, 2);
            assert_eq!(l.pop_front().unwrap().value, 1);
            assert!(l.pop_front().is_none());
            assert!(l.pop_back().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_iter_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

        let mut count = 0;
        for _item in l.iter() {
            count += 1;
        }
        assert_eq!(count, 0);

        let node1 = Box::new(new_node(1));
        l.push_back(node1);

        let node2 = Box::new(new_node(2));
        l.push_back(node2);

        let node3 = Box::new(new_node(3));
        l.push_back(node3);

        count = 0;
        for item in l.iter() {
            count += 1;
            println!("{}", item.value);
        }
        assert_eq!(count, 3);

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_iter_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let mut count = 0;
        for _item in l.iter() {
            count += 1;
        }
        assert_eq!(count, 0);

        let node1 = Arc::new(new_node(1));
        l.push_back(node1);

        let node2 = Arc::new(new_node(2));
        l.push_back(node2);

        let node3 = Arc::new(new_node(3));
        l.push_back(node3);

        // Check order
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 3);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn test_single_element_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();
        let node1 = Box::new(new_node(1));
        l.push_front(node1);
        let del_node = l.pop_back();
        assert!(del_node.is_some());
        assert_eq!(del_node.unwrap().value, 1);
        assert_eq!(0, l.len());
        assert!(l.pop_back().is_none());

        let mut l2 = DLinkedList::<Box<TestNode>, TestTag>::new();
        let node2 = Box::new(new_node(2));
        l2.push_back(node2);
        let del_node2 = l2.pop_back();
        assert!(del_node2.is_some());
        assert_eq!(del_node2.unwrap().value, 2);
        assert_eq!(0, l2.len());
        assert!(l2.pop_back().is_none());

        {
            let mut drain = l.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);

        {
            let mut drain = l2.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l2.len(), 0);
    }

    #[test]
    fn test_single_element_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();
        let node1 = Arc::new(new_node(1));
        l.push_front(node1);
        let del_node = l.pop_back();
        assert!(del_node.is_some());
        assert_eq!(0, l.len());
        assert!(l.pop_back().is_none());

        let mut l2 = DLinkedList::<Arc<TestNode>, TestTag>::new();
        let node2 = Arc::new(new_node(2));
        l2.push_back(node2);
        let del_node2 = l2.pop_back();
        assert!(del_node2.is_some());
        assert_eq!(0, l2.len());
        assert!(l2.pop_back().is_none());

        {
            let mut drain = l.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);

        {
            let mut drain = l2.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l2.len(), 0);
    }

    #[test]
    fn test_drop_box_implementation() {
        // Reset the counter before the test
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);

        {
            let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

            let node1 = Box::new(new_node(1));
            l.push_back(node1);

            let node2 = Box::new(new_node(2));
            l.push_back(node2);

            let node3 = Box::new(new_node(3));
            l.push_back(node3);

            assert_eq!(l.len(), 3);
            assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);
        } // `l` goes out of scope here, triggering DLinkedList's Drop, which drains and drops nodes.

        // All nodes should have been dropped
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_raw_pointer_list() {
        // Reset the counter before the test
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);

        // Manually create nodes as raw pointers
        let node1 = Box::into_raw(Box::new(new_node(10)));
        let node2 = Box::into_raw(Box::new(new_node(20)));

        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);

        unsafe {
            let mut l = DLinkedList::<*const TestNode, TestTag>::new();
            l.push_back(node1);
            l.push_back(node2);

            let mut iter = l.iter();
            let item = iter.next().unwrap();
            assert_eq!((**item).value, 10);
            let item = iter.next().unwrap();
            assert_eq!((**item).value, 20);
            assert!(iter.next().is_none());
        } // l dropped here. Because P is *const TestNode, needs_drop is false, so drain is NOT called.

        // Nodes should still exist
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);

        unsafe {
            // Check values
            assert_eq!((*node1).value, 10);
            assert_eq!((*node2).value, 20);

            // Clean up
            drop(Box::from_raw(node1));
            drop(Box::from_raw(node2));
        }
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_non_null_list() {
        // Reset the counter before the test
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);

        // Manually create nodes
        // Box::leak returns &mut T, which helps creating NonNull
        let node1 = Box::leak(Box::new(new_node(100)));
        let node2 = Box::leak(Box::new(new_node(200)));

        let ptr1 = NonNull::from(node1);
        let ptr2 = NonNull::from(node2);

        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);

        unsafe {
            let mut l = DLinkedList::<NonNull<TestNode>, TestTag>::new();
            l.push_back(ptr1);
            l.push_back(ptr2);

            let mut iter = l.iter();
            assert_eq!(iter.next().unwrap().as_ref().value, 100);
            assert_eq!(iter.next().unwrap().as_ref().value, 200);
            assert!(iter.next().is_none());
        } // l dropped here. NonNull doesn't need drop, so no drain.

        // Nodes should still exist
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);

        unsafe {
            // Clean up
            drop(Box::from_raw(ptr1.as_ptr()));
            drop(Box::from_raw(ptr2.as_ptr()));
        }

        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_clear() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

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

    #[test]
    fn test_remove_middle() {
        // Reset the counter before the test
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        {
            let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();

            let node1 = Box::new(new_node(1));
            l.push_back(node1);

            let node2 = Box::new(new_node(2));

            // NOTE: use `node_p = node2.as_ptr()`  will trigger miri stack borrow rule.
            // we use into_raw and then from_raw
            let node2_p = Box::into_raw(node2);
            l.push_back(unsafe { Box::from_raw(node2_p) });

            let node3 = Box::new(new_node(3));
            l.push_back(node3);

            assert_eq!(l.len(), 3);
            assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);

            let node2 = unsafe { l.remove_node(node2_p).unwrap() };
            assert_eq!(l.len(), 2);
            assert_eq!(node2.value, 2);

            let node4 = Box::new(new_node(4));

            let node4_p = Box::into_raw(node4);
            assert!(unsafe { l.remove_node(node4_p) }.is_none());
            unsafe {
                let _ = Box::from_raw(node4_p);
            }
        } // `l` goes out of scope here, triggering DLinkedList's Drop, which drains and drops nodes.

        // All nodes should have been dropped
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_peak_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();

        let node1 = Arc::new(new_node(1));
        l.push_back(node1);

        let node2 = Arc::new(new_node(2));
        l.push_back(node2);

        let node3 = Arc::new(new_node(3));
        l.push_back(node3.clone());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        let node3_p = Arc::as_ptr(&node3);

        unsafe { l.peak(node3_p) };

        // Check the order of remaining elements
        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 3);
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 1);
            assert_eq!(drain.next().unwrap().value, 2);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.len(), 0);
    }
}
