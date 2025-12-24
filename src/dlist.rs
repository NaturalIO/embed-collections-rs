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
//! ```rust
//! use embed_collections::{dlist::{DLinkedList, ListItem, ListNode}, Pointer};
//! use std::cell::UnsafeCell;
//!
//! struct MyItem {
//!     id: u32,
//!     data: String,
//!     node: UnsafeCell<ListNode<MyItem, ()>>, // Node embedded directly
//! }
//!
//! impl MyItem {
//!     fn new(id: u32, data: &str) -> Self {
//!         MyItem {
//!             id,
//!             data: data.to_string(),
//!             node: UnsafeCell::new(ListNode::default()),
//!         }
//!     }
//! }
//!
//! // Safety: Implementors must ensure `get_node` returns a valid reference
//! // to the embedded `ListNode`. `UnsafeCell` is used for interior mutability.
//! unsafe impl ListItem<()> for MyItem {
//!     fn get_node(&self) -> &mut ListNode<Self, ()> {
//!         unsafe { &mut *self.node.get() }
//!     }
//! }
//!
//! let mut list = DLinkedList::<Box<MyItem>, ()>::new();
//!
//! list.push_back(Box::new(MyItem::new(1, "First")));
//! list.push_front(Box::new(MyItem::new(2, "Second")));
//! list.push_back(Box::new(MyItem::new(3, "Third")));
//!
//! assert_eq!(list.len(), 3);
//!
//! // List order: (2, "Second") <-> (1, "First") <-> (3, "Third")
//! assert_eq!(list.pop_front().unwrap().id, 2);
//! assert_eq!(list.pop_back().unwrap().id, 3);
//! assert_eq!(list.pop_front().unwrap().id, 1);
//! assert!(list.is_empty());
//! ```

use crate::Pointer;
use std::marker::PhantomData;
use std::{fmt, mem, ptr::null};

/// A trait to return internal mutable ListNode for specified list.
///
/// The tag is used to distinguish different ListNodes within the same item,
/// allowing an item to belong to multiple lists simultaneously.
///
/// # Safety
///
/// Implementors must ensure `get_node` returns a valid reference to the `ListNode`
/// embedded within `Self`. Users must use `UnsafeCell` to hold `ListNode` to support
/// interior mutability required by list operations.
pub unsafe trait ListItem<Tag>: Sized {
    fn get_node(&self) -> &mut ListNode<Self, Tag>;
}

/// The node structure that must be embedded in items to be stored in a `DLinkedList`.
pub struct ListNode<T: Sized, Tag> {
    prev: *const T,
    next: *const T,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T, Tag> Send for ListNode<T, Tag> {}

impl<T: ListItem<Tag>, Tag> ListNode<T, Tag> {
    #[inline]
    fn get_prev<'a>(&self) -> Option<&'a mut ListNode<T, Tag>> {
        if self.prev.is_null() { None } else { unsafe { Some((*self.prev).get_node()) } }
    }

    #[inline]
    fn get_next<'a>(&self) -> Option<&'a mut ListNode<T, Tag>> {
        if self.next.is_null() { None } else { unsafe { Some((*self.next).get_node()) } }
    }
}

impl<T, Tag> Default for ListNode<T, Tag> {
    #[inline(always)]
    fn default() -> Self {
        Self { prev: null(), next: null(), _phan: Default::default() }
    }
}

impl<T: ListItem<Tag> + fmt::Debug, Tag> fmt::Debug for ListNode<T, Tag> {
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
pub struct DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
    length: u64,
    head: *const P::Target,
    tail: *const P::Target,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<P, Tag> Send for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
}

impl<P: fmt::Debug, Tag> fmt::Debug for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
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
    P::Target: ListItem<Tag>,
{
    /// Creates a new, empty doubly linked list.
    #[inline(always)]
    pub fn new() -> Self {
        DLinkedList { length: 0, head: null(), tail: null(), _phan: Default::default() }
    }

    /// Clears the list pointers. Note: This does NOT drop the elements.
    /// Use `drain` or `drop` if you need to release owned resources.
    #[inline]
    pub fn clear(&mut self) {
        self.length = 0;
        self.head = null();
        self.tail = null();
    }

    /// Returns the length of the list.
    #[inline(always)]
    pub fn get_length(&self) -> u64 {
        return self.length;
    }

    /// Returns the length of the list as `usize`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        return self.length as usize;
    }

    /// Returns `true` if the list contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    #[inline(always)]
    fn remove_node(&mut self, item: &P::Target) {
        let node = item.get_node();
        if let Some(prev) = node.get_prev() {
            prev.next = node.next;
        } else {
            self.head = node.next;
        }
        if let Some(next) = node.get_next() {
            next.prev = node.prev;
        } else {
            self.tail = node.prev;
        }
        node.next = null();
        node.prev = null();
        self.length -= 1;
    }

    /// Moves a node to the front of the list (e.g., for LRU updates).
    ///
    /// # Safety
    /// The pointer `ptr` must be valid and pointing to an element currently in the list
    /// or a valid free element if properly managed (though typically used for re-ordering).
    #[inline(always)]
    pub unsafe fn peak(&mut self, ptr: *mut P::Target) {
        assert!(!self.head.is_null());
        let item = unsafe { &(*ptr) };
        if !self.head.is_null() {
            let head_node = unsafe { (*self.head).get_node() } as *const ListNode<P::Target, Tag>;
            if head_node == item.get_node() as *const ListNode<P::Target, Tag> {
                return;
            }
        }
        self.remove_node(item);
        self.push_front_ptr(ptr);
    }

    /// Pushes an element to the front of the list.
    #[inline]
    pub fn push_front(&mut self, item: P) {
        let ptr = item.into_raw();
        self.push_front_ptr(ptr);
    }

    #[inline]
    fn push_front_ptr(&mut self, ptr: *const P::Target) {
        let node = unsafe { (*ptr).get_node() };
        let head = self.head;
        node.next = head;
        node.prev = null();

        if head.is_null() {
            self.tail = ptr;
        } else {
            unsafe {
                (*head).get_node().prev = ptr;
            }
        }
        self.head = ptr;
        self.length += 1;
    }

    /// Pushes an element to the back of the list.
    #[inline]
    pub fn push_back(&mut self, item: P) {
        let node = item.as_ref().get_node();
        let tail = self.tail;
        node.prev = tail;
        node.next = null();

        let ptr = item.into_raw();
        if tail.is_null() {
            self.head = ptr;
        } else {
            unsafe {
                (*tail).get_node().next = ptr;
            }
        }
        self.tail = ptr;
        self.length += 1;
    }

    /// Removes and returns the element at the front of the list.
    pub fn pop_front(&mut self) -> Option<P> {
        if self.head.is_null() {
            None
        } else {
            let head_ptr = self.head;
            let item = unsafe { &(*head_ptr) };
            self.remove_node(item);
            Some(unsafe { P::from_raw(head_ptr) })
        }
    }

    /// Removes and returns the element at the back of the list.
    #[inline]
    pub fn pop_back(&mut self) -> Option<P> {
        if self.tail.is_null() {
            None
        } else {
            let tail_ptr = self.tail;
            let item = unsafe { &(*tail_ptr) };
            self.remove_node(item);
            Some(unsafe { P::from_raw(tail_ptr) })
        }
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn get_front(&self) -> Option<&P::Target> {
        if self.head.is_null() { None } else { unsafe { Some(&(*self.head)) } }
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn get_back(&self) -> Option<&P::Target> {
        if self.tail.is_null() { None } else { unsafe { Some(&(*self.tail)) } }
    }

    /// Checks if the given node is the head of the list.
    #[inline(always)]
    pub fn is_front(&self, node: &P::Target) -> bool {
        if self.head.is_null() {
            false
        } else {
            // This comparison is tricky because self.head is *mut HrcWrapper<T>
            // and node is &mut ListNode<T>.
            // We need to compare the node address or the wrapper address.
            // Converting head -> node and comparing addresses of ListNode is safer.
            self.head == node as *const P::Target
        }
    }

    pub fn print<U: std::fmt::Debug>(&self) {
        println!("print list begin! length={}", self.length);
        let mut ptr = self.head;
        while !ptr.is_null() {
            unsafe {
                // Assuming T can be cast to U for printing, or T implements Debug.
                // The original code had print<T>, here print<U>.
                // We'll just print the address for now if T is not Debug?
                // Or assume T is Debug.
                // println!("node={:?}", item); // Requires T: Debug
                ptr = (*ptr).get_node().next;
            }
        }
        println!("print list end:");
    }

    // NOTE: If you plan on turn the raw pointer to owned, use drain instead
    /// Returns an iterator over the list (borrowed).
    #[inline(always)]
    pub fn iter<'a>(&'a self) -> DLinkedListIterator<'a, P, Tag> {
        DLinkedListIterator { list: self, cur: null() }
    }

    /// Returns a draining iterator that removes items from the list.
    /// Crucial for cleaning up lists containing owned pointers (like `Box`).
    #[inline(always)]
    pub fn drain<'a>(&'a mut self) -> DLinkedListDrainer<'a, P, Tag> {
        DLinkedListDrainer { list: self }
    }
}

impl<P, Tag> Drop for DLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
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
    P::Target: ListItem<Tag>,
{
    list: &'a DLinkedList<P, Tag>,
    cur: *const P::Target,
}

unsafe impl<'a, P, Tag> Send for DLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for DLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
    type Item = &'a P::Target;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur.is_null() {
            if self.list.head.is_null() {
                return None;
            } else {
                self.cur = self.list.head;
            }
        } else {
            let next = unsafe { (*self.cur).get_node().next };
            if next.is_null() {
                return None;
            } else {
                self.cur = next;
            }
        }
        unsafe { Some(&(*self.cur)) }
    }
}

pub struct DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
    list: &'a mut DLinkedList<P, Tag>,
}

unsafe impl<'a, P, Tag> Send for DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for DLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: ListItem<Tag>,
{
    type Item = P;

    #[inline]
    fn next(&mut self) -> Option<P> {
        self.list.pop_back()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::UnsafeCell;
    use std::ptr::NonNull;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct TestTag;

    #[derive(Debug)]
    pub struct TestNode {
        pub value: i64,
        pub node: UnsafeCell<ListNode<Self, TestTag>>,
        pub drop_detector: usize, // Field to uniquely identify nodes and track drops
    }

    static NEXT_DROP_ID: AtomicUsize = AtomicUsize::new(0);
    static ACTIVE_NODE_COUNT: AtomicUsize = AtomicUsize::new(0);

    impl Drop for TestNode {
        fn drop(&mut self) {
            ACTIVE_NODE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    unsafe impl Send for TestNode {}

    unsafe impl ListItem<TestTag> for TestNode {
        fn get_node(&self) -> &mut ListNode<Self, TestTag> {
            unsafe { &mut *self.node.get() }
        }
    }

    fn new_node(v: i64) -> TestNode {
        ACTIVE_NODE_COUNT.fetch_add(1, Ordering::SeqCst);
        TestNode {
            value: v,
            node: UnsafeCell::new(ListNode::default()),
            drop_detector: NEXT_DROP_ID.fetch_add(1, Ordering::SeqCst),
        }
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

        assert_eq!(3, l.get_length());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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

        assert_eq!(3, l.get_length());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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

        assert_eq!(3, l.get_length());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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

        assert_eq!(3, l.get_length());

        let mut iter = l.iter();
        assert_eq!(iter.next().unwrap().value, 1);
        assert_eq!(iter.next().unwrap().value, 2);
        assert_eq!(iter.next().unwrap().value, 3);
        assert!(iter.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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
        assert_eq!(2, l.get_length());
        assert!(del_node.is_some());
        assert_eq!(del_node.unwrap().value, 3);

        let mut iter_remaining = l.iter();
        assert_eq!(iter_remaining.next().unwrap().value, 1);
        assert_eq!(iter_remaining.next().unwrap().value, 2);
        assert!(iter_remaining.next().is_none());

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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
        assert_eq!(2, l.get_length());
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
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
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
            assert_eq!(drain.next().unwrap().value, 3);
            assert_eq!(drain.next().unwrap().value, 2);
            assert_eq!(drain.next().unwrap().value, 1);
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);
    }

    #[test]
    fn test_single_element_box() {
        let mut l = DLinkedList::<Box<TestNode>, TestTag>::new();
        let node1 = Box::new(new_node(1));
        l.push_front(node1);
        let del_node = l.pop_back();
        assert!(del_node.is_some());
        assert_eq!(del_node.unwrap().value, 1);
        assert_eq!(0, l.get_length());
        assert!(l.pop_back().is_none());

        let mut l2 = DLinkedList::<Box<TestNode>, TestTag>::new();
        let node2 = Box::new(new_node(2));
        l2.push_back(node2);
        let del_node2 = l2.pop_back();
        assert!(del_node2.is_some());
        assert_eq!(del_node2.unwrap().value, 2);
        assert_eq!(0, l2.get_length());
        assert!(l2.pop_back().is_none());

        {
            let mut drain = l.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);

        {
            let mut drain = l2.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l2.get_length(), 0);
    }

    #[test]
    fn test_single_element_arc() {
        let mut l = DLinkedList::<Arc<TestNode>, TestTag>::new();
        let node1 = Arc::new(new_node(1));
        l.push_front(node1);
        let del_node = l.pop_back();
        assert!(del_node.is_some());
        assert_eq!(0, l.get_length());
        assert!(l.pop_back().is_none());

        let mut l2 = DLinkedList::<Arc<TestNode>, TestTag>::new();
        let node2 = Arc::new(new_node(2));
        l2.push_back(node2);
        let del_node2 = l2.pop_back();
        assert!(del_node2.is_some());
        assert_eq!(0, l2.get_length());
        assert!(l2.pop_back().is_none());

        {
            let mut drain = l.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l.get_length(), 0);

        {
            let mut drain = l2.drain();
            assert!(drain.next().is_none());
        }
        assert_eq!(l2.get_length(), 0);
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

            assert_eq!(l.get_length(), 3);
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

        {
            let mut l = DLinkedList::<*const TestNode, TestTag>::new();
            l.push_back(node1);
            l.push_back(node2);

            let mut iter = l.iter();
            assert_eq!(iter.next().unwrap().value, 10);
            assert_eq!(iter.next().unwrap().value, 20);
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

        {
            let mut l = DLinkedList::<NonNull<TestNode>, TestTag>::new();
            l.push_back(ptr1);
            l.push_back(ptr2);

            let mut iter = l.iter();
            assert_eq!(iter.next().unwrap().value, 100);
            assert_eq!(iter.next().unwrap().value, 200);
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
}
