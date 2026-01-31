//! An owned intrusive singly linked list.

//!
//! This module provides `SLinkedListOwned`, a singly linked list for owned data (`Box<T>`).
//! Elements are responsible for storing their own `next` pointer.
//!
//! It's optimized for FIFO (First-In, First-Out) queue-like behavior.
//!
//! # Features
//! - O(1) push to back and pop from front.
//! - Owned elements (`Box<T>`).
//! - **Direct operation via SListItemOwned trait** (this feature is not in [crate::slist])
//!
//! # Example
//! ```rust
//! use embed_collections::slist_owned::{SLinkedListOwned, SListItemOwned};
//! use core::ptr::NonNull;
//!
//! struct MyTask {
//!     priority: u8,
//!     description: String,
//!     next: Option<NonNull<MyTask>>, // `next` pointer embedded directly
//! }
//!
//! impl MyTask {
//!     fn new(priority: u8, desc: &str) -> Self {
//!         MyTask {
//!             priority,
//!             description: desc.to_string(),
//!             next: None,
//!         }
//!     }
//! }
//!
//! // Implement SListItemOwned to provide access to the `next` pointer.
//! pub struct MyTaskTag;
//! impl SListItemOwned<MyTaskTag> for MyTask {
//!     fn get_node(&mut self) -> &mut Option<NonNull<Self>> {
//!         &mut self.next
//!     }
//! }
//!
//! let mut task_queue = SLinkedListOwned::<MyTask, MyTaskTag>::new();
//!
//! task_queue.push_back(Box::new(MyTask::new(1, "Handle user login")));
//! task_queue.push_back(Box::new(MyTask::new(2, "Process analytics data")));
//! task_queue.push_back(Box::new(MyTask::new(1, "Send welcome email")));
//!
//! assert_eq!(task_queue.len(), 3);
//!
//! // Process tasks in FIFO order
//! assert_eq!(task_queue.pop_front().unwrap().description, "Handle user login");
//! assert_eq!(task_queue.pop_front().unwrap().description, "Process analytics data");
//! assert_eq!(task_queue.pop_front().unwrap().description, "Send welcome email");
//! assert!(task_queue.is_empty());
//! ```
//!
//! # Using `SListItemOwned` Methods
//!
//! The `SListItemOwned` trait provides default methods like `append`, `pop`, and `consume_all`
//! that allow direct manipulation of list nodes.
//!
//! The `Drop` implementation on an item should call `consume_all` to ensure that if a node
//! is dropped, all subsequent nodes in the chain are also safely dropped, preventing memory leaks.
//!
//! ```rust
//! use embed_collections::slist_owned::{SListItemOwned, SLinkedListOwned};
//! use core::ptr::NonNull;
//!
//! // Define an item that can be part of the list
//! struct MyTask {
//!     description: String,
//!     next: Option<NonNull<MyTask>>,
//! }
//!
//! impl MyTask {
//!     fn new(desc: &str) -> Self {
//!         MyTask {
//!             description: desc.to_string(),
//!             next: None,
//!         }
//!     }
//! }
//!
//! impl Drop for MyTask {
//!     fn drop(&mut self) {
//!         // Ensure subsequent nodes are dropped to prevent memory leaks.
//!         SListItemOwned::consume_all(self);
//!     }
//! }
//!
//! impl SListItemOwned<()> for MyTask {
//!     fn get_node(&mut self) -> &mut Option<NonNull<Self>> {
//!         &mut self.next
//!     }
//! }
//!
//! // Create a base task node, which can act as the head of its own list.
//! let mut base_task = Box::new(MyTask::new("Base task"));
//!
//! // Create another list to append.
//! let mut sub_queue = SLinkedListOwned::<MyTask, ()>::new();
//! sub_queue.push_back(Box::new(MyTask::new("Sub task 1")));
//! sub_queue.push_back(Box::new(MyTask::new("Sub task 2")));
//!
//! // Use `append` to attach `sub_queue` after `base_task`.
//!
//! base_task.append(sub_queue);
//!
//! // The list is now: "Base task" -> "Sub task 1" -> "Sub task 2"
//! let popped_task = base_task.pop();
//! assert_eq!(popped_task.unwrap().description, "Sub task 1");
//! let popped_task = base_task.pop();
//! assert_eq!(popped_task.unwrap().description, "Sub task 2");
//! assert!(base_task.pop().is_none());
//! ```

use alloc::boxed::Box;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// A trait for items that can be stored in an `SLinkedListOwned`.
///
/// The item must contain a field that stores an `Option<NonNull<Self>>`, which will be
/// used as the `next` pointer in the linked list.
///
/// The tag is used to distinguish different list memberships within the same item.
/// For a single list, you can use `()`.
///
/// # Safety
/// Implementors must ensure `get_node` returns a mutable reference to the `Option<NonNull<Self>>`
/// field that is designated for this linked list.
pub trait SListItemOwned<Tag>: Sized {
    /// Returns a mutable reference to the next-pointer field.
    fn get_node(&mut self) -> &mut Option<NonNull<Self>>;

    /// Appends a list after the current node. `self` must be a tail node.
    /// The list `l` is consumed. The caller is responsible for updating the length
    /// and tail of the list that contains `self`.
    fn append(&mut self, mut l: SLinkedListOwned<Self, Tag>) {
        let node = self.get_node();
        assert!(node.is_none(), "can only append to a tail node");

        *node = l.head.take();

        // The list `l` is now empty, and we prevent its Drop implementation
        // from deallocating the nodes we've just moved.
        l.length = 0;
        l.tail = None;
    }

    /// Pops the item immediately after this one.
    ///
    /// The list's length and tail must be updated manually if the popped item was the tail.
    fn pop(&mut self) -> Option<Box<Self>> {
        let node = self.get_node();
        if let Some(next_ptr) = node {
            let mut popped_box: Box<Self> = unsafe { Box::from_raw(next_ptr.as_ptr()) };
            *node = popped_box.get_node().take(); // Ensure popped node's next is None
            Some(popped_box)
        } else {
            None
        }
    }

    /// Consumes and drops all nodes that follow the current one.
    fn consume_all(&mut self) {
        let mut current = self.get_node().take();
        while let Some(node_ptr) = current {
            let mut node_box: Box<Self> = unsafe { Box::from_raw(node_ptr.as_ptr()) };
            current = node_box.get_node().take();
            // node_box is dropped here.
        }
    }
}

/// An owned, intrusive singly linked list optimized for FIFO queues.
///
/// This list works with `Box<T>` and requires items to implement `SListItemOwned`.
/// It provides O(1) push to back and pop from front.
#[repr(C)]
pub struct SLinkedListOwned<T, Tag>
where
    T: SListItemOwned<Tag>,
{
    length: u64,
    head: Option<NonNull<T>>,
    tail: Option<NonNull<T>>,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T, Tag> Send for SLinkedListOwned<T, Tag> where T: SListItemOwned<Tag> {}

impl<T, Tag> SLinkedListOwned<T, Tag>
where
    T: SListItemOwned<Tag>,
{
    /// Creates a new, empty singly linked list.
    #[inline(always)]
    pub const fn new() -> Self {
        SLinkedListOwned { length: 0, head: None, tail: None, _phan: PhantomData }
    }

    /// Clears the list, dropping all elements.
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }

    /// Returns the length of the list.
    #[inline(always)]
    pub fn get_length(&self) -> u64 {
        self.length
    }

    /// Returns the length of the list as `usize`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.length as usize
    }

    /// Returns `true` if the list contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Prepends an element to the front of the list.
    #[inline]
    pub fn push_front(&mut self, mut item: Box<T>) {
        debug_assert!(item.get_node().is_none(), "Node is already in a list");
        // The new item's next pointer should point to the current head
        *item.get_node() = self.head;
        let ptr = NonNull::from(Box::leak(item));
        self.head = Some(ptr); // New item becomes the head
        if self.tail.is_none() {
            // If the list was empty, the new item is also the tail
            self.tail = Some(ptr);
        }
        self.length += 1;
    }

    /// Appends an element to the back of the list (FIFO: enqueue).
    #[inline]
    pub fn push_back(&mut self, mut item: Box<T>) {
        // NOTE: it's owned list, should not reuse item.
        // pop and drain should responsible to clear the item.pointer
        debug_assert!(item.get_node().is_none(), "Node is already in a list");
        let ptr = NonNull::from(Box::leak(item));
        // The new ptr is the new tail.
        // `replace` gives us the previous tail and updates it to the new one.
        let old_tail = self.tail.replace(ptr);
        match old_tail {
            Some(mut old_tail_ptr) => {
                // List was not empty, link old tail to new tail
                unsafe {
                    *old_tail_ptr.as_mut().get_node() = Some(ptr);
                }
            }
            None => {
                debug_assert!(self.head.is_none());
                // List was empty, new node is also the head
                self.head = Some(ptr);
            }
        }
        self.length += 1;
    }

    /// Removes the first element and returns it (FIFO: dequeue).
    pub fn pop_front(&mut self) -> Option<Box<T>> {
        if let Some(head_ptr) = self.head {
            let mut head_box: Box<T> = unsafe { Box::from_raw(head_ptr.as_ptr()) };
            self.head = *head_box.get_node();

            if self.head.is_none() {
                self.tail = None;
            }

            self.length -= 1;

            *head_box.get_node() = None;

            Some(head_box)
        } else {
            None
        }
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn get_front(&self) -> Option<&T> {
        self.head.map(|ptr| unsafe { ptr.as_ref() })
    }

    /// Returns a mutable reference to the front element.
    #[inline]
    pub fn get_front_mut(&mut self) -> Option<&mut T> {
        self.head.map(|mut ptr| unsafe { ptr.as_mut() })
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn get_back(&self) -> Option<&T> {
        self.tail.map(|ptr| unsafe { ptr.as_ref() })
    }

    /// Returns a mutable reference to the back element.
    #[inline]
    pub fn get_back_mut(&mut self) -> Option<&mut T> {
        self.tail.map(|mut ptr| unsafe { ptr.as_mut() })
    }

    /// Checks if the given node is the head of the list.
    #[inline(always)]
    pub fn is_front(&self, node: &T) -> bool {
        self.head.map_or(false, |head| head.as_ptr() == node as *const T as *mut T)
    }

    /// Returns a draining iterator that removes items from the list.
    #[inline(always)]
    pub fn drain(&mut self) -> SLinkedListOwnedDrainer<'_, T, Tag> {
        SLinkedListOwnedDrainer { list: self }
    }

    /// Returns a mutable iterator over the list.
    #[inline(always)]
    pub fn iter_mut(&mut self) -> SLinkedListOwnedIterMut<'_, T, Tag> {
        SLinkedListOwnedIterMut { cur: self.head, _phan: PhantomData }
    }
}

impl<T, Tag> Default for SLinkedListOwned<T, Tag>
where
    T: SListItemOwned<Tag>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, Tag> Drop for SLinkedListOwned<T, Tag>
where
    T: SListItemOwned<Tag>,
{
    fn drop(&mut self) {
        // Drain the list to drop all elements.
        self.drain().for_each(drop);
    }
}

/// A draining iterator for `SLinkedListOwned`.
pub struct SLinkedListOwnedDrainer<'a, T, Tag>
where
    T: SListItemOwned<Tag>,
{
    list: &'a mut SLinkedListOwned<T, Tag>,
}

impl<'a, T, Tag> Iterator for SLinkedListOwnedDrainer<'a, T, Tag>
where
    T: SListItemOwned<Tag>,
{
    type Item = Box<T>;

    #[inline]
    fn next(&mut self) -> Option<Box<T>> {
        self.list.pop_front()
    }
}

/// A mutable iterator for `SLinkedListOwned`.
pub struct SLinkedListOwnedIterMut<'a, T, Tag>
where
    T: SListItemOwned<Tag>,
{
    cur: Option<NonNull<T>>,
    _phan: PhantomData<(&'a mut T, fn(&Tag))>,
}

impl<'a, T, Tag> Iterator for SLinkedListOwnedIterMut<'a, T, Tag>
where
    T: SListItemOwned<Tag> + 'a,
{
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut cur_ptr) = self.cur {
            let cur_mut = unsafe { cur_ptr.as_mut() };
            self.cur = *cur_mut.get_node();
            Some(cur_mut)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct TestTag;

    #[derive(Debug)]
    pub struct TestNode {
        pub value: i64,
        pub next: Option<NonNull<TestNode>>,
    }

    static ACTIVE_NODE_COUNT: AtomicUsize = AtomicUsize::new(0);

    impl Drop for TestNode {
        fn drop(&mut self) {
            ACTIVE_NODE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    impl SListItemOwned<TestTag> for TestNode {
        fn get_node(&mut self) -> &mut Option<NonNull<Self>> {
            &mut self.next
        }
    }

    fn new_node(v: i64) -> TestNode {
        ACTIVE_NODE_COUNT.fetch_add(1, Ordering::SeqCst);
        TestNode { value: v, next: None }
    }

    #[test]
    fn test_push_back_pop_front() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedListOwned::<TestNode, TestTag>::new();

        l.push_back(Box::new(new_node(1)));
        l.push_back(Box::new(new_node(2)));
        l.push_back(Box::new(new_node(3)));

        assert_eq!(3, l.get_length());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);
        assert!(!l.is_empty());

        assert_eq!(l.get_front().unwrap().value, 1);
        assert_eq!(l.get_back().unwrap().value, 3);

        let n1 = l.pop_front();
        assert!(n1.is_some());
        assert_eq!(n1.unwrap().value, 1);
        assert_eq!(l.get_length(), 2);

        let n2 = l.pop_front();
        assert!(n2.is_some());
        assert_eq!(n2.unwrap().value, 2);
        assert_eq!(l.get_length(), 1);

        let n3 = l.pop_front();
        assert!(n3.is_some());
        assert_eq!(n3.unwrap().value, 3);
        assert_eq!(l.get_length(), 0);

        assert!(l.pop_front().is_none());
        assert!(l.is_empty());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_push_front() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedListOwned::<TestNode, TestTag>::new();

        l.push_front(Box::new(new_node(1))); // List: [1]
        assert_eq!(l.len(), 1);
        assert_eq!(l.get_front().unwrap().value, 1);
        assert_eq!(l.get_back().unwrap().value, 1);

        l.push_front(Box::new(new_node(2))); // List: [2, 1]
        assert_eq!(l.len(), 2);
        assert_eq!(l.get_front().unwrap().value, 2);
        assert_eq!(l.get_back().unwrap().value, 1);

        l.push_front(Box::new(new_node(3))); // List: [3, 2, 1]
        assert_eq!(l.len(), 3);
        assert_eq!(l.get_front().unwrap().value, 3);
        assert_eq!(l.get_back().unwrap().value, 1);

        // Check order after pops
        assert_eq!(l.pop_front().unwrap().value, 3);
        assert_eq!(l.pop_front().unwrap().value, 2);
        assert_eq!(l.pop_front().unwrap().value, 1);
        assert!(l.is_empty());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_drain() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedListOwned::<TestNode, TestTag>::new();

        l.push_back(Box::new(new_node(10)));
        l.push_back(Box::new(new_node(20)));
        l.push_back(Box::new(new_node(30)));

        assert_eq!(l.get_length(), 3);
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 3);

        {
            let mut drain = l.drain();
            assert_eq!(drain.next().unwrap().value, 10);
            assert_eq!(drain.next().unwrap().value, 20);
            assert_eq!(drain.next().unwrap().value, 30);
            assert!(drain.next().is_none());
        }

        assert_eq!(l.get_length(), 0);
        assert!(l.is_empty());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_iter_mut() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedListOwned::<TestNode, TestTag>::new();

        l.push_back(Box::new(new_node(100)));
        l.push_back(Box::new(new_node(200)));
        l.push_back(Box::new(new_node(300)));

        let mut iter = l.iter_mut();
        let n1 = iter.next().unwrap();
        assert_eq!(n1.value, 100);
        n1.value = 101;

        let n2 = iter.next().unwrap();
        assert_eq!(n2.value, 200);
        n2.value = 201;

        let n3 = iter.next().unwrap();
        assert_eq!(n3.value, 300);
        n3.value = 301;

        assert!(iter.next().is_none());

        assert_eq!(l.pop_front().unwrap().value, 101);
        assert_eq!(l.pop_front().unwrap().value, 201);
        assert_eq!(l.pop_front().unwrap().value, 301);

        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_clear() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedListOwned::<TestNode, TestTag>::new();

        l.push_back(Box::new(new_node(1)));
        l.push_back(Box::new(new_node(2)));

        assert_eq!(l.len(), 2);
        l.clear();
        assert!(l.is_empty());
        assert_eq!(l.len(), 0);
        assert!(l.get_front().is_none());
        assert!(l.get_back().is_none());
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_drop() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        {
            let mut l = SLinkedListOwned::<TestNode, TestTag>::new();
            l.push_back(Box::new(new_node(1)));
            l.push_back(Box::new(new_node(2)));
            assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 2);
        }
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }
}
