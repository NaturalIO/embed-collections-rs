use crate::Pointer;
use std::marker::PhantomData;
/// A linked list for Btree Node in LRU
///
/// TODO should cleanup unused functions
use std::{fmt, mem, ptr::null};

/// A trait to return internal mutable ListNode for specified list
///
/// The tag is for distinguish different ListNode among the item.
///
/// NOTE: User must use UnsafeCell to hold ListNode
pub unsafe trait ListItem<Tag>: Sized {
    fn get_node(&self) -> &mut ListNode<Self, Tag>;
}

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
    #[inline(always)]
    pub fn new() -> Self {
        DLinkedList { length: 0, head: null(), tail: null(), _phan: Default::default() }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.length = 0;
        self.head = null();
        self.tail = null();
    }

    #[inline(always)]
    pub fn get_length(&self) -> u64 {
        return self.length;
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        return self.length as usize;
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

    #[inline]
    pub fn get_front(&self) -> Option<&P::Target> {
        if self.head.is_null() { None } else { unsafe { Some(&(*self.head)) } }
    }

    #[inline]
    pub fn get_back(&self) -> Option<&P::Target> {
        if self.tail.is_null() { None } else { unsafe { Some(&(*self.tail)) } }
    }

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
    #[inline(always)]
    pub fn iter<'a>(&'a self) -> DLinkedListIterator<'a, P, Tag> {
        DLinkedListIterator { list: self, cur: null() }
    }

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

    impl crate::Pointer for Box<TestNode> {
        type Target = TestNode;

        fn as_ref(&self) -> &Self::Target {
            &**self
        }

        unsafe fn from_raw(p: *const Self::Target) -> Self {
            unsafe { Box::from_raw(p as *mut Self::Target) }
        }

        fn into_raw(self) -> *const Self::Target {
            Box::into_raw(self) as *const Self::Target
        }
    }

    impl crate::Pointer for Arc<TestNode> {
        type Target = TestNode;

        fn as_ref(&self) -> &Self::Target {
            &**self
        }

        unsafe fn from_raw(p: *const Self::Target) -> Self {
            unsafe { Arc::from_raw(p as *const Self::Target) }
        }

        fn into_raw(self) -> *const Self::Target {
            Arc::into_raw(self) as *const Self::Target
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
            unsafe {
                assert_eq!(iter.next().unwrap().value, 10);
                assert_eq!(iter.next().unwrap().value, 20);
                assert!(iter.next().is_none());
            }
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
}
