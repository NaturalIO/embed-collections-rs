use crate::Pointer;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ptr::null;

/// A trait to return internal mutable SListNode for specified list
///
/// The tag is for distinguish different SListNode among the item.
///
/// NOTE: User must use UnsafeCell to hold SListNode
pub unsafe trait SListItem<Tag>: Sized {
    fn get_node(&self) -> &mut SListNode<Self, Tag>;
}

pub struct SListNode<T: Sized, Tag> {
    next: *const T,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<T, Tag> Send for SListNode<T, Tag> {}

impl<T: SListItem<Tag>, Tag> SListNode<T, Tag> {}

impl<T, Tag> Default for SListNode<T, Tag> {
    #[inline(always)]
    fn default() -> Self {
        Self { next: null(), _phan: Default::default() }
    }
}

impl<T: SListItem<Tag> + fmt::Debug, Tag> fmt::Debug for SListNode<T, Tag> {
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

/// A singly linked list with head and tail pointers (FIFO queue)
pub struct SLinkedList<P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    length: u64,
    head: *const P::Target,
    tail: *const P::Target,
    _phan: PhantomData<fn(&Tag)>,
}

unsafe impl<P, Tag> Send for SLinkedList<P, Tag>
where
    P: Pointer,
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
    #[inline(always)]
    pub fn new() -> Self {
        SLinkedList { length: 0, head: null(), tail: null(), _phan: Default::default() }
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

    /// Appends an element to the back of the list (FIFO: enqueue).
    #[inline]
    pub fn push_back(&mut self, item: P) {
        let node = item.as_ref().get_node();
        node.next = null();

        let ptr = item.into_raw();

        if self.tail.is_null() {
            // List is empty
            self.head = ptr;
        } else {
            // List is not empty, update current tail's next
            unsafe {
                (*self.tail).get_node().next = ptr;
            }
        }
        self.tail = ptr;
        self.length += 1;
    }

    /// Removes the first element and returns it (FIFO: dequeue).
    pub fn pop_front(&mut self) -> Option<P> {
        if self.head.is_null() {
            None
        } else {
            let head_ptr = self.head;
            let node = unsafe { (*head_ptr).get_node() };
            let next_ptr = node.next;

            // Update head to next
            self.head = next_ptr;

            // If head became null (list empty), update tail to null too
            if self.head.is_null() {
                self.tail = null();
            }

            // Clean up the removed node's next pointer
            node.next = null();
            self.length -= 1;

            Some(unsafe { P::from_raw(head_ptr) })
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
        if self.head.is_null() { false } else { self.head == node as *const P::Target }
    }

    // NOTE: If you plan on turn the raw pointer to owned, use drain instead
    #[inline(always)]
    pub fn iter<'a>(&'a self) -> SLinkedListIterator<'a, P, Tag> {
        SLinkedListIterator { list: self, cur: null() }
    }

    #[inline(always)]
    pub fn drain<'a>(&'a mut self) -> SLinkedListDrainer<'a, P, Tag> {
        SLinkedListDrainer { list: self }
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

pub struct SLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    list: &'a SLinkedList<P, Tag>,
    cur: *const P::Target,
}

unsafe impl<'a, P, Tag> Send for SLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for SLinkedListIterator<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
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

pub struct SLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
    list: &'a mut SLinkedList<P, Tag>,
}

unsafe impl<'a, P, Tag> Send for SLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
{
}

impl<'a, P, Tag> Iterator for SLinkedListDrainer<'a, P, Tag>
where
    P: Pointer,
    P::Target: SListItem<Tag>,
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
    use std::cell::UnsafeCell;
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct TestTag;

    #[derive(Debug)]
    pub struct TestNode {
        pub value: i64,
        pub node: UnsafeCell<SListNode<Self, TestTag>>,
        pub drop_detector: usize,
    }

    static NEXT_DROP_ID: AtomicUsize = AtomicUsize::new(0);
    static ACTIVE_NODE_COUNT: AtomicUsize = AtomicUsize::new(0);

    impl Drop for TestNode {
        fn drop(&mut self) {
            ACTIVE_NODE_COUNT.fetch_sub(1, Ordering::SeqCst);
        }
    }

    unsafe impl Send for TestNode {}

    unsafe impl SListItem<TestTag> for TestNode {
        fn get_node(&self) -> &mut SListNode<Self, TestTag> {
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

    fn new_node(v: i64) -> TestNode {
        ACTIVE_NODE_COUNT.fetch_add(1, Ordering::SeqCst);
        TestNode {
            value: v,
            node: UnsafeCell::new(SListNode::default()),
            drop_detector: NEXT_DROP_ID.fetch_add(1, Ordering::SeqCst),
        }
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

        assert_eq!(3, l.get_length());
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
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_drain() {
        ACTIVE_NODE_COUNT.store(0, Ordering::SeqCst);
        let mut l = SLinkedList::<Box<TestNode>, TestTag>::new();

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
        assert_eq!(ACTIVE_NODE_COUNT.load(Ordering::SeqCst), 0);
    }
}
