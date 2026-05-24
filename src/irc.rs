//! Intrusive Reference Counter (Irc)
//!
//! `Irc` is an intrusive reference counting smart pointer, similar to `Arc` but without weak reference support.
//! It requires the inner type to implement [IrcItem] trait to provide a counter field.
//!
//! The underlayer of `Irc` is Box, unlike `Arc` which wrap a hidden ArcInner on your inner types,
//! Irc use the same memory location of your inner types.
//!
//! # Benefits
//!
//! - No need to manual implementing the inc / dec on counter.
//!
//! - No enforced weak counter if you don't need it (every atomic op has cost).
//!
//! - [IrcItem::on_drop] in the trait allow you to have the ownship of underlying inner memory after
//!   the reference count of Irc is dropped. And you only need to define the drop behavior once,
//!   instead of write the same logic `Arc::into_inner` in every possible places
//!   (If forgetting so make your code block and hard to debug).
//!
//! - Using `Irc` to wrap a `Box`, no additional memory allocation and memory fragmentation, no
//!   additional dereference cost (than using `Arc<Box<T>>`)
//!
//! - You can allocate a box from the time of its birth and wrap it will `Irc` for temporary usage,
//!   don't need to move bytes from / to stack. (especially when the inner object is large)
//!
//! - Advanced usage, multiple layer customized counter, on the same heap object, while preserving
//!   the safe boundary
//!
//! # Example (Irc wrapping a Box)
//!
//! ```rust
//! use embed_collections::irc::{Irc, IrcItem};
//! use core::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
//! use crossfire::oneshot;
//! use std::thread;
//! use std::time::Duration;
//!
//! // Usually we use Irc for some large structure, but we show a simple demo here.
//! struct MyItem {
//!     is_done: AtomicBool,
//!     counter: AtomicUsize,
//!     done_tx: Option<oneshot::TxOneshot<Box<MyItem>>>,
//! }
//!
//! unsafe impl IrcItem<()> for MyItem {
//!     type Counter = AtomicUsize;
//!     fn counter(&self) -> &Self::Counter {
//!         &self.counter
//!     }
//!
//!     // overwrite default behavior to send the item through channel
//!     fn on_drop(mut this: Box<Self>) {
//!         let done_tx = this.done_tx.take().unwrap();
//!         done_tx.send(this);
//!     }
//! }
//!
//! let (done_tx, done_rx) = oneshot::oneshot();
//! let boxed_item = Box::new(MyItem {
//!     is_done: AtomicBool::new(false),
//!     counter: AtomicUsize::new(0),
//!     done_tx: Some(done_tx),
//! });
//!
//! // Convert from Box to Irc, which does not have additional allocation.
//! let item = Irc::<_, ()>::from(boxed_item);
//! thread::spawn(move || {
//!     thread::sleep(Duration::from_secs(1));
//!     item.is_done.store(true, Ordering::SeqCst);
//!     drop(item);
//! });
//! let item: Box<MyItem> = done_rx.recv().unwrap();
//! assert!(item.is_done.load(Ordering::SeqCst));
//! ```

use crate::{Pointer, SmartPointer};
use alloc::boxed::Box;
use atomic_traits::{
    Atomic, NumOps,
    fetch::{Add, Sub},
};
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;
use core::sync::atomic::{
    Ordering::{Acquire, Relaxed, Release},
    fence,
};

/// trait for types that can be wrapped by [Irc]
///
/// # Safety
///
/// Tag is for distinguish multiple Irc from the same Inner type.
/// When implement multiple types of Irc from the same object,
/// you must make sure they don't have overlapped Counter fields.
pub unsafe trait IrcItem<Tag>: Sized + Send + Sync
where
    <Self::Counter as Atomic>::Type: From<u8> + Into<usize> + PartialEq,
{
    /// The type of counter
    type Counter: NumOps;

    /// return reference to the field of counter
    fn counter(&self) -> &Self::Counter;

    /// The default behavior for Irc is dropping the boxed inner.
    ///
    /// You can overwrite this if you want to send the inner somewhere.
    /// We pass box here to reduce moving cost.
    #[allow(clippy::boxed_local)]
    #[inline(always)]
    fn on_drop(_this: Box<Self>) {}

    #[inline]
    fn strong_count(&self) -> usize {
        self.counter().load(Relaxed).into()
    }
}

/// Intrusive reference counter, which support conversion bwteween `Box<T>`.
///
/// It does not support weak reference.
pub struct Irc<T: IrcItem<Tag>, Tag> {
    inner: NonNull<T>,
    _phan: PhantomData<fn(&Tag)>,
}

impl<T: IrcItem<Tag>, Tag> Irc<T, Tag> {
    /// Wrap a stack value T into Irc.
    ///
    /// The counter will be reset to 1 on initialization.
    #[inline]
    pub fn new(inner: T) -> Self {
        inner.counter().store(1u8.into(), Relaxed);
        Self {
            inner: unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(inner))) },
            _phan: Default::default(),
        }
    }

    #[inline(always)]
    fn get_inner(&self) -> &T {
        unsafe { self.inner.as_ref() }
    }

    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.inner == other.inner
    }

    /// If is_unique returns true, then this thread is the only owner
    ///
    /// # False negative
    ///
    /// it's possible to return false when counter drop to 1,
    /// Because of using Acquire load and Release on drop.
    ///
    /// # Example
    ///
    ///
    /// ```rust
    /// use embed_collections::irc::{Irc, IrcItem};
    /// use core::sync::atomic::AtomicUsize;
    ///
    /// struct Tag;
    ///
    /// struct MyItem {
    ///     value: i32,
    ///     counter: AtomicUsize,
    /// }
    ///
    /// unsafe impl IrcItem<Tag> for MyItem {
    ///     type Counter = AtomicUsize;
    ///     fn counter(&self) -> &Self::Counter {
    ///         &self.counter
    ///     }
    /// }
    ///
    /// // Create a new Irc
    /// let irc1 = Irc::<_, Tag>::new(MyItem { value: 10, counter: AtomicUsize::new(0) });
    /// assert_eq!(irc1.value, 10);
    /// assert!(irc1.is_unique());
    ///
    /// // Clone the Irc
    /// let irc2 = irc1.clone();
    /// assert_eq!(irc1.strong_count(), 2);
    /// assert!(!irc1.is_unique());
    #[inline]
    pub fn is_unique(&self) -> bool {
        // Safety:
        // we have make sure counter reset to 1 on init.
        // although clone use Relaxed, it can never pass this fence
        self.counter().load(Acquire) == 1u8.into()
    }

    /// return mutable reference if we are the only owner
    ///
    /// # False negative
    ///
    /// It can return None even when only one reference left
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.is_unique() { Some(unsafe { this.inner.as_mut() }) } else { None }
    }
}

impl<T: IrcItem<Tag> + Clone, Tag> Irc<T, Tag> {
    /// The Cow function, the same as `Arc::make_mut()`
    ///
    /// # Example
    ///
    /// ```rust
    /// use embed_collections::irc::{Irc, IrcItem};
    /// use core::sync::atomic::AtomicUsize;
    ///
    /// struct Tag;
    /// struct MyItem {
    ///     value: i32,
    ///     counter: AtomicUsize,
    /// }
    ///
    /// impl Clone for MyItem {
    ///     fn clone(&self) -> Self {
    ///         Self { value: self.value, counter: AtomicUsize::new(0) }
    ///     }
    /// }
    ///
    /// unsafe impl IrcItem<Tag> for MyItem {
    ///     type Counter = AtomicUsize;
    ///     fn counter(&self) -> &Self::Counter {
    ///         &self.counter
    ///     }
    /// }
    ///
    /// let mut irc1 = Irc::<_, Tag>::new(MyItem { value: 10, counter: AtomicUsize::new(0) });
    /// let irc2 = irc1.clone();
    ///
    /// // This will clone the inner item because it's shared
    /// let m = Irc::make_mut(&mut irc1);
    /// m.value = 20;
    ///
    /// assert_eq!(irc1.value, 20);
    /// assert_eq!(irc2.value, 10);
    /// ```
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        if !this.is_unique() {
            let cloned_item = this.get_inner().clone();
            let mut new_irc = Self::new(cloned_item);
            core::mem::swap(this, &mut new_irc);
        }
        unsafe { this.inner.as_mut() }
    }
}

impl<T: IrcItem<Tag>, Tag> Deref for Irc<T, Tag> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.get_inner()
    }
}

impl<T: IrcItem<Tag>, Tag> AsRef<T> for Irc<T, Tag> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.get_inner()
    }
}

unsafe impl<T: IrcItem<Tag>, Tag> Send for Irc<T, Tag> {}
unsafe impl<T: IrcItem<Tag>, Tag> Sync for Irc<T, Tag> {}

impl<T: IrcItem<Tag>, Tag> From<Box<T>> for Irc<T, Tag> {
    /// Convert a boxed T into Irc.
    ///
    /// The counter will be reset to 1 on initialization.
    #[inline]
    fn from(inner: Box<T>) -> Self {
        inner.counter().store(1u8.into(), Relaxed);
        Self {
            inner: unsafe { NonNull::new_unchecked(Box::into_raw(inner)) },
            _phan: Default::default(),
        }
    }
}

impl<T: IrcItem<Tag>, Tag> Clone for Irc<T, Tag> {
    #[inline]
    fn clone(&self) -> Self {
        self.get_inner().counter().fetch_add(1u8.into(), Relaxed);
        Self { inner: self.inner, _phan: Default::default() }
    }
}

impl<T: IrcItem<Tag>, Tag> Drop for Irc<T, Tag> {
    #[inline]
    fn drop(&mut self) {
        let p = self.inner.as_ptr();
        unsafe {
            if (*p).counter().fetch_sub(1u8.into(), Release) == 1u8.into() {
                fence(Acquire);
                let inner = Box::from_raw(p);
                IrcItem::<Tag>::on_drop(inner);
            }
        }
    }
}

impl<T: IrcItem<Tag> + fmt::Debug, Tag> fmt::Debug for Irc<T, Tag> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.get_inner().fmt(f)
    }
}

impl<T: IrcItem<Tag> + fmt::Display, Tag> fmt::Display for Irc<T, Tag> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.get_inner().fmt(f)
    }
}

impl<T: IrcItem<Tag>, Tag> Pointer for Irc<T, Tag> {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        unsafe { self.inner.as_ref() }
    }

    /// # Safety
    ///
    /// must be pointer acquire from [Irc::into_raw()]
    #[inline]
    unsafe fn from_raw(p: *const Self::Target) -> Self {
        Self {
            inner: unsafe { NonNull::new_unchecked(p as *mut Self::Target) },
            _phan: Default::default(),
        }
    }

    #[inline]
    fn into_raw(self) -> *const Self::Target {
        let p = self.inner.as_ptr();
        core::mem::forget(self);
        p
    }
}

impl<T: IrcItem<Tag>, Tag> SmartPointer for Irc<T, Tag> {
    #[inline]
    fn new(inner: T) -> Self {
        Irc::new(inner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::{CounterI32, alive_count, reset_alive_count};
    use core::sync::atomic::AtomicUsize;
    use std::thread;

    struct Tag;

    struct TestItem {
        value: CounterI32,
        counter: AtomicUsize,
    }

    impl TestItem {
        fn new(val: i32) -> Self {
            Self { value: CounterI32::new(val), counter: AtomicUsize::new(0) }
        }
    }

    impl Clone for TestItem {
        fn clone(&self) -> Self {
            Self { value: self.value.clone(), counter: AtomicUsize::new(0) }
        }
    }

    unsafe impl IrcItem<Tag> for TestItem {
        type Counter = AtomicUsize;
        fn counter(&self) -> &Self::Counter {
            &self.counter
        }
    }

    #[test]
    fn test_basic() {
        reset_alive_count();
        {
            let item = TestItem::new(10);
            let irc1 = Irc::<_, Tag>::new(item);
            assert_eq!(irc1.value.value, 10);
            assert_eq!(irc1.strong_count(), 1);
            assert!(irc1.is_unique());
            assert_eq!(alive_count(), 1);

            let irc2 = irc1.clone();
            assert_eq!(irc1.strong_count(), 2);
            assert_eq!(irc2.strong_count(), 2);
            assert!(!irc1.is_unique());
            assert_eq!(alive_count(), 1);

            drop(irc1);
            assert_eq!(irc2.strong_count(), 1);
            assert!(irc2.is_unique());
            assert_eq!(alive_count(), 1);
        }
        assert_eq!(alive_count(), 0);
    }

    #[test]
    fn test_get_mut() {
        reset_alive_count();
        let mut irc = Irc::<_, Tag>::new(TestItem::new(10));
        assert!(Irc::get_mut(&mut irc).is_some());

        let _irc2 = irc.clone();
        assert!(Irc::get_mut(&mut irc).is_none());
    }

    #[test]
    fn test_make_mut() {
        reset_alive_count();
        let mut irc = Irc::<_, Tag>::new(TestItem::new(10));

        // Unique, no clone
        {
            let m = Irc::make_mut(&mut irc);
            m.value.value = 20;
        }
        assert_eq!(irc.value.value, 20);
        assert_eq!(alive_count(), 1);

        // Not unique, should clone
        let irc2 = irc.clone();
        assert_eq!(alive_count(), 1);
        {
            let m = Irc::make_mut(&mut irc);
            m.value.value = 30;
        }
        assert_eq!(irc.value.value, 30);
        assert_eq!(irc2.value.value, 20);
        assert_eq!(alive_count(), 2);

        assert!(irc.is_unique());
        assert!(irc2.is_unique());
    }

    #[test]
    fn test_multithread_count() {
        reset_alive_count();
        {
            let irc = Irc::<_, Tag>::new(TestItem::new(0));
            let mut handles = vec![];

            for _ in 0..10 {
                let irc_clone = irc.clone();
                handles.push(thread::spawn(move || {
                    for _ in 0..1000 {
                        let temp = irc_clone.clone();
                        assert_eq!(temp.value.value, 0);
                    }
                }));
            }

            for handle in handles {
                handle.join().unwrap();
            }

            assert_eq!(irc.strong_count(), 1);
            assert!(irc.is_unique());
            assert_eq!(alive_count(), 1);
        }
        assert_eq!(alive_count(), 0);
    }

    #[test]
    fn test_multithread_drop() {
        reset_alive_count();
        {
            let irc = Irc::<_, Tag>::new(TestItem::new(0));
            let mut handles = vec![];
            for _ in 0..10 {
                let irc_clone = irc.clone();
                handles.push(thread::spawn(move || {
                    for _ in 0..1000 {
                        let temp = irc_clone.clone();
                        assert_eq!(temp.value.value, 0);
                    }
                }));
            }
            drop(irc);
            for handle in handles {
                handle.join().unwrap();
            }
        }
        assert_eq!(alive_count(), 0);
    }

    #[test]
    fn test_drop_all() {
        reset_alive_count();
        let irc = Irc::<_, Tag>::new(TestItem::new(0));
        let mut clones = vec![];
        for _ in 0..100 {
            clones.push(irc.clone());
        }
        assert_eq!(alive_count(), 1);
        drop(clones);
        assert_eq!(alive_count(), 1);
        drop(irc);
        assert_eq!(alive_count(), 0);
    }
}
