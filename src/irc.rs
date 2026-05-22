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
    /// You can overwrite this if you want to send the inner somewhere
    #[inline(always)]
    fn on_drop(_this: Box<Self>) {}

    #[inline]
    fn strong_count(&self) -> usize {
        self.counter().load(Relaxed).into()
    }
}

/// Intrusive reference counter, which support conversion bwteween `Box<T>`.
///
/// It does not support weak reference
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
