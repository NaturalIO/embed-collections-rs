#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![doc = include_str!("../README.md")]

use std::mem;
use std::ptr::NonNull;

/// Abstract pointer trait to support various pointer types in collections.
///
/// This trait allows the collections to work with:
/// - `Box<T>`: Owned, automatically dropped.
/// - `Arc<T>`: Shared ownership.
/// - `Rc<T>`: Single thread ownership.
/// - `NonNull<T>`: Raw non-null pointers (manual memory management).
/// - `*const T`: Raw pointers (recommend to use `NonNull<T>` instead)
pub trait Pointer: Sized {
    type Target;

    fn as_ref(&self) -> &Self::Target;

    unsafe fn from_raw(p: *const Self::Target) -> Self;

    fn into_raw(self) -> *const Self::Target;
}

impl<T> Pointer for *const T {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        unsafe { mem::transmute(*self) }
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        p as *const T
    }

    fn into_raw(self) -> *const Self::Target {
        self as *const T
    }
}

impl<T> Pointer for NonNull<T> {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        unsafe { self.as_ref() }
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        unsafe { NonNull::new_unchecked(p as *mut T) }
    }

    fn into_raw(self) -> *const Self::Target {
        self.as_ptr()
    }
}

impl<T> Pointer for Box<T> {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        &**self
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        unsafe { Box::from_raw(p as *mut T) }
    }

    fn into_raw(self) -> *const Self::Target {
        Box::into_raw(self)
    }
}

impl<T> Pointer for std::rc::Rc<T> {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        &**self
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        unsafe { std::rc::Rc::from_raw(p) }
    }

    fn into_raw(self) -> *const Self::Target {
        std::rc::Rc::into_raw(self)
    }
}

impl<T> Pointer for std::sync::Arc<T> {
    type Target = T;

    #[inline]
    fn as_ref(&self) -> &Self::Target {
        &**self
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        unsafe { std::sync::Arc::from_raw(p) }
    }

    fn into_raw(self) -> *const Self::Target {
        std::sync::Arc::into_raw(self)
    }
}

#[cfg(feature = "dlist")]
pub mod dlist;
#[cfg(feature = "slist")]
pub mod slist;
