#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]

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
        unsafe { std::mem::transmute(*self) }
    }

    unsafe fn from_raw(p: *const Self::Target) -> Self {
        p as *const T
    }

    fn into_raw(self) -> *const Self::Target {
        self as *const T
    }
}

pub mod dlist;
