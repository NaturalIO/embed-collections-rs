//! Various - A small-list optimization container for efficient parameter passing.
//!
//! `Various<T>` optimizing for the common case of a single element (use Option initially).
//! It's storage can be seamless grow when more elements pushed, using [SegList](crate::seg_list),
//! more efficient for CPU cache-line (compared to LinkedList), and produce less memory fragment (compared to `Vec`).
//!
//! # NOTE:
//!
//! It does not support random access, only sequential read and write.
//!
//! # Example
//!
//! ```rust
//! use embed_collections::various::Various;
//!
//! // Create an empty Various
//! let mut values = Various::new();
//!
//! // Push a single element (no allocation)
//! values.push(42);
//! assert_eq!(values.len(), 1);
//! assert_eq!(values.first(), Some(&42));
//!
//! // Push more elements (transitions to SegList internally)
//! values.push(100);
//! values.push(200);
//! assert_eq!(values.len(), 3);
//!
//! // Iterate over elements
//! let sum: i32 = values.iter().sum();
//! assert_eq!(sum, 342);
//!
//! // Pop elements from the back
//! assert_eq!(values.pop(), Some(200));
//! assert_eq!(values.pop(), Some(100));
//! assert_eq!(values.pop(), Some(42));
//! assert_eq!(values.pop(), None);
//!
//! // Create from a single value
//! let single = Various::from("hello");
//! assert_eq!(single.first(), Some(&"hello"));
//!
//! // Efficient for function parameter passing
//! fn process_items(items: &Various<i32>) -> i32 {
//!     items.iter().sum()
//! }
//!
//! let items = Various::from(10);
//! assert_eq!(process_items(&items), 10);
//! ```

use crate::seg_list::SegList;
use core::fmt;

pub struct Various<T> {
    inner: VariousInner<T>,
}

enum VariousInner<T> {
    One(Option<T>),
    More(SegList<T>),
}

macro_rules! match_iter {
    ($self: expr, $iter_type: tt, $f: tt $($m: tt)*) =>{
        match $self.inner {
            VariousInner::One($($m)* s)=>$iter_type::One(s.$f()),
            VariousInner::More($($m)* s)=>$iter_type::More(s.$f()),
        }
    }
}

macro_rules! match_call {
    ($self: expr, $cls: tt, $call: tt) => {
        match $self {
            $cls::One(i) => i.$call(),
            $cls::More(i) => i.$call(),
        }
    };
}

impl<T> Default for Various<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Various<T> {
    #[inline]
    pub fn new() -> Self {
        Self { inner: VariousInner::One(None) }
    }

    #[inline]
    pub fn from(item: T) -> Self {
        Self { inner: VariousInner::One(Some(item)) }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match &self.inner {
            VariousInner::One(i) => i.is_none(),
            VariousInner::More(i) => i.is_empty(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match &self.inner {
            VariousInner::One(i) => {
                if i.is_none() {
                    0
                } else {
                    1
                }
            }
            VariousInner::More(i) => i.len(),
        }
    }

    /// push element to the tail
    #[inline]
    pub fn push(&mut self, new_item: T) {
        match self.inner {
            VariousInner::More(ref mut s) => {
                s.push(new_item);
            }
            VariousInner::One(ref mut s) => {
                if s.is_none() {
                    s.replace(new_item);
                } else {
                    let mut l = SegList::new();
                    l.push(s.take().unwrap());
                    l.push(new_item);
                    self.inner = VariousInner::More(l);
                }
            }
        }
    }

    /// pop element from the tail
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        match self.inner {
            VariousInner::More(ref mut s) => s.pop(),
            VariousInner::One(ref mut s) => s.take(),
        }
    }

    #[inline]
    pub fn iter<'a>(&'a self) -> VariousIter<'a, T> {
        match_iter!(self, VariousIter, iter ref)
    }

    pub fn iter_mut<'a>(&'a mut self) -> VariousIterMut<'a, T> {
        match_iter!(self, VariousIterMut, iter_mut ref mut)
    }

    #[inline]
    pub fn first(&self) -> Option<&T> {
        match self.inner {
            VariousInner::One(ref s) => s.as_ref(),
            VariousInner::More(ref s) => s.iter().next(),
        }
    }

    #[inline]
    pub fn last(&self) -> Option<&T> {
        match self.inner {
            VariousInner::More(ref s) => s.last(),
            VariousInner::One(ref s) => s.as_ref(),
        }
    }

    pub fn last_mut(&mut self) -> Option<&mut T> {
        match self.inner {
            VariousInner::More(ref mut s) => s.last_mut(),
            VariousInner::One(ref mut s) => s.as_mut(),
        }
    }

    #[inline]
    pub fn take(&mut self) -> Self {
        use core::mem;
        Various { inner: mem::replace(&mut self.inner, VariousInner::One(None)) }
    }
}

impl<T> IntoIterator for Various<T> {
    type Item = T;

    type IntoIter = VariousIntoIter<T>;

    fn into_iter(self) -> VariousIntoIter<T> {
        match_iter!(self, VariousIntoIter, into_iter)
    }
}

impl<'a, T> IntoIterator for &'a Various<T> {
    type Item = &'a T;

    type IntoIter = VariousIter<'a, T>;

    fn into_iter(self) -> VariousIter<'a, T> {
        match_iter!(self, VariousIter, iter ref)
    }
}

pub enum VariousIter<'a, T> {
    One(core::option::Iter<'a, T>),
    More(crate::seg_list::SegListIter<'a, T>),
}

impl<'a, T> core::iter::Iterator for VariousIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match_call!(self, VariousIter, next)
    }
}

pub enum VariousIterMut<'a, T> {
    One(core::option::IterMut<'a, T>),
    More(crate::seg_list::SegListIterMut<'a, T>),
}

impl<'a, T> core::iter::Iterator for VariousIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        match_call!(self, VariousIterMut, next)
    }
}

pub enum VariousIntoIter<T> {
    One(core::option::IntoIter<T>),
    More(crate::seg_list::SegListDrain<T>),
}

impl<T> core::iter::Iterator for VariousIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match_call!(self, VariousIntoIter, next)
    }
}

impl<T: fmt::Debug> fmt::Debug for Various<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.inner {
            VariousInner::One(s) => s.fmt(f),
            VariousInner::More(s) => s.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_one() {
        let mut s = Various::new();
        s.push(1);
        assert_eq!(s.len(), 1);
        for i in &s {
            assert_eq!(*i, 1);
        }
        assert_eq!(Some(1), s.pop());
        assert_eq!(s.len(), 0);
        if (&s).into_iter().next().is_some() {
            unreachable!();
        }
    }

    #[test]
    fn test_cap_0() {
        let mut s = Various::new();
        s.push(1);
        assert_eq!(s.len(), 1);
        for i in &s {
            assert_eq!(*i, 1);
        }
        s.push(2);
        s.push(3);
        assert_eq!(s.len(), 3);
        let mut total = 0;
        for i in &s {
            total += *i;
        }
        assert_eq!(total, 6);
        for i in s.iter_mut() {
            *i += 1;
        }
        let mut total = 0;
        for i in &s {
            total += *i;
        }
        assert_eq!(total, 9);
        assert_eq!(s.pop(), Some(4));
        let mut total = 0;
        for i in s {
            total += i;
        }
        assert_eq!(total, 5);
    }

    #[test]
    fn test_more() {
        let mut s = Various::new();
        s.push(1);
        s.push(2);
        s.push(3);
        assert_eq!(s.len(), 3);
        let mut total = 0;
        for i in &s {
            total += *i;
        }
        assert_eq!(total, 6);
        for i in s.iter_mut() {
            *i += 1;
        }
        let mut total = 0;
        for i in &s {
            total += *i;
        }
        assert_eq!(total, 9);
        assert_eq!(s.pop(), Some(4));
        let mut total = 0;
        for i in s {
            total += i;
        }
        assert_eq!(total, 5);
    }
}
