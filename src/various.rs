//! Various: A small-list optimization container for efficient parameter passing.
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
use core::iter::{ExactSizeIterator, Iterator};

pub struct Various<T> {
    inner: VariousInner<T>,
}

enum VariousInner<T> {
    One(Option<T>),
    More(SegList<T>),
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

    /// NOTE: when multiple element already in the list, it will swap out original list and push again.
    #[inline]
    pub fn prepend(&mut self, new_item: T) {
        if self.is_empty() {
            self.push(new_item);
        } else {
            let mut temp = Self { inner: VariousInner::More(SegList::new()) };
            core::mem::swap(self, &mut temp);
            self.push(new_item);
            for item in temp {
                self.push(item);
            }
        }
    }

    #[inline]
    pub fn iter(&self) -> VariousIter<'_, T> {
        let inner = match &self.inner {
            VariousInner::One(s) => VariousIterInner::One(s.iter()),
            VariousInner::More(s) => VariousIterInner::More(s.iter()),
        };
        VariousIter { inner }
    }

    pub fn iter_mut(&mut self) -> VariousIterMut<'_, T> {
        let inner = match &mut self.inner {
            VariousInner::One(s) => VariousIterMutInner::One(s.iter_mut()),
            VariousInner::More(s) => VariousIterMutInner::More(s.iter_mut()),
        };
        VariousIterMut { inner }
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

    /// Returns a reverse iterator over the elements
    #[inline]
    pub fn iter_rev(&self) -> VariousIter<'_, T> {
        let inner = match &self.inner {
            VariousInner::One(s) => VariousIterInner::One(s.iter()),
            VariousInner::More(s) => VariousIterInner::More(s.iter_rev()),
        };
        VariousIter { inner }
    }

    /// Returns a mutable reverse iterator over the elements
    #[inline]
    pub fn iter_mut_rev(&mut self) -> VariousIterMut<'_, T> {
        let inner = match &mut self.inner {
            VariousInner::One(s) => VariousIterMutInner::One(s.iter_mut()),
            VariousInner::More(s) => VariousIterMutInner::More(s.iter_mut_rev()),
        };
        VariousIterMut { inner }
    }

    /// Take the content out and leave and empty option inside, freeing inner memory
    #[inline]
    pub fn take(&mut self) -> Self {
        use core::mem;
        Various { inner: mem::replace(&mut self.inner, VariousInner::One(None)) }
    }

    /// Clear the content without freeing inner memory
    #[inline]
    pub fn clear(&mut self) {
        match &mut self.inner {
            VariousInner::One(inner) => {
                let _ = inner.take();
            }
            VariousInner::More(inner) => inner.clear(),
        }
    }
}

impl<T> IntoIterator for Various<T> {
    type Item = T;

    type IntoIter = VariousIntoIter<T>;

    fn into_iter(self) -> VariousIntoIter<T> {
        let inner = match self.inner {
            VariousInner::One(s) => VariousIntoIterInner::One(s.into_iter()),
            VariousInner::More(s) => VariousIntoIterInner::More(s.into_iter()),
        };
        VariousIntoIter { inner }
    }
}

impl<T> Various<T> {
    /// Returns a reverse consuming iterator
    #[inline]
    pub fn into_iter_rev(self) -> VariousIntoIter<T> {
        let inner = match self.inner {
            VariousInner::One(s) => VariousIntoIterInner::One(s.into_iter()),
            VariousInner::More(s) => VariousIntoIterInner::More(s.into_iter_rev()),
        };
        VariousIntoIter { inner }
    }
}

impl<'a, T> IntoIterator for &'a Various<T> {
    type Item = &'a T;
    type IntoIter = VariousIter<'a, T>;

    #[inline]
    fn into_iter(self) -> VariousIter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Various<T> {
    type Item = &'a mut T;
    type IntoIter = VariousIterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> VariousIterMut<'a, T> {
        self.iter_mut()
    }
}

pub struct VariousIter<'a, T> {
    inner: VariousIterInner<'a, T>,
}

enum VariousIterInner<'a, T> {
    One(core::option::Iter<'a, T>),
    More(crate::seg_list::SegListIter<'a, T>),
}

impl<'a, T> Iterator for VariousIter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            VariousIterInner::One(i) => i.next(),
            VariousIterInner::More(i) => i.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = match &self.inner {
            VariousIterInner::One(i) => i.len(),
            VariousIterInner::More(i) => i.len(),
        };
        (l, Some(l))
    }
}

impl<'a, T> ExactSizeIterator for VariousIter<'a, T> {}

pub struct VariousIterMut<'a, T> {
    inner: VariousIterMutInner<'a, T>,
}

enum VariousIterMutInner<'a, T> {
    One(core::option::IterMut<'a, T>),
    More(crate::seg_list::SegListIterMut<'a, T>),
}

impl<'a, T> Iterator for VariousIterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            VariousIterMutInner::One(i) => i.next(),
            VariousIterMutInner::More(i) => i.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = match &self.inner {
            VariousIterMutInner::One(i) => i.len(),
            VariousIterMutInner::More(i) => i.len(),
        };
        (l, Some(l))
    }
}

impl<'a, T> ExactSizeIterator for VariousIterMut<'a, T> {}

pub struct VariousIntoIter<T> {
    inner: VariousIntoIterInner<T>,
}

enum VariousIntoIterInner<T> {
    One(core::option::IntoIter<T>),
    More(crate::seg_list::SegListIntoIter<T>),
}

impl<T> Iterator for VariousIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            VariousIntoIterInner::One(i) => i.next(),
            VariousIntoIterInner::More(i) => i.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = match &self.inner {
            VariousIntoIterInner::One(i) => i.len(),
            VariousIntoIterInner::More(i) => i.len(),
        };
        (l, Some(l))
    }
}

impl<T> ExactSizeIterator for VariousIntoIter<T> {}

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
    fn test_multiple() {
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
    fn test_prepend() {
        let mut s = Various::<i32>::new();
        s.prepend(1);
        assert_eq!(s.len(), 1);
        for i in &s {
            assert_eq!(*i, 1);
        }
        s.prepend(2);
        assert_eq!(s.len(), 2);
        let mut iter = s.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        s.prepend(3);
        assert_eq!(s.len(), 3);
        let mut iter = s.iter();
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        let collected: Vec<i32> = s.into_iter().collect();
        assert_eq!(collected, vec![3, 2, 1]);
    }

    #[test]
    fn test_iter_rev_one() {
        // Test reverse iterator with single element
        let mut s = Various::new();
        s.push(42);

        let collected: Vec<i32> = s.iter_rev().copied().collect();
        assert_eq!(collected, vec![42]);

        // Test mutable reverse iterator
        for i in s.iter_mut_rev() {
            *i *= 10;
        }
        assert_eq!(s.first(), Some(&420));
    }

    #[test]
    fn test_iter_rev_more() {
        // Test reverse iterator with multiple elements
        let mut s = Various::new();
        s.push(1);
        s.push(2);
        s.push(3);
        let iter = s.iter_rev();
        assert_eq!(iter.len(), 3);
        let collected: Vec<i32> = iter.copied().collect();
        assert_eq!(collected, vec![3, 2, 1]);

        // Test mutable reverse iterator
        for i in s.iter_mut_rev() {
            *i *= 10;
        }
        let collected: Vec<i32> = s.iter().copied().collect();
        assert_eq!(collected, vec![10, 20, 30]);
    }

    #[test]
    fn test_iter_rev_empty() {
        // Test reverse iterator with empty Various
        let s: Various<i32> = Various::new();
        let iter = s.iter_rev();
        assert_eq!(iter.len(), 0);
        let collected: Vec<i32> = iter.copied().collect();
        assert!(collected.is_empty());

        let mut s_mut: Various<i32> = Various::new();
        let count = s_mut.iter_mut_rev().count();
        assert_eq!(count, 0);
    }

    #[test]
    fn test_into_rev_one() {
        // Test reverse consuming iterator with single element
        let mut s = Various::new();
        s.push(42);
        let iter = s.into_iter_rev();
        assert_eq!(iter.len(), 1);
        let collected: Vec<i32> = iter.collect();
        assert_eq!(collected, vec![42]);
    }

    #[test]
    fn test_into_rev_more() {
        // Test reverse consuming iterator with multiple elements
        let mut s = Various::new();
        s.push(1);
        s.push(2);
        s.push(3);
        let iter = s.into_iter_rev();
        assert_eq!(iter.len(), 3);
        let collected: Vec<i32> = iter.collect();
        assert_eq!(collected, vec![3, 2, 1]);
    }

    #[test]
    fn test_into_rev_empty() {
        // Test reverse consuming iterator with empty Various
        let s: Various<i32> = Various::new();
        let iter = s.into_iter_rev();
        assert_eq!(iter.len(), 0);
        let collected: Vec<i32> = iter.collect();
        assert!(collected.is_empty());
    }
}
