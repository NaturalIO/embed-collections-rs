//! A fixed-size vector with const generic capacity.
//!
//! This module provides `ConstVec`, a vector with a fixed capacity determined at compile time
//! via const generics. It provides O(1) push and pop operations, but returns errors when the
//! capacity is exceeded instead of reallocating.
//!
//! # Features
//! - Fixed capacity determined at compile time
//! - O(1) push and pop operations
//! - No heap allocation after initial creation
//!
//! # Example
//! ```rust
//! use embed_collections::const_vec::ConstVec;
//!
//! let mut vec: ConstVec<i32, 3> = ConstVec::new();
//!
//! assert!(vec.push(1).is_ok());
//! assert!(vec.push(2).is_ok());
//! assert!(vec.push(3).is_ok());
//!
//! // Capacity is full, next push returns Err
//! assert!(vec.push(4).is_err());
//!
//! assert_eq!(vec.len(), 3);
//! assert_eq!(vec.capacity(), 3);
//! ```

use core::fmt;
use core::mem::MaybeUninit;

/// A fixed-size vector with const generic capacity.
///
/// The capacity is determined at compile time via the const generic parameter `N`.
/// When the vector is full, push operations return `Err(item)` instead of reallocating.
pub struct ConstVec<T, const N: usize> {
    // Storage for elements, using MaybeUninit to handle uninitialized memory
    data: [MaybeUninit<T>; N],
    // Current number of elements in the vector
    len: usize,
}

impl<T, const N: usize> ConstVec<T, N> {
    /// Creates a new empty `ConstVec`.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let vec: ConstVec<i32, 5> = ConstVec::new();
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.capacity(), 5);
    /// ```
    #[inline(always)]
    pub fn new() -> Self {
        // Create an array of uninitialized values using from_fn
        // This is safe because MaybeUninit<T> can hold uninitialized data
        let data = core::array::from_fn(|_| MaybeUninit::uninit());

        Self { data, len: 0 }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// assert_eq!(vec.len(), 0);
    ///
    /// vec.push(1).unwrap();
    /// assert_eq!(vec.len(), 1);
    /// ```
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// assert!(vec.is_empty());
    ///
    /// vec.push(1).unwrap();
    /// assert!(!vec.is_empty());
    /// ```
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the capacity of the vector.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let vec: ConstVec<i32, 5> = ConstVec::new();
    /// assert_eq!(vec.capacity(), 5);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns `true` if the vector is at full capacity.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 2> = ConstVec::new();
    /// assert!(!vec.is_full());
    ///
    /// vec.push(1).unwrap();
    /// vec.push(2).unwrap();
    /// assert!(vec.is_full());
    /// ```
    #[inline(always)]
    pub const fn is_full(&self) -> bool {
        self.len == N
    }

    /// Appends an element to the back of the vector.
    ///
    /// Returns `Ok(())` if the element was successfully added, or `Err(item)`
    /// if the vector is at full capacity.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 2> = ConstVec::new();
    ///
    /// assert!(vec.push(1).is_ok());
    /// assert!(vec.push(2).is_ok());
    /// assert!(vec.push(3).is_err()); // Capacity exceeded
    ///
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline]
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.len < N {
            // Safe because we're writing to an uninitialized slot and we've checked the bounds
            self.data[self.len] = MaybeUninit::new(item);
            self.len += 1;
            Ok(())
        } else {
            Err(item)
        }
    }

    /// Removes and returns the last element from the vector.
    ///
    /// Returns `Some(item)` if the vector is not empty, or `None` if it is empty.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(1).unwrap();
    /// vec.push(2).unwrap();
    ///
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len > 0 {
            self.len -= 1;
            // Safe because we've checked that len > 0, so this slot is initialized
            let item = unsafe { self.data[self.len].assume_init_read() };
            Some(item)
        } else {
            None
        }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(10).unwrap();
    /// vec.push(20).unwrap();
    ///
    /// assert_eq!(vec.get(0), Some(&10));
    /// assert_eq!(vec.get(1), Some(&20));
    /// assert_eq!(vec.get(2), None);
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            // Safe because we've checked the bounds and we only initialize up to len
            Some(unsafe { self.data[index].assume_init_ref() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(10).unwrap();
    ///
    /// if let Some(elem) = vec.get_mut(0) {
    ///     *elem = 30;
    /// }
    ///
    /// assert_eq!(vec.get(0), Some(&30));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            // Safe because we've checked the bounds and we only initialize up to len
            Some(unsafe { self.data[index].assume_init_mut() })
        } else {
            None
        }
    }

    /// Inserts an element at the specified index.
    ///
    /// If the index is greater than the length, returns `None`.
    ///
    /// If the vector is not full, the element is inserted and all elements
    /// from the index onward are shifted right by one, and `None` is returned.
    ///
    /// If the vector is full, the element is inserted, all elements from the
    /// index onward are shifted right by one, the last element is removed and
    /// returned in `Some`.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 4> = ConstVec::new();
    /// vec.push(1).expect("push failed");
    /// vec.push(2).expect("push failed");
    /// vec.push(3).expect("push failed");
    ///
    /// // Insert at index 1 (not full)
    /// assert_eq!(vec.insert(1, 10), None);
    /// assert_eq!(vec.get(0), Some(&1));
    /// assert_eq!(vec.get(1), Some(&10));
    /// assert_eq!(vec.get(2), Some(&2));
    /// assert_eq!(vec.get(3), Some(&3));
    ///
    /// // Insert when full - removes last element
    /// let removed = vec.insert(2, 20);
    /// assert_eq!(removed, Some(3));
    /// assert_eq!(vec.get(0), Some(&1));
    /// assert_eq!(vec.get(1), Some(&10));
    /// assert_eq!(vec.get(2), Some(&20));
    /// assert_eq!(vec.get(3), Some(&2));
    /// ```
    #[inline]
    pub fn insert(&mut self, index: usize, item: T) -> Option<T> {
        if index > self.len {
            // Invalid index
            return None;
        }

        if self.len < N {
            // Not full, shift elements to the right
            // Start from the end and move backwards
            for i in (index..self.len).rev() {
                unsafe {
                    let src = self.data[i].as_ptr();
                    let dst = self.data[i + 1].as_mut_ptr();
                    core::ptr::copy_nonoverlapping(src, dst, 1);
                }
            }
            // Insert the new element
            self.data[index] = MaybeUninit::new(item);
            self.len += 1;
            None
        } else {
            // Full, need to remove the last element
            // Save the last element to return
            let last_item = unsafe { self.data[N - 1].assume_init_read() };

            // Shift elements from index to N-2 to the right
            for i in (index..N - 1).rev() {
                unsafe {
                    let src = self.data[i].as_ptr();
                    let dst = self.data[i + 1].as_mut_ptr();
                    core::ptr::copy_nonoverlapping(src, dst, 1);
                }
            }

            // Insert the new element
            self.data[index] = MaybeUninit::new(item);

            Some(last_item)
        }
    }

    /// Returns an iterator over the elements of the vector.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(1).expect("push failed");
    /// vec.push(2).expect("push failed");
    /// vec.push(3).expect("push failed");
    ///
    /// let mut iter = vec.iter();
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T, N> {
        Iter { vec: self, pos: 0 }
    }

    /// Returns a mutable iterator over the elements of the vector.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(1).expect("push failed");
    /// vec.push(2).expect("push failed");
    /// vec.push(3).expect("push failed");
    ///
    /// for elem in vec.iter_mut() {
    ///     *elem *= 2;
    /// }
    ///
    /// assert_eq!(vec.get(0), Some(&2));
    /// assert_eq!(vec.get(1), Some(&4));
    /// assert_eq!(vec.get(2), Some(&6));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, N> {
        IterMut { vec: self, pos: 0 }
    }
}

/// An iterator over the elements of a `ConstVec`.
pub struct Iter<'a, T, const N: usize> {
    vec: &'a ConstVec<T, N>,
    pos: usize,
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.vec.len {
            let item = unsafe { self.vec.data[self.pos].assume_init_ref() };
            self.pos += 1;
            Some(item)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vec.len - self.pos;
        (remaining, Some(remaining))
    }
}

impl<'a, T, const N: usize> ExactSizeIterator for Iter<'a, T, N> {}

/// A mutable iterator over the elements of a `ConstVec`.
pub struct IterMut<'a, T, const N: usize> {
    vec: &'a mut ConstVec<T, N>,
    pos: usize,
}

impl<'a, T, const N: usize> Iterator for IterMut<'a, T, N> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.vec.len {
            // Safe because we checked bounds and the data is initialized
            let item = unsafe {
                let item = self.vec.data[self.pos].assume_init_mut();
                // Convert the lifetime from &mut self to 'a
                core::mem::transmute::<&mut T, &'a mut T>(item)
            };
            self.pos += 1;
            Some(item)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vec.len - self.pos;
        (remaining, Some(remaining))
    }
}

impl<'a, T, const N: usize> ExactSizeIterator for IterMut<'a, T, N> {}

impl<T, const N: usize> Drop for ConstVec<T, N> {
    fn drop(&mut self) {
        // Drop all initialized elements
        for i in 0..self.len {
            unsafe {
                self.data[i].assume_init_drop();
            }
        }
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for ConstVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConstVec")
            .field("len", &self.len)
            .field("capacity", &N)
            .field("data", &&self.data[..self.len])
            .finish()
    }
}

impl<T: Clone, const N: usize> Clone for ConstVec<T, N> {
    fn clone(&self) -> Self {
        let mut new_vec = Self::new();
        for i in 0..self.len {
            // Safe because we know these elements are initialized
            let item = unsafe { self.data[i].assume_init_ref() };
            // We know new_vec has enough capacity because N is the same
            // This should never fail, but we use match to avoid Debug requirement
            match new_vec.push(item.clone()) {
                Ok(()) => {}
                Err(_) => panic!("ConstVec clone failed: capacity exceeded"),
            }
        }
        new_vec
    }
}

impl<T: PartialEq, const N: usize> PartialEq for ConstVec<T, N> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            // Safe because we know these elements are initialized
            let a = unsafe { self.data[i].assume_init_ref() };
            let b = unsafe { other.data[i].assume_init_ref() };
            if a != b {
                return false;
            }
        }
        true
    }
}

impl<T: Eq, const N: usize> Eq for ConstVec<T, N> {}

impl<T, const N: usize> Default for ConstVec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> core::ops::Index<usize> for ConstVec<T, N> {
    type Output = T;

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(10).expect("push failed");
    /// vec.push(20).expect("push failed");
    ///
    /// assert_eq!(vec[0], 10);
    /// assert_eq!(vec[1], 20);
    /// ```
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

impl<T, const N: usize> core::ops::IndexMut<usize> for ConstVec<T, N> {
    /// Returns a mutable reference to the element at the given index.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    /// ```rust
    /// use embed_collections::const_vec::ConstVec;
    ///
    /// let mut vec: ConstVec<i32, 5> = ConstVec::new();
    /// vec.push(10).expect("push failed");
    /// vec.push(20).expect("push failed");
    ///
    /// vec[0] = 30;
    /// assert_eq!(vec[0], 30);
    /// ```
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("index out of bounds")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let vec: ConstVec<i32, 5> = ConstVec::new();
        assert!(vec.is_empty());
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 5);
        assert!(!vec.is_full());
    }

    #[test]
    fn test_push_pop() {
        let mut vec: ConstVec<i32, 3> = ConstVec::new();

        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert!(vec.push(3).is_ok());
        assert!(vec.is_full());
        assert_eq!(vec.len(), 3);

        // Try to push when full
        assert_eq!(vec.push(4), Err(4));
        assert_eq!(vec.len(), 3);

        // Pop elements
        assert_eq!(vec.pop(), Some(3));
        assert_eq!(vec.pop(), Some(2));
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.pop(), None);
        assert!(vec.is_empty());

        // Can push again after popping
        assert!(vec.push(10).is_ok());
        assert_eq!(vec.pop(), Some(10));
    }

    #[test]
    fn test_get() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();

        vec.push(10).expect("push failed");
        vec.push(20).expect("push failed");
        vec.push(30).expect("push failed");

        assert_eq!(vec.get(0), Some(&10));
        assert_eq!(vec.get(1), Some(&20));
        assert_eq!(vec.get(2), Some(&30));
        assert_eq!(vec.get(3), None);
        assert_eq!(vec.get(100), None);
    }

    #[test]
    fn test_get_mut() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();

        vec.push(10).expect("push failed");
        vec.push(20).expect("push failed");

        if let Some(elem) = vec.get_mut(0) {
            *elem = 100;
        }

        assert_eq!(vec.get(0), Some(&100));
        assert_eq!(vec.get(1), Some(&20));
    }

    #[test]
    fn test_is_full() {
        let mut vec: ConstVec<i32, 2> = ConstVec::new();

        assert!(!vec.is_full());
        vec.push(1).expect("push failed");
        assert!(!vec.is_full());
        vec.push(2).expect("push failed");
        assert!(vec.is_full());

        vec.pop();
        assert!(!vec.is_full());
    }

    #[test]
    fn test_clone() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");

        let cloned = vec.clone();
        assert_eq!(cloned.len(), 3);
        assert_eq!(cloned.get(0), Some(&1));
        assert_eq!(cloned.get(1), Some(&2));
        assert_eq!(cloned.get(2), Some(&3));
    }

    #[test]
    fn test_eq() {
        let mut vec1: ConstVec<i32, 5> = ConstVec::new();
        vec1.push(1).expect("push failed");
        vec1.push(2).expect("push failed");

        let mut vec2: ConstVec<i32, 5> = ConstVec::new();
        vec2.push(1).expect("push failed");
        vec2.push(2).expect("push failed");

        let mut vec3: ConstVec<i32, 5> = ConstVec::new();
        vec3.push(1).expect("push failed");
        vec3.push(3).expect("push failed");

        assert_eq!(vec1, vec2);
        assert_ne!(vec1, vec3);
    }

    #[test]
    fn test_debug() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");

        let debug_str = format!("{:?}", vec);
        assert!(debug_str.contains("ConstVec"));
        assert!(debug_str.contains("len"));
        assert!(debug_str.contains("capacity"));
    }

    #[test]
    fn test_default() {
        let vec: ConstVec<i32, 5> = ConstVec::default();
        assert!(vec.is_empty());
        assert_eq!(vec.capacity(), 5);
    }

    #[test]
    fn test_drop() {
        use std::cell::Cell;

        #[derive(Debug)]
        struct DropCounter<'a> {
            count: &'a Cell<i32>,
        }

        impl<'a> Drop for DropCounter<'a> {
            fn drop(&mut self) {
                self.count.set(self.count.get() + 1);
            }
        }

        let count = Cell::new(0);
        {
            let mut vec: ConstVec<DropCounter, 3> = ConstVec::new();
            vec.push(DropCounter { count: &count }).expect("push failed");
            vec.push(DropCounter { count: &count }).expect("push failed");
            vec.push(DropCounter { count: &count }).expect("push failed");
            assert_eq!(count.get(), 0);
        }
        assert_eq!(count.get(), 3);
    }

    #[test]
    fn test_insert_not_full() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");

        // Insert at index 1, not full
        assert_eq!(vec.insert(1, 10), None);
        assert_eq!(vec.len(), 4);
        assert_eq!(vec.get(0), Some(&1));
        assert_eq!(vec.get(1), Some(&10));
        assert_eq!(vec.get(2), Some(&2));
        assert_eq!(vec.get(3), Some(&3));
        assert_eq!(vec.get(4), None);

        // Insert at beginning
        assert_eq!(vec.insert(0, 20), None);
        assert_eq!(vec.len(), 5);
        assert_eq!(vec.get(0), Some(&20));
        assert_eq!(vec.get(1), Some(&1));
        assert_eq!(vec.get(2), Some(&10));
        assert_eq!(vec.get(3), Some(&2));
        assert_eq!(vec.get(4), Some(&3));
        assert!(vec.is_full());
    }

    #[test]
    fn test_insert_full() {
        let mut vec: ConstVec<i32, 4> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");
        vec.push(4).expect("push failed");
        assert!(vec.is_full());

        // Insert at index 1 when full, should remove last element (4)
        let removed = vec.insert(1, 10);
        assert_eq!(removed, Some(4));
        assert_eq!(vec.len(), 4); // Still full
        assert_eq!(vec.get(0), Some(&1));
        assert_eq!(vec.get(1), Some(&10));
        assert_eq!(vec.get(2), Some(&2));
        assert_eq!(vec.get(3), Some(&3));

        // Insert at beginning when full, should remove last element (3)
        let removed = vec.insert(0, 20);
        assert_eq!(removed, Some(3));
        assert_eq!(vec.len(), 4);
        assert_eq!(vec.get(0), Some(&20));
        assert_eq!(vec.get(1), Some(&1));
        assert_eq!(vec.get(2), Some(&10));
        assert_eq!(vec.get(3), Some(&2));
    }

    #[test]
    fn test_insert_at_end() {
        let mut vec: ConstVec<i32, 4> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");

        // Insert at end (index == len)
        assert_eq!(vec.insert(2, 10), None);
        assert_eq!(vec.len(), 3);
        assert_eq!(vec.get(0), Some(&1));
        assert_eq!(vec.get(1), Some(&2));
        assert_eq!(vec.get(2), Some(&10));
    }

    #[test]
    fn test_insert_invalid_index() {
        let mut vec: ConstVec<i32, 4> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");

        // Insert at invalid index (greater than len)
        assert_eq!(vec.insert(5, 10), None);
        assert_eq!(vec.len(), 2); // Unchanged
        assert_eq!(vec.get(0), Some(&1));
        assert_eq!(vec.get(1), Some(&2));
    }

    #[test]
    fn test_insert_empty() {
        let mut vec: ConstVec<i32, 4> = ConstVec::new();

        // Insert into empty vector
        assert_eq!(vec.insert(0, 10), None);
        assert_eq!(vec.len(), 1);
        assert_eq!(vec.get(0), Some(&10));
    }

    #[test]
    fn test_iter() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");

        let mut iter = vec.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);

        // Check size_hint
        let mut iter2 = vec.iter();
        assert_eq!(iter2.size_hint(), (3, Some(3)));
        iter2.next();
        assert_eq!(iter2.size_hint(), (2, Some(2)));
    }

    #[test]
    fn test_iter_mut() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");

        // Double each element
        for elem in vec.iter_mut() {
            *elem *= 2;
        }

        assert_eq!(vec.get(0), Some(&2));
        assert_eq!(vec.get(1), Some(&4));
        assert_eq!(vec.get(2), Some(&6));

        // Check iterator works correctly
        let mut iter = vec.iter_mut();
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 4));
        assert_eq!(iter.next(), Some(&mut 6));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_index() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(10).expect("push failed");
        vec.push(20).expect("push failed");
        vec.push(30).expect("push failed");

        assert_eq!(vec[0], 10);
        assert_eq!(vec[1], 20);
        assert_eq!(vec[2], 30);

        // Test with a function that uses indexing
        fn get_element(vec: &ConstVec<i32, 5>, index: usize) -> i32 {
            vec[index]
        }

        assert_eq!(get_element(&vec, 1), 20);
    }

    #[test]
    fn test_index_mut() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(10).expect("push failed");
        vec.push(20).expect("push failed");

        vec[0] = 100;
        vec[1] = 200;

        assert_eq!(vec[0], 100);
        assert_eq!(vec[1], 200);

        // Test with a function that uses mutable indexing
        fn double_first(vec: &mut ConstVec<i32, 5>) {
            vec[0] *= 2;
        }

        double_first(&mut vec);
        assert_eq!(vec[0], 200);
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_out_of_bounds() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(10).expect("push failed");

        let _ = vec[5]; // Should panic
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_mut_out_of_bounds() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(10).expect("push failed");

        vec[5] = 20; // Should panic
    }

    #[test]
    fn test_empty_iter() {
        let vec: ConstVec<i32, 5> = ConstVec::new();
        let mut iter = vec.iter();

        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_iter_exact_size() {
        let mut vec: ConstVec<i32, 5> = ConstVec::new();
        vec.push(1).expect("push failed");
        vec.push(2).expect("push failed");
        vec.push(3).expect("push failed");

        let iter = vec.iter();
        assert_eq!(iter.len(), 3); // ExactSizeIterator provides len()

        let iter_mut = vec.iter_mut();
        assert_eq!(iter_mut.len(), 3);
    }
}
