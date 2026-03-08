//! Segmented List - A segmented list with cache-friendly node sizes.
//!
//! Each segment is a singly linked list node containing dynamically calculated
//! number of elements based on cache line size and element size.

use alloc::alloc::{alloc, dealloc, handle_alloc_error};
use core::alloc::Layout;
use core::mem::{MaybeUninit, align_of, size_of};
use core::ptr::{NonNull, null_mut};

/// Cache line size in bytes
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm64ec",
    target_arch = "powerpc64",
))]
pub const CACHE_LINE_SIZE: usize = 128;
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm64ec",
    target_arch = "powerpc64",
)))]
pub const CACHE_LINE_SIZE: usize = 64;

/// Segmented list with cache-friendly segment sizes
///
/// Each segment's capacity is calculated at runtime based on T's size
/// to fit within a cache line.
///
pub struct SegList<T> {
    /// Pointer to the last segment (tail.get_header().next points to first element), to reduce the main struct size
    tail: NonNull<SegHeader<T>>,
    /// Total number of elements in the list
    count: usize,
}

unsafe impl<T: Send> Send for SegList<T> {}
unsafe impl<T: Send> Sync for SegList<T> {}

impl<T> SegList<T> {
    /// Create a new empty SegList with one allocated segment
    pub fn new() -> Self {
        let mut seg = unsafe { Segment::<T>::alloc(null_mut(), null_mut()) };
        let header_ptr = seg.header.as_ptr();
        let header = seg.get_header_mut();
        // Make it circular: tail.next points to head (itself for now)
        header.next = header_ptr;
        Self { tail: seg.header, count: 0 }
    }

    /// Returns true if the list is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Get the capacity of each segment
    #[inline(always)]
    pub const fn segment_cap() -> usize {
        Segment::<T>::LAYOUT_INFO.0
    }

    /// Returns the total number of elements in the list
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Push an element to the back of the list
    pub fn push(&mut self, item: T) {
        unsafe {
            let mut tail_seg = Segment::from_raw(self.tail);
            if tail_seg.is_full() {
                let tail_ptr = tail_seg.header.as_ptr();
                let cur = tail_seg.get_header_mut();
                let new_seg = Segment::alloc(tail_ptr, cur.next);
                cur.next = new_seg.header.as_ptr();
                self.tail = new_seg.header;
                tail_seg = new_seg;
            }
            tail_seg.push(item);
        }
        self.count += 1;
    }

    /// Pop an element from the back of the list
    pub fn pop(&mut self) -> Option<T> {
        if self.count == 0 {
            return None;
        }
        unsafe {
            let mut tail_seg = Segment::from_raw(self.tail);
            let (item, is_empty) = tail_seg.pop();
            if is_empty {
                let cur = tail_seg.get_header_mut();
                let first_ptr = cur.next;
                let cur_prev = cur.prev;
                if self.tail.as_ptr() != first_ptr && !cur_prev.is_null() {
                    // More than one segment: remove tail segment
                    self.tail = NonNull::new_unchecked(cur_prev);
                    (*self.tail.as_ptr()).next = first_ptr;
                    tail_seg.dealloc();
                }
                // If only one segment, keep it for future use
            }
            self.count -= 1;
            Some(item)
        }
    }

    // Break the cycle and free all segments
    #[inline]
    fn break_first_node(&mut self) -> Segment<T> {
        let tail_header = unsafe { self.tail.as_mut() };
        let first = tail_header.next;
        tail_header.next = null_mut();
        unsafe { Segment::from_raw(NonNull::new_unchecked(first)) }
    }

    /// Returns an iterator over the list
    pub fn iter(&self) -> SegListIter<'_, T> {
        let head = unsafe { self.tail.as_ref().next };
        let first_seg = if head.is_null() {
            None
        } else {
            Some(unsafe { Segment::from_raw(NonNull::new_unchecked(head)) })
        };
        SegListIter {
            cur: first_seg,
            cur_idx: 0,
            remaining: self.count,
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns a mutable iterator over the list
    pub fn iter_mut(&mut self) -> SegListIterMut<'_, T> {
        let head = unsafe { self.tail.as_ref().next };
        let first_seg = if head.is_null() {
            None
        } else {
            Some(unsafe { Segment::from_raw(NonNull::new_unchecked(head)) })
        };
        SegListIterMut {
            cur: first_seg,
            cur_idx: 0,
            remaining: self.count,
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns a draining iterator that consumes the list and yields elements from head to tail
    pub fn drain(mut self) -> SegListDrain<T> {
        // Break the cycle and get the first segment
        let first = self.break_first_node();
        // To prevent drop from being called
        core::mem::forget(self);

        SegListDrain { cur: Some(first), cur_idx: 0 }
    }

    /// Returns a reference to the first element in the list
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.iter().next()
    }

    /// Returns a reference to the last element in the list
    #[inline]
    pub fn last(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        // SAFETY: tail always points to a valid segment with at least one element
        unsafe {
            let header = self.tail.as_ref();
            let count = header.count;
            let items = (self.tail.as_ptr() as *mut u8).add(Segment::<T>::LAYOUT_INFO.1)
                as *mut MaybeUninit<T>;
            Some((*items.add(count - 1)).assume_init_ref())
        }
    }

    /// Returns a mutable reference to the last element in the list
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        if self.is_empty() {
            return None;
        }
        // SAFETY: tail always points to a valid segment with at least one element
        unsafe {
            let header = self.tail.as_mut();
            let count = header.count;
            let items = (self.tail.as_ptr() as *mut u8).add(Segment::<T>::LAYOUT_INFO.1)
                as *mut MaybeUninit<T>;
            Some((*items.add(count - 1)).assume_init_mut())
        }
    }

    /// Clear all elements from the list
    pub fn clear(&mut self) {
        while self.pop().is_some() {}
    }
}

impl<T> Default for SegList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for SegList<T> {
    fn drop(&mut self) {
        // Break the cycle and get the first segment
        let mut cur = self.break_first_node();
        loop {
            // Save next pointer before dealloc
            let next = cur.get_header().next;
            unsafe { cur.dealloc() };
            if next.is_null() {
                break;
            }
            cur = unsafe { Segment::from_raw(NonNull::new_unchecked(next)) };
        }
    }
}

impl<T> IntoIterator for SegList<T> {
    type Item = T;
    type IntoIter = SegListDrain<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.drain()
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for SegList<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SegList").field("len", &self.len()).finish()
    }
}

/// Segment header containing metadata
#[repr(C)]
struct SegHeader<T> {
    /// Count of valid elements in this segment
    count: usize,
    prev: *mut SegHeader<T>,
    /// Next segment in the list
    next: *mut SegHeader<T>,
}

/// A segment containing header and element storage
struct Segment<T> {
    /// Pointer to the header
    header: NonNull<SegHeader<T>>,
    /// Pointer to the element storage (right after header in memory)
    items: *mut MaybeUninit<T>,
}

impl<T> Segment<T> {
    // cap, data_offset, mem layout
    const LAYOUT_INFO: (usize, usize, Layout) = {
        let header_size = size_of::<SegHeader<T>>();
        let t_size = size_of::<T>();
        let t_align = align_of::<MaybeUninit<T>>();

        // Calculate first element's offset (considering T's alignment)
        let data_offset = (header_size + t_align - 1) & !(t_align - 1);
        let min_total_size = data_offset + if t_size == 0 { 1 } else { t_size };
        let alloc_size = (min_total_size + CACHE_LINE_SIZE - 1) & !(CACHE_LINE_SIZE - 1);

        let capacity = if t_size == 0 {
            64 // zero size obj
        } else {
            (alloc_size - data_offset) / t_size
        };
        // rust 1.57 support assert in const fn
        assert!(capacity >= 1);
        let final_align = if CACHE_LINE_SIZE > t_align { CACHE_LINE_SIZE } else { t_align };
        match Layout::from_size_align(alloc_size, final_align) {
            Ok(l) => (capacity, data_offset, l),
            Err(_) => panic!("Invalid layout"),
        }
    };

    const fn get_layout() -> Layout {
        Self::LAYOUT_INFO.2
    }

    /// Create a new empty segment with calculated capacity
    unsafe fn alloc(prev: *mut SegHeader<T>, next: *mut SegHeader<T>) -> Self {
        let layout = Self::get_layout();
        let ptr: *mut u8 = unsafe { alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }
        unsafe {
            let p = NonNull::new_unchecked(ptr as *mut SegHeader<T>);
            let header = p.as_ptr();
            // Initialize header
            (*header).count = 0;
            (*header).prev = prev;
            (*header).next = next;
            Self::from_raw(p)
        }
    }

    unsafe fn dealloc(&mut self) {
        if core::mem::needs_drop::<T>() {
            for i in 0..self.len() {
                unsafe {
                    (*self.item_ptr(i)).assume_init_drop();
                }
            }
        }
        // Deallocate the entire segment (header + items)
        unsafe {
            dealloc(self.header.as_ptr() as *mut u8, Self::LAYOUT_INFO.2);
        }
    }

    #[inline(always)]
    unsafe fn from_raw(header: NonNull<SegHeader<T>>) -> Self {
        let p = header.as_ptr() as *mut u8;
        let items = unsafe { p.add(Self::LAYOUT_INFO.1) as *mut MaybeUninit<T> };
        Self { header, items }
    }

    /// Get the count of valid elements in this segment
    #[inline(always)]
    fn len(&self) -> usize {
        unsafe { (*self.header.as_ptr()).count }
    }

    #[inline(always)]
    fn get_header(&self) -> &SegHeader<T> {
        unsafe { self.header.as_ref() }
    }

    #[inline(always)]
    fn get_header_mut(&mut self) -> &mut SegHeader<T> {
        unsafe { self.header.as_mut() }
    }

    /// Check if segment has no valid elements
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if segment is full
    #[inline(always)]
    fn is_full(&self) -> bool {
        self.len() >= Self::LAYOUT_INFO.0
    }

    /// Get pointer to item at index
    #[inline]
    fn item_ptr(&self, index: usize) -> *mut MaybeUninit<T> {
        unsafe { self.items.add(index) }
    }

    /// Push an element to this segment (if not full)
    #[inline]
    fn push(&mut self, item: T) {
        debug_assert!(!self.is_full());
        let idx = self.get_header().count;
        unsafe {
            (*self.item_ptr(idx)).write(item);
        }
        self.get_header_mut().count = idx + 1;
    }

    /// return (item, is_empty_now)
    #[inline]
    fn pop(&mut self) -> (T, bool) {
        debug_assert!(!self.is_empty());
        let idx = self.get_header().count - 1;
        let item = unsafe { self.item_ptr(idx).read().assume_init() };
        self.get_header_mut().count = idx;
        (item, idx == 0)
    }
}

/// Immutable iterator over SegList
pub struct SegListIter<'a, T> {
    cur: Option<Segment<T>>,
    cur_idx: usize,
    remaining: usize,
    _marker: core::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for SegListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let cur = self.cur.as_ref()?;
        let cur_header = cur.get_header();
        unsafe {
            if self.cur_idx >= cur_header.count {
                let next = cur_header.next;
                // In circular list, next is never null, but we use remaining to limit iteration
                self.cur = Some(Segment::from_raw(NonNull::new_unchecked(next)));
                self.cur_idx = 0;
                return self.next();
            }
            let item = (*cur.item_ptr(self.cur_idx)).assume_init_ref();
            self.cur_idx += 1;
            self.remaining -= 1;
            Some(item)
        }
    }
}

/// Mutable iterator over SegList
pub struct SegListIterMut<'a, T> {
    cur: Option<Segment<T>>,
    cur_idx: usize,
    remaining: usize,
    _marker: core::marker::PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for SegListIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let cur = self.cur.as_mut()?;
        let cur_header = cur.get_header();
        unsafe {
            if self.cur_idx >= cur_header.count {
                let next = cur_header.next;
                // In circular list, next is never null, but we use remaining to limit iteration
                self.cur = Some(Segment::from_raw(NonNull::new_unchecked(next)));
                self.cur_idx = 0;
                return self.next();
            }
            let item = (*cur.item_ptr(self.cur_idx)).assume_init_mut();
            self.cur_idx += 1;
            self.remaining -= 1;
            Some(item)
        }
    }
}

/// Draining iterator over SegList
/// Consumes elements from head to tail (FIFO order)
pub struct SegListDrain<T> {
    cur: Option<Segment<T>>,
    cur_idx: usize,
}

impl<T> Iterator for SegListDrain<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.cur.as_mut()?;
        unsafe {
            let cur_header = cur.get_header();
            // Skip empty segments
            if self.cur_idx >= cur_header.count {
                // Save next pointer before dealloc
                let next = cur_header.next;
                // Don't call Segment::dealloc because we have already yield item outside
                dealloc(cur.header.as_ptr() as *mut u8, Segment::<T>::LAYOUT_INFO.2);
                if next.is_null() {
                    self.cur = None;
                    return None;
                } else {
                    self.cur = Some(Segment::from_raw(NonNull::new_unchecked(next)));
                    self.cur_idx = 0;
                    return self.next();
                }
            }
            let item = cur.item_ptr(self.cur_idx).read().assume_init();
            self.cur_idx += 1;
            if self.cur_idx >= cur_header.count {
                // Save next pointer before dealloc
                let next = cur_header.next;
                // Don't call Segment::dealloc because we have already yield item outside
                dealloc(cur.header.as_ptr() as *mut u8, Segment::<T>::LAYOUT_INFO.2);
                if next.is_null() {
                    self.cur = None;
                } else {
                    self.cur = Some(Segment::from_raw(NonNull::new_unchecked(next)));
                    self.cur_idx = 0;
                }
            }
            Some(item)
        }
    }
}

impl<T> Drop for SegListDrain<T> {
    fn drop(&mut self) {
        let mut next: *mut SegHeader<T>;
        if let Some(mut cur) = self.cur.take() {
            unsafe {
                // Save next pointer before dealloc
                let header = cur.get_header();
                next = header.next;
                // Drop remaining elements in this segment (from current index to end)
                if core::mem::needs_drop::<T>() {
                    for i in self.cur_idx..header.count {
                        (*cur.item_ptr(i)).assume_init_drop();
                    }
                }
                dealloc(cur.header.as_ptr() as *mut u8, Segment::<T>::LAYOUT_INFO.2);
                while !next.is_null() {
                    cur = Segment::from_raw(NonNull::new_unchecked(next));
                    let header = cur.get_header();
                    next = header.next;
                    cur.dealloc();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicUsize, Ordering};

    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug)]
    struct DropTracker(i32);

    impl Drop for DropTracker {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn reset_drop_count() {
        DROP_COUNT.store(0, Ordering::SeqCst);
    }

    fn get_drop_count() -> usize {
        DROP_COUNT.load(Ordering::SeqCst)
    }

    #[test]
    fn test_multiple_segments() {
        let mut list: SegList<i32> = SegList::new();
        if CACHE_LINE_SIZE == 128 {
            assert_eq!(Segment::<i32>::LAYOUT_INFO.0, 26);
        }

        for i in 0..100 {
            list.push(i);
        }

        assert_eq!(list.len(), 100);

        for i in (0..100).rev() {
            assert_eq!(list.pop(), Some(i));
        }

        assert_eq!(list.pop(), None);
    }

    #[test]
    fn test_iter_single_segment() {
        // Test with small number of elements (single segment)
        let mut list: SegList<i32> = SegList::new();

        for i in 0..10 {
            list.push(i);
        }
        assert_eq!(list.first(), Some(&0));
        assert_eq!(list.last(), Some(&9));

        // Test immutable iterator
        let collected: Vec<i32> = list.iter().copied().collect();
        assert_eq!(collected, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);

        // Test mutable iterator - modify elements
        for item in list.iter_mut() {
            *item *= 2;
        }
        assert_eq!(list.first(), Some(&0));
        assert_eq!(list.last(), Some(&18));

        // Verify modification
        let collected: Vec<i32> = list.iter().copied().collect();
        assert_eq!(collected, vec![0, 2, 4, 6, 8, 10, 12, 14, 16, 18]);

        // Test pop() - should return elements in LIFO order
        for i in (0..10).rev() {
            assert_eq!(list.pop(), Some(i * 2));
        }
        assert_eq!(list.pop(), None);
        assert!(list.is_empty());
    }

    #[test]
    fn test_iter_multi_segment() {
        // Test with many elements (multiple segments)
        let mut list: SegList<i32> = SegList::new();

        for i in 0..200 {
            list.push(i * 10);
        }
        assert_eq!(list.first(), Some(&0));
        assert_eq!(list.last(), Some(&1990));

        // Test immutable iterator across multiple segments
        let collected: Vec<i32> = list.iter().copied().collect();
        let expected: Vec<i32> = (0..200).map(|i| i * 10).collect();
        assert_eq!(collected, expected);

        // Test mutable iterator - modify elements
        for item in list.iter_mut() {
            *item += 1;
        }
        assert_eq!(list.first(), Some(&1));
        assert_eq!(list.last(), Some(&1991));

        // Verify modification
        let collected: Vec<i32> = list.iter().copied().collect();
        let expected: Vec<i32> = (0..200).map(|i| i * 10 + 1).collect();
        assert_eq!(collected, expected);

        // Test pop() - should return elements in LIFO order across multiple segments
        for i in (0..200).rev() {
            assert_eq!(list.pop(), Some(i * 10 + 1));
        }
        assert_eq!(list.pop(), None);
        assert!(list.is_empty());
    }

    #[test]
    fn test_drain() {
        // Get capacity per segment for DropTracker (i32)
        let cap = Segment::<DropTracker>::LAYOUT_INFO.0;

        // Scenario 1: Single segment, drain completely
        {
            reset_drop_count();
            {
                let mut list: SegList<DropTracker> = SegList::new();
                // Push fewer elements than one segment capacity
                for i in 0..5 {
                    list.push(DropTracker(i));
                }
                assert!(list.len() < cap);

                // Drain all elements
                let drained: Vec<i32> = list.drain().map(|d| d.0).collect();
                assert_eq!(drained, vec![0, 1, 2, 3, 4]);
            }
            // All 5 elements should be dropped by drain
            assert_eq!(get_drop_count(), 5);
        }

        // Scenario 2: Three segments, drain first segment partially, then drop remaining
        {
            reset_drop_count();
            {
                let mut list: SegList<DropTracker> = SegList::new();
                // Push elements to create 3 segments (cap * 2 + 5 = more than 2 segments)
                let total = cap * 2 + 5;
                for i in 0..total {
                    list.push(DropTracker(i as i32));
                }

                // Drain only half of first segment
                let drain_count = cap / 2;
                let mut drain_iter = list.drain();
                for i in 0..drain_count {
                    assert_eq!(drain_iter.next().unwrap().0, i as i32);
                }
                // Drop the drain iterator early (remaining elements should be dropped)
                drop(drain_iter);
            }
            // All elements should be dropped (drained + remaining in list)
            assert_eq!(get_drop_count(), cap * 2 + 5);
        }

        // Scenario 3: Three segments, drain exactly first segment, then drop remaining
        {
            reset_drop_count();
            {
                let mut list: SegList<DropTracker> = SegList::new();
                // Push elements to create 3 segments
                let total = cap * 2 + 3;
                for i in 0..total {
                    list.push(DropTracker(i as i32));
                }

                // Drain exactly first segment
                let mut drain_iter = list.drain();
                for i in 0..cap {
                    assert_eq!(drain_iter.next().unwrap().0, i as i32);
                }
                // Drop the drain iterator early
                drop(drain_iter);
            }
            // All elements should be dropped
            assert_eq!(get_drop_count(), cap * 2 + 3);
        }
    }

    #[test]
    fn test_drop_single_segment() {
        reset_drop_count();
        {
            let mut list: SegList<DropTracker> = SegList::new();
            let cap = Segment::<DropTracker>::LAYOUT_INFO.0;

            // Push fewer elements than one segment capacity
            for i in 0..5 {
                list.push(DropTracker(i));
            }
            assert!(list.len() < cap);

            // list drops here, should drop all elements
        }

        assert_eq!(get_drop_count(), 5);
    }

    #[test]
    fn test_drop_multi_segment() {
        let cap = Segment::<DropTracker>::LAYOUT_INFO.0;
        reset_drop_count();
        {
            let mut list: SegList<DropTracker> = SegList::new();

            // Push elements to create multiple segments (3 segments)
            let total = cap * 2 + 10;
            for i in 0..total {
                list.push(DropTracker(i as i32));
            }
            // list drops here, should drop all elements across all segments
        }
        assert_eq!(get_drop_count(), cap * 2 + 10);
    }

    #[test]
    fn test_clear() {
        let mut list: SegList<i32> = SegList::new();

        for i in 0..50 {
            list.push(i);
        }

        list.clear();

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop(), None);
    }

    /// Large struct that takes significant space (64 bytes)
    /// This forces each segment to hold fewer elements, testing multi-segment behavior
    #[derive(Debug, Clone, Copy, PartialEq)]
    struct LargeStruct {
        data: [u64; 16], // 64 bytes
    }

    impl LargeStruct {
        fn new(val: u64) -> Self {
            Self { data: [val; 16] }
        }
    }

    #[test]
    fn test_size() {
        let layout = Segment::<LargeStruct>::LAYOUT_INFO;
        println!(
            "LargeStruct: cap {} offset {}, size {}, align {}",
            layout.0,
            layout.1,
            layout.2.size(),
            layout.2.align()
        );
        let layout = Segment::<u64>::LAYOUT_INFO;
        println!(
            "u64: cap {} offset {}, size {}, align {}",
            layout.0,
            layout.1,
            layout.2.size(),
            layout.2.align()
        );
        let layout = Segment::<u32>::LAYOUT_INFO;
        println!(
            "u32: cap {} offset {}, size {}, align {}",
            layout.0,
            layout.1,
            layout.2.size(),
            layout.2.align()
        );
        let layout = Segment::<u16>::LAYOUT_INFO;
        println!(
            "u16: cap {} offset {}, size {}, align {}",
            layout.0,
            layout.1,
            layout.2.size(),
            layout.2.align()
        );
    }

    #[test]
    fn test_large_type_push_pop() {
        let mut list: SegList<LargeStruct> = SegList::new();
        // Push elements - each segment can only hold a few due to large element size
        for i in 0..50 {
            list.push(LargeStruct::new(i));
        }
        assert_eq!(list.len(), 50);

        // Pop all elements - should work correctly across multiple segments
        for i in (0..50).rev() {
            let val = list.pop().unwrap();
            assert_eq!(val.data[0], i);
            assert_eq!(val.data[7], i);
        }
        assert!(list.is_empty());
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn test_large_type_iter() {
        let mut list: SegList<LargeStruct> = SegList::new();

        // Push elements
        for i in 0..30 {
            list.push(LargeStruct::new(i * 10));
        }

        // Test iterator
        let collected: Vec<u64> = list.iter().map(|s| s.data[0]).collect();
        let expected: Vec<u64> = (0..30).map(|i| i * 10).collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn test_large_type_iter_mut() {
        let mut list: SegList<LargeStruct> = SegList::new();

        // Push elements
        for i in 0..20 {
            list.push(LargeStruct::new(i));
        }

        // Modify through iterator
        for item in list.iter_mut() {
            item.data[0] *= 2;
        }

        // Verify modification
        let collected: Vec<u64> = list.iter().map(|s| s.data[0]).collect();
        let expected: Vec<u64> = (0..20).map(|i| i * 2).collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn test_large_type_drain() {
        let mut list: SegList<LargeStruct> = SegList::new();

        // Push elements
        for i in 0..40 {
            list.push(LargeStruct::new(i));
        }

        // Drain and verify FIFO order
        let drained: Vec<u64> = list.drain().map(|s| s.data[0]).collect();
        let expected: Vec<u64> = (0..40).collect();
        assert_eq!(drained, expected);
    }

    #[test]
    fn test_large_type_clear() {
        let mut list: SegList<LargeStruct> = SegList::new();

        // Push elements
        for i in 0..60 {
            list.push(LargeStruct::new(i));
        }
        assert_eq!(list.len(), 60);

        // Clear
        list.clear();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop(), None);
    }
}
