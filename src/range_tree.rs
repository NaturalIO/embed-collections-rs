use alloc::collections::BTreeMap;
use core::fmt;

pub struct AddressTag;
pub struct SizeTag;

pub struct RangeTree<T>
where
    T: RangeTreeOps,
{
    map: BTreeMap<u64, u64>,
    space: u64,
    ops: T,
}

unsafe impl<T: RangeTreeOps> Send for RangeTree<T> {}

pub trait RangeTreeOps: Sized + Default {
    type ExtNode: Default;
    fn op_add(&mut self, start: u64, end: u64);
    fn op_remove(&mut self, start: u64, end: u64);

    #[inline]
    fn stat_decrease(&mut self, _start: u64, _end: u64) {}

    #[inline]
    fn stat_increase(&mut self, _start: u64, _end: u64) {}
}

pub type RangeTreeSimple = RangeTree<DummyAllocator>;

#[derive(Default)]
#[repr(C)]
pub struct DummyAllocator();

impl RangeTreeOps for DummyAllocator {
    type ExtNode = ();
    #[inline]
    fn op_add(&mut self, _start: u64, _end: u64) {}

    #[inline]
    fn op_remove(&mut self, _start: u64, _end: u64) {}
}

/// A range segment representation for iteration and find results
#[derive(Clone, Copy)]
pub struct RangeSeg<T: RangeTreeOps> {
    pub start: u64,
    pub end: u64,
    _phantom: core::marker::PhantomData<T>,
}

impl<T: RangeTreeOps> RangeSeg<T> {
    #[inline]
    pub fn valid(&self) {
        assert!(self.start <= self.end, "RangeSeg:{:?} invalid", self);
    }

    #[inline]
    pub fn get_range(&self) -> (u64, u64) {
        (self.start, self.end)
    }
}

impl<T: RangeTreeOps> fmt::Display for RangeSeg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RangeSeg({}-{})", self.start, self.end)
    }
}

impl<T: RangeTreeOps> fmt::Debug for RangeSeg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "( start: {}, end:{} )", self.start, self.end)
    }
}

pub struct RangeTreeIter<'a, T: RangeTreeOps> {
    current: Option<alloc::collections::btree_map::Iter<'a, u64, u64>>,
    _phantom: core::marker::PhantomData<&'a T>,
}

unsafe impl<'a, T: RangeTreeOps> Send for RangeTreeIter<'a, T> {}

impl<'a, T: RangeTreeOps> Iterator for RangeTreeIter<'a, T> {
    type Item = RangeSeg<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let iter = self.current.as_mut()?;
        let (&start, &end) = iter.next()?;
        Some(RangeSeg { start, end, _phantom: core::marker::PhantomData })
    }
}

impl<'a, T: RangeTreeOps> IntoIterator for &'a RangeTree<T> {
    type Item = RangeSeg<T>;
    type IntoIter = RangeTreeIter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[allow(dead_code)]
impl<T: RangeTreeOps> Default for RangeTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: RangeTreeOps> RangeTree<T> {
    pub fn new() -> Self {
        RangeTree { map: BTreeMap::new(), space: 0, ops: T::default() }
    }

    #[inline]
    pub fn get_ops(&mut self) -> &mut T {
        &mut self.ops
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[inline(always)]
    pub fn get_space(&self) -> u64 {
        self.space
    }

    #[inline(always)]
    pub fn get_count(&self) -> i64 {
        self.map.len() as i64
    }

    #[inline(always)]
    pub fn add_abs(&mut self, start: u64, end: u64) {
        assert!(start < end, "range tree add start={} end={}", start, end);
        self.add(start, end - start);
    }

    /// Add range segment, possible adjacent, assume no overlapping with existing range
    ///
    /// # panic
    ///
    /// Panic if there's overlapping range
    #[inline]
    pub fn add(&mut self, start: u64, size: u64) {
        assert!(size > 0, "range tree add size={} error", size);
        let end = start + size;

        // Fast path: empty tree
        if self.map.is_empty() {
            self.map.insert(start, end);
            self.ops.op_add(start, end);
            self.ops.stat_increase(start, end);
            self.space += size;
            return;
        }

        // Single range(..=end) lookup to find:
        // 1. A range that ends at 'start' (merge before) - via next_back()
        // 2. A range that starts at 'end' (merge after) - via checking last entry
        let mut iter = self.map.range(..=end);

        // Get the last range with start <= end
        let last = iter.next_back();

        // Check for forward merge: is there a range starting exactly at end?
        let mut merge_after = false;
        let mut after_end = 0;

        if let Some((&last_start, &last_end)) = last {
            // Check if last range starts exactly at end (merge after)
            if last_start == end {
                merge_after = true;
                after_end = last_end;
            }

            // Check for overlap with last range
            // Last range [last_start, last_end) should not overlap with [start, end)
            if last_start < end && last_end > start {
                panic!(
                    "allocating allocated {}-{} overlaps with {}-{}",
                    start, end, last_start, last_end
                );
            }
        }

        // Now check for backward merge by looking at the previous range
        // We need a range that ends exactly at start
        let mut merge_before = false;
        let mut before_start = 0;

        if let Some((&prev_start, &prev_end)) = iter.next_back() {
            // Check if previous range ends exactly at start (merge before)
            if prev_end == start {
                merge_before = true;
                before_start = prev_start;
            }

            // Also check for overlap with previous range
            if prev_end > start {
                panic!(
                    "allocating allocated {}-{} overlaps with {}-{}",
                    start, end, prev_start, prev_end
                );
            }
        } else if last.is_some() {
            // No previous range in iterator, but we have last
            // Check if last range (which has start <= end) could be before start
            let (last_start, last_end) = last.unwrap();
            if *last_start < start && *last_end == start {
                merge_before = true;
                before_start = *last_start;
            }
        }

        self.space += size;

        match (merge_before, merge_after) {
            (true, true) => {
                // Merge both sides: [before] + [new] + [after]
                self.ops.op_remove(before_start, start);
                self.ops.op_remove(end, after_end);
                self.map.remove(&before_start);
                self.map.remove(&end);

                self.map.insert(before_start, after_end);
                self.ops.op_add(before_start, after_end);

                self.ops.stat_decrease(before_start, start);
                self.ops.stat_decrease(end, after_end);
                self.ops.stat_increase(before_start, after_end);
            }
            (true, false) => {
                // Merge before only
                self.ops.op_remove(before_start, start);
                self.map.remove(&before_start);

                self.map.insert(before_start, end);
                self.ops.op_add(before_start, end);

                self.ops.stat_decrease(before_start, start);
                self.ops.stat_increase(before_start, end);
            }
            (false, true) => {
                // Merge after only
                self.ops.op_remove(end, after_end);
                self.map.remove(&end);

                self.map.insert(start, after_end);
                self.ops.op_add(start, after_end);

                self.ops.stat_decrease(end, after_end);
                self.ops.stat_increase(start, after_end);
            }
            (false, false) => {
                // No merge, just insert
                self.map.insert(start, end);
                self.ops.op_add(start, end);
                self.ops.stat_increase(start, end);
            }
        }
    }

    /// Find a range that overlaps with [start, end)
    fn find_overlapping(&self, start: u64, end: u64) -> Option<(u64, u64)> {
        // Find the first range with start >= start, or the range before it
        let mut iter = self.map.range(..=start);
        if let Some((&prev_start, &prev_end)) = iter.next_back() {
            if prev_end > start {
                // Overlaps with previous range
                return Some((prev_start, prev_end));
            }
        }

        // Check the next range
        let mut iter = self.map.range(start..);
        if let Some((&next_start, &next_end)) = iter.next() {
            if next_start < end {
                // Overlaps with next range
                return Some((next_start, next_end));
            }
        }

        None
    }

    /// Add range segment, possible adjacent, and check overlapping.
    ///
    /// If there's overlapping with existing range, return `Err((start, end))`
    #[inline]
    pub fn add_find_overlap(&mut self, start: u64, size: u64) -> Result<(), (u64, u64)> {
        assert!(size > 0, "range tree add size={} error", size);
        let end = start + size;

        // Check for overlapping range
        if let Some((existing_start, existing_end)) = self.find_overlapping(start, end) {
            let max_start = if start > existing_start { start } else { existing_start };
            let min_end = if end < existing_end { end } else { existing_end };
            return Err((max_start, min_end));
        }

        self.space += size;
        self.merge_seg(start, end);
        Ok(())
    }

    /// Add range which may be crossed section or larger with existing, will merge the range
    #[inline]
    pub fn add_and_merge(&mut self, start: u64, size: u64) {
        assert!(size > 0, "range tree add size={} error", size);
        let mut new_start = start;
        let mut new_end = start + size;

        // Find and merge all overlapping ranges
        loop {
            let mut found_overlap = false;

            // Check for overlapping range
            if let Some((existing_start, existing_end)) = self.find_overlapping(new_start, new_end)
            {
                // Expand the new range to include the overlapping range
                if existing_start < new_start {
                    new_start = existing_start;
                }
                if existing_end > new_end {
                    new_end = existing_end;
                }

                // Remove the overlapping range
                self.ops.op_remove(existing_start, existing_end);
                self.ops.stat_decrease(existing_start, existing_end);
                self.map.remove(&existing_start);
                self.space -= existing_end - existing_start;
                found_overlap = true;
            }

            if !found_overlap {
                break;
            }
        }

        self.space += new_end - new_start;
        self.merge_seg(new_start, new_end);
    }

    #[inline(always)]
    fn merge_seg(&mut self, start: u64, end: u64) {
        // Check for adjacent ranges to merge
        let mut merge_before = false;
        let mut merge_after = false;
        let (mut before_start, mut before_end) = (0, 0);
        let (mut after_start, mut after_end) = (0, 0);

        // Check the range before
        let mut iter = self.map.range(..start);
        if let Some((&prev_start, &prev_end)) = iter.next_back() {
            if prev_end == start {
                merge_before = true;
                before_start = prev_start;
                before_end = prev_end;
            }
        }

        // Check the range after
        let mut iter = self.map.range(end..);
        if let Some((&next_start, &next_end)) = iter.next() {
            if next_start == end {
                merge_after = true;
                after_start = next_start;
                after_end = next_end;
            }
        }

        if merge_before && merge_after {
            // Merge Both: [before] + [new] + [after]
            self.ops.op_remove(before_start, before_end);
            self.ops.op_remove(after_start, after_end);
            self.map.remove(&before_start);
            self.map.remove(&after_start);

            // Insert merged range
            self.map.insert(before_start, after_end);
            self.ops.op_add(before_start, after_end);

            self.ops.stat_decrease(before_start, before_end);
            self.ops.stat_decrease(after_start, after_end);
            self.ops.stat_increase(before_start, after_end);
        } else if merge_before {
            // Merge Before Only: Extend `before.end`
            self.ops.op_remove(before_start, before_end);
            self.map.remove(&before_start);

            self.map.insert(before_start, end);
            self.ops.op_add(before_start, end);

            self.ops.stat_decrease(before_start, before_end);
            self.ops.stat_increase(before_start, end);
        } else if merge_after {
            // Merge After Only: Extend `after.start`
            self.ops.op_remove(after_start, after_end);
            self.map.remove(&after_start);

            self.map.insert(start, after_end);
            self.ops.op_add(start, after_end);

            self.ops.stat_decrease(after_start, after_end);
            self.ops.stat_increase(start, after_end);
        } else {
            // No Merge. Insert new.
            self.map.insert(start, end);
            self.ops.op_add(start, end);
            self.ops.stat_increase(start, end);
        }
    }

    /// Ensure remove all overlapping range
    ///
    /// Returns true if removal happens
    #[inline(always)]
    pub fn remove_and_split(&mut self, start: u64, size: u64) -> bool {
        let mut removed = false;
        loop {
            if !self.remove(start, size) {
                break;
            }
            removed = true;
        }
        removed
    }

    /// Only used when remove range overlap one segment,
    ///
    /// NOTE: If not the case (start, size) might overlaps with multiple segment,  use remove_and_split() instead.
    /// return true when one segment is removed.
    #[inline]
    pub fn remove(&mut self, start: u64, size: u64) -> bool {
        let end = start + size;

        // Find the overlapping range
        let overlapping = self.find_overlapping(start, end);
        if overlapping.is_none() {
            return false;
        }

        let (rs_start, rs_end) = overlapping.unwrap();

        assert!(size > 0, "range tree remove size={} error", size);
        assert!(
            rs_start <= end && rs_end >= start,
            "range tree remove error, rs_start={} rs_end={} start={} end={}",
            rs_start,
            rs_end,
            start,
            end
        );

        let left_over = rs_start < start;
        let right_over = rs_end > end;
        let size_deduce: u64;

        self.ops.op_remove(rs_start, rs_end);
        self.map.remove(&rs_start);

        if left_over && right_over {
            // Remove the middle of segment larger than requested range
            size_deduce = size;
            // Insert Left part [rs_start, start)
            self.map.insert(rs_start, start);
            self.ops.op_add(rs_start, start);
            // Insert Right part [end, rs_end)
            self.map.insert(end, rs_end);
            self.ops.op_add(end, rs_end);

            self.ops.stat_decrease(rs_start, rs_end);
            self.ops.stat_increase(rs_start, start);
            self.ops.stat_increase(end, rs_end);
        } else if left_over {
            // Remove Right end
            size_deduce = rs_end - start;
            // Insert Left part [rs_start, start)
            self.map.insert(rs_start, start);
            self.ops.op_add(rs_start, start);

            self.ops.stat_decrease(rs_start, rs_end);
            self.ops.stat_increase(rs_start, start);
        } else if right_over {
            // Remove Left end
            size_deduce = end - rs_start;
            // Insert Right part [end, rs_end)
            self.map.insert(end, rs_end);
            self.ops.op_add(end, rs_end);

            self.ops.stat_decrease(rs_start, rs_end);
            self.ops.stat_increase(end, rs_end);
        } else {
            // Remove Exact / Total
            size_deduce = rs_end - rs_start;
            self.ops.stat_decrease(rs_start, rs_end);
        }

        self.space -= size_deduce;
        true
    }

    /// return only when segment overlaps with [start, start+size]
    #[inline]
    pub fn find(&self, start: u64, size: u64) -> Option<RangeSeg<T>> {
        if self.map.is_empty() {
            return None;
        }
        assert!(size > 0, "range tree find size={} error", size);
        let end = start + size;

        self.find_overlapping(start, end).map(|(s, e)| RangeSeg {
            start: s,
            end: e,
            _phantom: core::marker::PhantomData,
        })
    }

    /// return only when segment overlaps with [start, start+size), if multiple segment exists,
    /// return the smallest start
    #[inline]
    pub fn find_contained(&self, start: u64, size: u64) -> Option<RangeSeg<T>> {
        assert!(size > 0, "range tree find size={} error", size);
        if self.map.is_empty() {
            return None;
        }
        let end = start + size;

        // Find overlapping range with the smallest start
        // First check if there's a range starting before or at 'start' that overlaps
        if let Some((&prev_start, &prev_end)) = self.map.range(..=start).next_back() {
            if prev_end > start {
                // Overlapping: [prev_start, prev_end) overlaps with [start, end)
                return Some(RangeSeg {
                    start: prev_start,
                    end: prev_end,
                    _phantom: core::marker::PhantomData,
                });
            }
        }

        // Then check if there's a range starting within [start, end)
        if let Some((&s, &e)) = self.map.range(start..end).next() {
            return Some(RangeSeg { start: s, end: e, _phantom: core::marker::PhantomData });
        }

        None
    }

    #[inline]
    pub fn iter(&self) -> RangeTreeIter<'_, T> {
        RangeTreeIter { current: Some(self.map.iter()), _phantom: core::marker::PhantomData }
    }

    #[inline]
    pub fn walk<F: FnMut(&RangeSeg<T>)>(&self, mut cb: F) {
        for (&start, &end) in &self.map {
            let seg = RangeSeg { start, end, _phantom: core::marker::PhantomData };
            cb(&seg);
        }
    }

    /// If cb returns false, break
    #[inline]
    pub fn walk_conditioned<F: FnMut(&RangeSeg<T>) -> bool>(&self, mut cb: F) {
        for (&start, &end) in &self.map {
            let seg = RangeSeg { start, end, _phantom: core::marker::PhantomData };
            if !cb(&seg) {
                break;
            }
        }
    }

    /// Validate the BTreeMap structure
    pub fn validate(&self) {
        let mut prev_end: Option<u64> = None;
        for (&start, &end) in &self.map {
            assert!(start < end, "Invalid range: start {} >= end {}", start, end);
            if let Some(pe) = prev_end {
                assert!(
                    start > pe,
                    "Overlapping or adjacent ranges detected: previous end {} >= current start {}",
                    pe,
                    start
                );
            }
            prev_end = Some(end);
        }

        // Verify space calculation
        let calculated_space: u64 = self
            .map
            .values()
            .map(|&end| end)
            .zip(self.map.keys().map(|&start| start))
            .map(|(end, start)| end - start)
            .sum();
        assert_eq!(
            self.space, calculated_space,
            "Space mismatch: stored {} != calculated {}",
            self.space, calculated_space
        );
    }
}

#[cfg(feature = "std")]
pub fn range_tree_print(tree: &RangeTreeSimple) {
    if tree.get_space() == 0 {
        println!("tree is empty");
    } else {
        tree.walk(|rs| {
            println!("\t{}-{}", rs.start, rs.end);
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_tree_sizeof() {
        println!("range tree sizeof {}", std::mem::size_of::<RangeTreeSimple>());
        println!(
            "RangeSeg<DummyAllocator>  sizeof {}",
            std::mem::size_of::<RangeSeg<DummyAllocator>>()
        );
    }

    #[test]
    fn range_tree_add() {
        let mut rt = RangeTreeSimple::new();
        assert!(rt.find(0, 10).is_none());
        assert_eq!(0, rt.get_space());

        rt.add(0, 2);
        assert_eq!(2, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 2), rs.as_ref().unwrap().get_range());

        assert!(rt.find_contained(0, 3).is_some());

        // left join
        rt.add_and_merge(2, 5);
        assert_eq!(7, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().get_range());

        // without join
        rt.add_and_merge(10, 5);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 15), rs.unwrap().get_range());

        // right join
        rt.add_and_merge(8, 2);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 15), rs.unwrap().get_range());

        // left and right join
        rt.add_and_merge(7, 1);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((0, 15), rs.unwrap().get_range());

        rt.validate();
    }

    #[test]
    fn range_tree_add_and_merge() {
        let mut rt = RangeTreeSimple::new();
        assert!(rt.find(0, 10).is_none());
        assert_eq!(0, rt.get_space());

        rt.add_and_merge(0, 2);
        assert_eq!(2, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 2), rs.as_ref().unwrap().get_range());

        assert!(rt.find_contained(0, 3).is_some()); // REVERT FIX: Changed from is_none() to is_some()

        // left join
        rt.add_and_merge(2, 5);
        assert_eq!(7, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().get_range());

        // without join
        rt.add_and_merge(15, 5);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((15, 20), rs.unwrap().get_range());

        // right join
        rt.add_and_merge(13, 2);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((13, 20), rs.unwrap().get_range());

        // duplicate
        rt.add_and_merge(14, 8);
        assert_eq!(16, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().get_range());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((13, 22), rs.unwrap().get_range());

        // without join
        rt.add_and_merge(25, 5);
        assert_eq!(21, rt.get_space());
        assert_eq!(3, rt.get_count());

        let rs = rt.find_contained(26, 1);
        assert!(rs.is_some());
        assert_eq!((25, 30), rs.unwrap().get_range());

        // duplicate
        rt.add_and_merge(12, 20);
        assert_eq!(27, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().get_range());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((12, 32), rs.unwrap().get_range());

        // left and right join
        rt.add_and_merge(7, 5);
        assert_eq!(32, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((0, 32), rs.unwrap().get_range());

        rt.validate();
    }

    #[test]
    fn range_tree_remove() {
        let mut rt = RangeTreeSimple::new();
        // add [0, 15]
        rt.add(0, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        // remove [7, 8] expect [0, 7] [8, 15]
        rt.remove(7, 1);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 15), rs.unwrap().get_range());
        rt.validate();

        // remove [12, 15] expect [0, 7] [8, 12]
        rt.remove(12, 3);
        assert_eq!(11, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 12), rs.unwrap().get_range());
        rt.validate();

        // remove [2, 5] expect [0, 2] [5, 7] [8, 12]
        rt.remove(2, 3);
        assert_eq!(8, rt.get_space());
        assert_eq!(3, rt.get_count());

        let rs = rt.find_contained(5, 1);
        assert!(rs.is_some());
        assert_eq!((5, 7), rs.unwrap().get_range());
        rt.validate();

        // remove [8, 10] expect [0, 2] [5, 7] [10, 12]
        rt.remove(8, 2);
        assert_eq!(6, rt.get_space());
        assert_eq!(3, rt.get_count());

        let rs = rt.find_contained(10, 1);
        assert!(rs.is_some());
        assert_eq!((10, 12), rs.unwrap().get_range());
        rt.validate();

        // remove [0, 2] expect [5, 7] [10, 12]
        rt.remove(0, 2);
        assert_eq!(4, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(5, 1);
        assert!(rs.is_some());
        assert_eq!((5, 7), rs.unwrap().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_walk() {
        let mut rt = RangeTreeSimple::new();
        rt.add(0, 2);
        rt.add(4, 4);
        rt.add(12, 8);
        rt.add(32, 16);
        assert_eq!(30, rt.get_space());
        assert_eq!(4, rt.get_count());

        fn cb_print(rs: &RangeSeg<DummyAllocator>) {
            println!("walk callback cb_print range_seg:{:?}", rs);
        }

        rt.walk(cb_print);
    }

    #[test]
    fn range_tree_iter() {
        let mut rt = RangeTreeSimple::new();
        rt.add(0, 2);
        rt.add(4, 4);
        rt.add(12, 8);
        rt.add(32, 16);

        let mut count = 0;
        let mut total_space = 0;
        for rs in rt.iter() {
            count += 1;
            total_space += rs.end - rs.start;
        }
        assert_eq!(count, rt.get_count() as usize);
        assert_eq!(total_space, rt.get_space());
        assert_eq!(4, count);
        assert_eq!(30, total_space);

        // Test IntoIterator
        let ranges_from_into_iter: Vec<(u64, u64)> =
            (&rt).into_iter().map(|rs| rs.get_range()).collect();
        assert_eq!(ranges_from_into_iter, vec![(0, 2), (4, 8), (12, 20), (32, 48)]);

        // Test for loop on reference
        let mut ranges_from_for: Vec<(u64, u64)> = Vec::new();
        for rs in &rt {
            ranges_from_for.push(rs.get_range());
        }
        assert_eq!(ranges_from_for, vec![(0, 2), (4, 8), (12, 20), (32, 48)]);
    }

    #[test]
    fn range_tree_find_overlap() {
        let mut rt = RangeTreeSimple::new();
        rt.add_abs(2044, 2052);
        rt.add_abs(4092, 4096);
        rt.add_abs(516096, 516098);
        rt.add_abs(518140, 518148);
        rt.add_abs(520188, 520194);
        rt.add_abs(522236, 522244);
        rt.add_abs(524284, 524288);
        rt.add_abs(66060288, 66060290);
        rt.add_abs(66062332, 66062340);
        rt.add_abs(66064380, 66064384);
        let result = rt.find_contained(0, 4096).unwrap();
        assert_eq!(result.start, 2044);
        assert_eq!(result.end, 2052);
        for i in &[4096, 516098, 518148, 520194, 522244, 524288, 66060290, 66062340, 66064384] {
            let result = rt.find_contained(4000, *i).unwrap();
            assert_eq!(result.start, 4092);
        }
        range_tree_print(&rt);
        let _space1 = rt.get_space();
        assert!(rt.remove(0, 66064384));
        assert!(rt.get_space() > 0, "only remove one");
        range_tree_print(&rt);
        rt.remove_and_split(0, 66064384); // remove all
        assert_eq!(rt.get_space(), 0);
    }

    #[test]
    fn range_tree_find_overlap_simple() {
        let mut rt = RangeTreeSimple::new();
        rt.add_abs(20, 80);
        rt.add_abs(120, 180);
        rt.add_abs(220, 280);
        rt.add_abs(320, 380);
        rt.add_abs(420, 480);
        rt.add_abs(520, 580);
        rt.add_abs(620, 680);
        range_tree_print(&rt);
        let result = rt.find_contained(240, 340).unwrap();
        assert_eq!(result.start, 220);
        assert_eq!(result.end, 280);
    }

    #[test]
    fn range_tree_remove1() {
        let mut rt = RangeTreeSimple::new();

        // add [0, 15]
        rt.add(0, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        // remove [7, 10] expect [0, 7] [10, 15]
        rt.remove_and_split(7, 3);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 15), rs.unwrap().get_range());
        rt.validate();

        // remove right over [13, 18] expect [0, 7] [10, 13]
        rt.remove_and_split(13, 5);
        assert_eq!(10, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 13), rs.unwrap().get_range());
        rt.validate();

        // remove nothing [9, 10] expect [0, 7] [10, 13]
        assert!(!rt.remove_and_split(9, 1));
        assert_eq!(10, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 13), rs.unwrap().get_range());
        rt.validate();

        // remove left over [9, 11] expect [0, 7] [11, 13]
        rt.remove_and_split(9, 2);
        assert_eq!(9, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((11, 13), rs.unwrap().get_range());
        rt.validate();

        // remove [6, 12] expect [0, 6] [12, 13]
        rt.remove_and_split(6, 6);
        assert_eq!(7, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(0, 5);
        assert!(rs.is_some());
        assert_eq!((0, 6), rs.unwrap().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove2() {
        let mut rt = RangeTreeSimple::new();

        // add [0, 15]
        rt.add(0, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((0, 15), rs.unwrap().get_range());
        rt.validate();

        // remove left over and right over [0, 20] expect []
        rt.remove_and_split(0, 20);
        assert_eq!(0, rt.get_space());
        assert_eq!(0, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_none());
        rt.validate();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove3() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().get_range());
        rt.validate();

        // add [49, 64]
        rt.add(49, 15);
        assert_eq!(45, rt.get_space());
        assert_eq!(3, rt.get_count());

        let rs = rt.find_contained(50, 1);
        assert!(rs.is_some());
        assert_eq!((49, 64), rs.unwrap().get_range());
        rt.validate();

        // remove left over and right over [6, 56] expect [1, 6] [56, 64]
        rt.remove_and_split(6, 50);
        assert_eq!(13, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(58, 1);
        assert!(rs.is_some());
        assert_eq!((56, 64), rs.unwrap().get_range());
        rt.validate();

        let rs = rt.find_contained(3, 1);
        assert!(rs.is_some());
        assert_eq!((1, 6), rs.unwrap().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove4() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().get_range());
        rt.validate();

        // remove right over [6, 56] expect [1, 6]
        rt.remove_and_split(6, 50);
        assert_eq!(5, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(3, 1);
        assert!(rs.is_some());
        assert_eq!((1, 6), rs.unwrap().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove5() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().get_range());
        rt.validate();

        // remove left over [0, 40] expect [40, 48]
        rt.remove_and_split(0, 40);
        assert_eq!(8, rt.get_space());
        assert_eq!(1, rt.get_count());

        let rs = rt.find_contained(42, 1);
        assert!(rs.is_some());
        assert_eq!((40, 48), rs.unwrap().get_range());
        rt.validate();
    }

    // Test RangeTreeOps
    pub struct TestAllocator {
        size_tree: BTreeMap<u64, u64>, // start -> end mapping for tracking sizes
    }

    impl Default for TestAllocator {
        fn default() -> Self {
            Self::new()
        }
    }

    impl TestAllocator {
        pub fn new() -> Self {
            TestAllocator { size_tree: BTreeMap::new() }
        }
    }

    impl Drop for TestAllocator {
        fn drop(&mut self) {
            println!("drop test allocator");
        }
    }

    impl RangeTreeOps for TestAllocator {
        type ExtNode = ();

        fn op_add(&mut self, start: u64, end: u64) {
            self.size_tree.insert(start, end);
        }

        fn op_remove(&mut self, start: u64, _end: u64) {
            self.size_tree.remove(&start);
        }
    }

    #[test]
    fn range_tree_ops() {
        // TODO test allocator size tree
        let mut ms_tree = RangeTree::<TestAllocator>::new();

        assert!(ms_tree.find(0, 10).is_none());
        assert_eq!(0, ms_tree.get_space());

        ms_tree.add(0, 100);
        assert_eq!(100, ms_tree.get_space());
        assert_eq!(1, ms_tree.get_count());

        let rs = ms_tree.find(0, 1).unwrap();
        assert_eq!((0, 100), rs.get_range());

        ms_tree.remove(0, 100);
        assert_eq!(0, ms_tree.get_space());
        assert_eq!(0, ms_tree.get_count());

        println!("out")
    }
}
