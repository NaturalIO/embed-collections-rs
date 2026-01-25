use std::mem::offset_of;
use std::{cell::UnsafeCell, cmp::Ordering, fmt, sync::Arc};

use super::avl_old::{AvlDirection, AvlNode, AvlNodeRef, AvlSearchResult, AvlTree};

const MIDDLE_SIZE_LOW_BOUND: u64 = 16 * 1024;
const MIDDLE_SIZE_UP_BOUND: u64 = 64 * 1024;

#[derive(Default)]
pub struct RangeSeg {
    node: AvlNode<RangeSeg>,
    pub ext_node: AvlNode<RangeSeg>,
    pub start: u64,
    pub end: u64,
}

pub type RangeSegRef = AvlNodeRef<RangeSeg>;

pub struct RangeTree<T>
where
    T: RangeTreeOps,
{
    root: AvlTree<RangeSeg>,
    space: u64,
    small_count: usize,
    middle_count: usize,
    large_count: usize,
    ops: Option<T>,
    enable_stats: bool,
}

pub trait RangeTreeOps {
    fn op_add(&mut self, rs: RangeSegRef);
    fn op_remove(&mut self, rs: &RangeSegRef);
}

pub type RangeTreeSimple = RangeTree<DummyAllocator>;

pub struct DummyAllocator();

impl RangeSeg {
    #[inline]
    pub fn valid(&self) {
        assert!(self.start <= self.end, "RangeSeg:{:?} invalid", self);
    }

    #[inline]
    pub fn new_raw(s: u64, e: u64) -> RangeSeg {
        RangeSeg { start: s, end: e, ..Default::default() }
    }

    #[inline]
    pub fn new(s: u64, e: u64) -> RangeSegRef {
        AvlNodeRef(Arc::new(UnsafeCell::new(RangeSeg { start: s, end: e, ..Default::default() })))
    }

    #[inline]
    pub fn get_range(&self) -> (u64, u64) {
        (self.start, self.end)
    }
}

impl fmt::Display for RangeSeg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RangeSeg({}-{}) ", self.start, self.end)
    }
}

impl fmt::Debug for RangeSeg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let _ = write!(f, "( start: {}, end:{}, ", self.start, self.end);
        let _ = write!(f, "node: {:#?}, ", &self.node);
        let _ = write!(f, "ext_node: {:#?} ", &self.ext_node);
        write!(f, ")")
    }
}

impl RangeTreeOps for DummyAllocator {
    #[inline]
    fn op_add(&mut self, _rs: RangeSegRef) {}

    #[inline]
    fn op_remove(&mut self, _rs: &RangeSegRef) {}
}

// when return is overlapping, return equal
fn range_tree_segment_cmp(a: &RangeSeg, b: &RangeSegRef) -> Ordering {
    let _a = a;
    let _b = b.borrow();
    //    _a.valid();
    //    _b.valid();
    if _a.end <= _b.start {
        return Ordering::Less;
    } else if _a.start >= _b.end {
        return Ordering::Greater;
    } else {
        return Ordering::Equal;
    }
}

#[allow(dead_code)]
impl<T: RangeTreeOps> RangeTree<T> {
    pub fn new() -> Self {
        let off_node = offset_of!(RangeSeg, node);
        let rt = RangeTree {
            root: AvlTree::<RangeSeg>::new(off_node),
            space: 0,
            small_count: 0,
            middle_count: 0,
            large_count: 0,
            ops: None,
            enable_stats: false,
        };
        return rt;
    }

    pub fn enable_stats(&mut self) {
        self.enable_stats = true;
    }

    pub fn set_ops(&mut self, ops: T) {
        self.ops.replace(ops);
    }

    #[inline]
    pub fn get_ops(&mut self) -> Option<&mut T> {
        self.ops.as_mut()
    }

    pub fn is_empty(&self) -> bool {
        if 0 == self.root.get_count() {
            return true;
        }
        false
    }

    #[inline(always)]
    pub fn get_space(&self) -> u64 {
        return self.space;
    }

    #[inline(always)]
    pub fn get_count(&self) -> i64 {
        return self.root.get_count();
    }

    #[inline(always)]
    pub fn get_small_count(&self) -> usize {
        return self.small_count;
    }

    #[inline(always)]
    pub fn get_middle_count(&self) -> usize {
        return self.middle_count;
    }

    #[inline(always)]
    pub fn get_large_count(&self) -> usize {
        return self.large_count;
    }

    #[inline]
    fn stat_decrease(&mut self, start: u64, end: u64) {
        assert!(end > start, "range tree stat_decrease start={} end={} error", start, end);
        let size = end - start;
        if size < MIDDLE_SIZE_LOW_BOUND {
            self.small_count -= 1;
        } else if size >= MIDDLE_SIZE_UP_BOUND {
            self.large_count -= 1;
        } else {
            self.middle_count -= 1;
        }
    }

    #[inline]
    fn stat_increase(&mut self, start: u64, end: u64) {
        assert!(end > start, "range tree stat_increase start={} end={} error", start, end);
        let size = end - start;
        if size < MIDDLE_SIZE_LOW_BOUND {
            self.small_count += 1;
        } else if size >= MIDDLE_SIZE_UP_BOUND {
            self.large_count += 1;
        } else {
            self.middle_count += 1;
        }
    }

    // Add range segment, possible adjacent, assume no overlapping with existing range
    pub fn add(&mut self, start: u64, size: u64) {
        assert!(size > 0, "range tree add size={} error", size);
        let rs_raw = RangeSeg::new_raw(start, start + size);
        let result = self.root.find(&rs_raw, range_tree_segment_cmp);
        if result.direction.is_none() {
            panic!("allocating allocated {} of {}", &rs_raw, result.into_exact().unwrap());
        }

        self.space += size;
        self.merge_seg(rs_raw, result);
    }

    // Add range segment, possible adjacent, assume no overlapping with existing range
    pub fn add_find_overlap(&mut self, start: u64, size: u64) -> Result<(), (u64, u64)> {
        assert!(size > 0, "range tree add size={} error", size);
        let rs_raw = RangeSeg::new_raw(start, start + size);
        let result = self.root.find(&rs_raw, range_tree_segment_cmp);
        if result.direction.is_none() {
            let ol_node = result.into_exact().unwrap();
            let max_start = if rs_raw.start > ol_node.start { rs_raw.start } else { ol_node.start };
            let min_end = if rs_raw.end > ol_node.end { ol_node.end } else { rs_raw.end };
            return Err((max_start, min_end));
        }

        self.space += size;
        self.merge_seg(rs_raw, result);
        return Ok(());
    }

    #[inline(always)]
    pub fn add_abs(&mut self, start: u64, end: u64) {
        assert!(start < end, "range tree add start={} end={}", start, end);
        self.add(start, end - start);
    }

    // Add range which may be crossed section or larger with existing
    pub fn add_and_merge(&mut self, start: u64, size: u64) {
        assert!(size > 0, "range tree add size={} error", size);
        let mut rs_raw = RangeSeg::new_raw(start, start + size);
        let mut result = self.root.find(&rs_raw, range_tree_segment_cmp);

        while result.direction.is_none() {
            let node = result.get_exact().unwrap();
            let _node = node.borrow();
            if _node.start < rs_raw.start {
                rs_raw.start = _node.start;
            }
            if _node.end > rs_raw.end {
                rs_raw.end = _node.end;
            }
            if !self.remove(_node.start, _node.end - _node.start) {
                panic!("rs[{}:{}] NOT existed", _node.start, _node.end - _node.start);
            }
            result = self.root.find(&rs_raw, range_tree_segment_cmp);
        }

        self.space += rs_raw.end - rs_raw.start;
        self.merge_seg(rs_raw, result);
    }

    #[inline(always)]
    fn merge_seg(&mut self, rs: RangeSeg, result: AvlSearchResult<RangeSeg>) {
        let mut before = self.root.nearest(&result, AvlDirection::Left);
        let mut after = self.root.nearest(&result, AvlDirection::Right);
        let mut merge_before = false;
        let mut merge_after = false;
        let mut before_start = 0;
        let mut before_end = 0;
        let mut after_start = 0;
        let mut after_end = 0;
        let mut before_rs: Option<&mut RangeSeg> = None;
        let mut after_rs: Option<&mut RangeSeg> = None;
        let start = rs.start;
        let end = rs.end;
        if let Some(ref mut _before) = before {
            let __before = _before.borrow_mut();
            if __before.end == start {
                merge_before = true;
                before_start = __before.start;
                before_end = __before.end;
                before_rs.replace(__before);
            }
        }
        if let Some(ref mut _after) = after {
            let __after = _after.borrow_mut();
            if __after.start == end {
                merge_after = true;
                after_start = __after.start;
                after_end = __after.end;
                after_rs.replace(__after);
            }
        }

        match (merge_before, merge_after) {
            (true, true) => {
                let _before = before.as_ref().unwrap();
                self.root.remove(&_before);
                after_rs.unwrap().start = before_start;
                if let Some(ref mut ops) = self.ops {
                    ops.op_remove(&_before);
                    let _after = after.as_ref().unwrap();
                    ops.op_remove(&_after);
                    ops.op_add(after.unwrap());
                }

                if self.enable_stats {
                    self.stat_decrease(before_start, before_end);
                    self.stat_decrease(after_start, after_end);
                    self.stat_increase(before_start, after_end);
                }
            }
            (true, false) => {
                before_rs.unwrap().end = end;
                if let Some(ref mut ops) = self.ops {
                    let _before = before.as_ref().unwrap();
                    ops.op_remove(&_before);
                    ops.op_add(before.unwrap());
                }
                if self.enable_stats {
                    self.stat_decrease(before_start, before_end);
                    self.stat_increase(before_start, end);
                }
            }
            (false, true) => {
                after_rs.unwrap().start = start;
                if let Some(ref mut ops) = self.ops {
                    let _after = after.as_ref().unwrap();
                    ops.op_remove(&_after);
                    ops.op_add(after.unwrap());
                }
                if self.enable_stats {
                    self.stat_decrease(after_start, after_end);
                    self.stat_increase(start, after_end);
                }
            }
            (false, false) => {
                let node = AvlNodeRef(Arc::new(UnsafeCell::new(rs)));
                if let Some(ref mut ops) = self.ops {
                    ops.op_add(node.clone());
                }
                self.root.insert(node, result);
                if self.enable_stats {
                    self.stat_increase(start, end);
                }
            }
        }
    }

    // Ensure remove all overlaping range
    #[inline(always)]
    pub fn remove_and_split(&mut self, start: u64, size: u64) -> bool {
        let mut removed = false;
        loop {
            if !self.remove(start, size) {
                break;
            }
            removed = true;
        }
        return removed;
    }

    // Only used when remove range overlap one segment,
    // If not the case (start, size) might overlaps with muliple segment,  use remove_and_split() instead.
    // return true when one segment is removed.
    pub fn remove(&mut self, start: u64, size: u64) -> bool {
        let end = start + size;
        let search_rs = RangeSeg::new_raw(start, end);
        let result = self.root.find(&search_rs, range_tree_segment_cmp).into_exact();
        if result.is_none() {
            return false;
        }
        assert!(size > 0, "range tree remove size={} error", size);

        let rs_node = result.unwrap();
        let rs = rs_node.borrow_mut();
        let rs_start = rs.start;
        let rs_end = rs.end;
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

        match (left_over, right_over) {
            (true, true) => {
                // Remove the middle of segment larger than requested range
                size_deduce = size;
                if self.enable_stats {
                    self.stat_decrease(rs_start, rs_end);
                    self.stat_increase(rs_start, start);
                    self.stat_increase(end, rs_end);
                }

                rs.end = start;
                let _ = rs;

                let new_rs = RangeSeg::new(end, rs_end);

                if let Some(ref mut ops) = self.ops {
                    ops.op_remove(&rs_node);
                    ops.op_add(rs_node.clone());
                    ops.op_add(new_rs.clone());
                }
                self.root.insert_here(new_rs, &rs_node, AvlDirection::Right);
            }
            (true, false) => {
                // Remove the right end of segment larger than requested range
                size_deduce = rs_end - start;
                if self.enable_stats {
                    self.stat_decrease(rs_start, rs_end);
                    self.stat_increase(rs_start, start);
                }

                let _ = rs;

                if let Some(ref mut ops) = self.ops {
                    ops.op_remove(&rs_node);
                    ops.op_add(rs_node);
                }
            }
            (false, true) => {
                // Remove the left of segment larger than requested range
                size_deduce = end - rs_start;
                if self.enable_stats {
                    self.stat_decrease(rs_start, rs_end);
                    self.stat_increase(end, rs_end);
                }

                let _ = rs;
                if let Some(ref mut ops) = self.ops {
                    ops.op_remove(&rs_node);
                    ops.op_add(rs_node);
                }
            }
            (false, false) => {
                // Remove the node of one segment smaller than or equal with requested range
                size_deduce = rs_end - rs_start;
                let _ = rs;
                self.root.remove(&rs_node);
                if let Some(ref mut ops) = self.ops {
                    ops.op_remove(&rs_node);
                }
                if self.enable_stats {
                    self.stat_decrease(rs_start, rs_end);
                }
            }
        }
        self.space -= size_deduce;
        return true;
    }

    // return only when segment overlaps with [start, start+size]
    pub fn find(&self, start: u64, size: u64) -> Option<RangeSegRef> {
        if self.root.get_count() == 0 {
            return None;
        }
        debug_assert!(size > 0, "range tree find size={} error", size);
        let end = start + size;
        let rs = RangeSeg::new_raw(start, end);
        let result = self.root.find(&rs, range_tree_segment_cmp);
        return result.into_exact();
    }

    // return only when segment contains [start, size], if multiple segment exists, return the
    // smallest start
    pub fn find_contained(&self, start: u64, size: u64) -> Option<RangeSegRef> {
        debug_assert!(size > 0, "range tree find size={} error", size);
        if self.root.get_count() == 0 {
            return None;
        }
        let end = start + size;
        let rs_search = RangeSeg::new_raw(start, end);
        self.root.find_contained(&rs_search, range_tree_segment_cmp)
    }

    pub fn walk<F: FnMut(&RangeSegRef)>(&self, mut cb: F) {
        let mut node = self.root.first();
        loop {
            if let Some(_node) = node {
                cb(&_node);
                node = self.root.walk(&_node, AvlDirection::Right);
            } else {
                break;
            }
        }
    }

    // If cb returns false, break
    pub fn walk_conditioned<F: FnMut(&RangeSegRef) -> bool>(&self, mut cb: F) {
        let mut node = self.root.first();
        loop {
            if let Some(_node) = node {
                if !cb(&_node) {
                    break;
                }
                node = self.root.walk(&_node, AvlDirection::Right);
            } else {
                break;
            }
        }
    }

    pub fn get_root(&self) -> &AvlTree<RangeSeg> {
        return &self.root;
    }

    pub fn validate(&self) {
        self.root.validate(range_tree_segment_cmp);
    }
}

pub fn size_tree_insert_cmp(a: &RangeSeg, b: &RangeSegRef) -> Ordering {
    let _a = a;
    let _b = b.borrow();
    let size_a = _a.end - _a.start;
    let size_b = _b.end - _b.start;
    if size_a < size_b {
        return Ordering::Less;
    } else if size_a > size_b {
        return Ordering::Greater;
    } else {
        if _a.start < _b.start {
            return Ordering::Less;
        } else if _a.start > _b.start {
            return Ordering::Greater;
        } else {
            return Ordering::Equal;
        }
    }
}

pub fn size_tree_find_cmp(a: &RangeSeg, b: &RangeSegRef) -> Ordering {
    let _a = a;
    let _b = b.borrow();
    let size_a = _a.end - _a.start;
    let size_b = _b.end - _b.start;
    return size_a.cmp(&size_b);
}

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
    fn range_tree_add() {
        let mut rt = RangeTreeSimple::new();
        assert!(rt.find(0, 10).is_none());
        assert_eq!(0, rt.get_space());

        rt.add(0, 2);
        assert_eq!(2, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 2), rs.as_ref().unwrap().borrow().get_range());
        assert_eq!(2, Arc::strong_count(&rs.unwrap().0));

        assert!(rt.find_contained(0, 3).is_some());

        // left join
        rt.add(2, 5);
        assert_eq!(7, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().borrow().get_range());

        // without join
        rt.add(10, 5);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 15), rs.unwrap().borrow().get_range());

        // right join
        rt.add(8, 2);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 15), rs.unwrap().borrow().get_range());

        // left and right join
        rt.add(7, 1);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((0, 15), rs.unwrap().borrow().get_range());

        rt.validate();
    }

    #[test]
    fn range_tree_add_and_merge() {
        let mut rt = RangeTreeSimple::new();
        assert!(rt.find(0, 10).is_none());
        assert_eq!(0, rt.get_space());

        rt.add_and_merge(0, 2);
        assert_eq!(2, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 2), rs.as_ref().unwrap().borrow().get_range());
        assert_eq!(2, Arc::strong_count(&rs.unwrap().0));

        assert!(rt.find_contained(0, 3).is_some());

        // left join
        rt.add_and_merge(2, 5);
        assert_eq!(7, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().borrow().get_range());

        // without join
        rt.add_and_merge(15, 5);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((15, 20), rs.unwrap().borrow().get_range());

        // right join
        rt.add_and_merge(13, 2);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((13, 20), rs.unwrap().borrow().get_range());

        // duplicate
        rt.add_and_merge(14, 8);
        assert_eq!(16, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().borrow().get_range());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((13, 22), rs.unwrap().borrow().get_range());

        // without join
        rt.add_and_merge(25, 5);
        assert_eq!(21, rt.get_space());
        assert_eq!(3, rt.root.get_count());

        let rs = rt.find_contained(26, 1);
        assert!(rs.is_some());
        assert_eq!((25, 30), rs.unwrap().borrow().get_range());

        // duplicate
        rt.add_and_merge(12, 20);
        assert_eq!(27, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(0, 1);
        assert!(rs.is_some());
        assert_eq!((0, 7), rs.unwrap().borrow().get_range());

        let rs = rt.find_contained(16, 1);
        assert!(rs.is_some());
        assert_eq!((12, 32), rs.unwrap().borrow().get_range());

        // left and right join
        rt.add_and_merge(7, 5);
        assert_eq!(32, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((0, 32), rs.unwrap().borrow().get_range());

        rt.validate();
    }

    #[test]
    fn range_tree_remove() {
        let mut rt = RangeTreeSimple::new();
        // add [0, 15]
        rt.add(0, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        // remove [7, 8] expect [0, 7] [8, 15]
        rt.remove(7, 1);
        assert_eq!(14, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 15), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove [12, 15] expect [0, 7] [8, 12]
        rt.remove(12, 3);
        assert_eq!(11, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((8, 12), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove [2, 5] expect [0, 2] [5, 7] [8, 12]
        rt.remove(2, 3);
        assert_eq!(8, rt.get_space());
        assert_eq!(3, rt.root.get_count());

        let rs = rt.find_contained(5, 1);
        assert!(rs.is_some());
        assert_eq!((5, 7), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove [8, 10] expect [0, 2] [5, 7] [10, 12]
        rt.remove(8, 2);
        assert_eq!(6, rt.get_space());
        assert_eq!(3, rt.root.get_count());

        let rs = rt.find_contained(10, 1);
        assert!(rs.is_some());
        assert_eq!((10, 12), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove [0, 2] expect [5, 7] [10, 12]
        rt.remove(0, 2);
        assert_eq!(4, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(5, 1);
        assert!(rs.is_some());
        assert_eq!((5, 7), rs.unwrap().borrow().get_range());
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
        assert_eq!(4, rt.root.get_count());

        fn cb_print(rs: &RangeSegRef) {
            println!("walk callback cb_print range_seg:{:?}", rs);
        }

        rt.walk(cb_print);
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
        assert_eq!(1, rt.root.get_count());

        // remove [7, 10] expect [0, 7] [10, 15]
        rt.remove_and_split(7, 3);
        assert_eq!(12, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 15), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove right over [13, 18] expect [0, 7] [10, 13]
        rt.remove_and_split(13, 5);
        assert_eq!(10, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 13), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove nothing [9, 10] expect [0, 7] [10, 13]
        assert!(!rt.remove_and_split(9, 1));
        assert_eq!(10, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((10, 13), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove left over [9, 11] expect [0, 7] [11, 13]
        rt.remove_and_split(9, 2);
        assert_eq!(9, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((11, 13), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove [6, 12] expect [0, 6] [12, 13]
        rt.remove_and_split(6, 6);
        assert_eq!(7, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(0, 5);
        assert!(rs.is_some());
        assert_eq!((0, 6), rs.unwrap().borrow().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove2() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove left over and right over [0, 20] expect []
        rt.remove_and_split(0, 20);
        assert_eq!(0, rt.get_space());
        assert_eq!(0, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_none());
        rt.validate();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().borrow().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove3() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().borrow().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().borrow().get_range());
        rt.validate();

        // add [49, 64]
        rt.add(49, 15);
        assert_eq!(45, rt.get_space());
        assert_eq!(3, rt.root.get_count());

        let rs = rt.find_contained(50, 1);
        assert!(rs.is_some());
        assert_eq!((49, 64), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove left over and right over [6, 56] expect [1, 6] [56, 64]
        rt.remove_and_split(6, 50);
        assert_eq!(13, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(58, 1);
        assert!(rs.is_some());
        assert_eq!((56, 64), rs.unwrap().borrow().get_range());
        rt.validate();

        let rs = rt.find_contained(3, 1);
        assert!(rs.is_some());
        assert_eq!((1, 6), rs.unwrap().borrow().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove4() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().borrow().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove right over [6, 56] expect [1, 6]
        rt.remove_and_split(6, 50);
        assert_eq!(5, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(3, 1);
        assert!(rs.is_some());
        assert_eq!((1, 6), rs.unwrap().borrow().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_remove5() {
        let mut rt = RangeTreeSimple::new();

        // add [1, 16]
        rt.add(1, 15);
        assert_eq!(15, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(11, 1);
        assert!(rs.is_some());
        assert_eq!((1, 16), rs.unwrap().borrow().get_range());
        rt.validate();

        // add [33, 48]
        rt.add(33, 15);
        assert_eq!(30, rt.get_space());
        assert_eq!(2, rt.root.get_count());

        let rs = rt.find_contained(40, 1);
        assert!(rs.is_some());
        assert_eq!((33, 48), rs.unwrap().borrow().get_range());
        rt.validate();

        // remove left over [0, 40] expect [40, 48]
        rt.remove_and_split(0, 40);
        assert_eq!(8, rt.get_space());
        assert_eq!(1, rt.root.get_count());

        let rs = rt.find_contained(42, 1);
        assert!(rs.is_some());
        assert_eq!((40, 48), rs.unwrap().borrow().get_range());
        rt.validate();
    }

    #[test]
    fn range_tree_stats() {
        let mut rt = RangeTreeSimple::new();
        rt.enable_stats();

        rt.add(0, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(4 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(8 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(12 * 1024, 4 * 1024);

        assert_eq!(0, rt.small_count);
        assert_eq!(1, rt.middle_count);
        rt.add(16 * 1024, 8 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(24 * 1024, 8 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(32 * 1024, 16 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(48 * 1024, 16 * 1024);

        assert_eq!(0, rt.middle_count);
        assert_eq!(1, rt.large_count);

        rt.add(1048 * 1024, 16 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(1032 * 1024, 16 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(1024 * 1024, 8 * 1024);
        assert_eq!(1, rt.middle_count);
        rt.add(1016 * 1024, 8 * 1024);
        assert_eq!(1, rt.middle_count);

        rt.add(1000 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(1004 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(1008 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        rt.add(1012 * 1024, 4 * 1024);
        assert_eq!(0, rt.small_count);
        assert_eq!(0, rt.middle_count);
        assert_eq!(2, rt.large_count);

        rt.remove(16 * 1024, 4 * 1024);
        assert_eq!(2, rt.middle_count);
        assert_eq!(1, rt.large_count);

        rt.remove(32 * 1024, 4 * 1024);
        assert_eq!(1, rt.small_count);
        assert_eq!(2, rt.middle_count);

        rt.remove(1060 * 1024, 4 * 1024);
        assert_eq!(3, rt.middle_count);
        assert_eq!(0, rt.large_count);

        rt.remove(1000 * 1024, 4 * 1024);
        assert_eq!(3, rt.middle_count);
    }

    // Test RangeTreeOps
    pub struct TestAllocator {
        size_tree: AvlTree<RangeSeg>,
    }

    impl TestAllocator {
        pub fn new() -> Self {
            let off_ext = offset_of!(RangeSeg, ext_node);
            TestAllocator { size_tree: AvlTree::<RangeSeg>::new(off_ext) }
        }
    }

    impl Drop for TestAllocator {
        fn drop(&mut self) {
            println!("drop test allocator");
        }
    }

    impl RangeTreeOps for TestAllocator {
        fn op_add(&mut self, rs: RangeSegRef) {
            self.size_tree.add(rs, size_tree_insert_cmp);
        }

        fn op_remove(&mut self, rs: &RangeSegRef) {
            self.size_tree.remove(&rs);
        }
    }

    #[test]
    fn range_tree_ops() {
        // TODO test allocator sie tree
        let a = TestAllocator::new();
        {
            let mut ms_tree = RangeTree::<TestAllocator>::new();
            ms_tree.set_ops(a);

            assert!(ms_tree.find(0, 10).is_none());
            assert_eq!(0, ms_tree.get_space());

            ms_tree.add(0, 100);
            assert_eq!(100, ms_tree.get_space());
            assert_eq!(1, ms_tree.get_count());

            let rs = ms_tree.find_contained(0, 1);
            assert!(rs.is_some());
            assert_eq!((0, 100), rs.as_ref().unwrap().borrow().get_range());

            assert_eq!(3, Arc::strong_count(&rs.as_ref().unwrap().0));

            ms_tree.remove(0, 100);
            assert_eq!(0, ms_tree.get_space());
            assert_eq!(0, ms_tree.get_count());

            assert_eq!(1, Arc::strong_count(&rs.as_ref().unwrap().0));
        }
        println!("out")
    }

    //    #[test]
    //    fn range_tree_memleak() {
    //        use std::time::Duration;
    //        loop {
    //            for _i in 0..1000 {
    //                let mut rt = RangeTreeSimple::new();
    //                for i in (0..1000).step_by(3) {
    //                    rt.add(i, 1);
    //                }
    //                let mut free_args = Vec::<u64>::new();
    //                let cb = |rs: &RangeSegRef| {
    //                    free_args.push(rs.end - rs.start);
    //                };
    //                rt.walk(cb);
    //            }
    //            println!("sleep");
    //            std::thread::sleep(Duration::from_secs(1));
    //        }
    //    }
}
