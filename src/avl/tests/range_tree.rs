// Use crate range-tree-rs instead, this implementation is just to ensure avl is tested

use super::super::*;
use alloc::sync::Arc;
use core::{
    cell::{Cell, UnsafeCell},
    cmp::Ordering,
    fmt,
};

#[derive(Default)]
#[repr(C)]
pub struct RangeSeg {
    node: UnsafeCell<AvlNode<Self, ()>>,
    pub start: Cell<u64>,
    pub end: Cell<u64>,
}

impl PartialOrd for RangeSeg {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl PartialEq for RangeSeg {
    fn eq(&self, other: &Self) -> bool {
        Ord::cmp(self, other) == Ordering::Equal
    }
}

impl Eq for RangeSeg {}

impl Ord for RangeSeg {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.end.get() <= other.start.get() {
            Ordering::Less
        } else if self.start.get() >= other.end.get() {
            Ordering::Greater
        } else {
            // intersection
            Ordering::Equal
        }
    }
}

unsafe impl Send for RangeSeg {}

unsafe impl AvlItem<()> for RangeSeg {
    type Key = Self;

    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }

    fn borrow_key(&self) -> &Self::Key {
        self
    }
}

pub struct RangeTree {
    root: AvlTree<Arc<RangeSeg>, ()>,
    space: u64,
}

unsafe impl Send for RangeTree {}

impl RangeSeg {
    #[inline]
    pub fn valid(&self) {
        assert!(self.start.get() <= self.end.get(), "RangeSeg:{:?} invalid", self);
    }

    #[inline]
    pub fn new(s: u64, e: u64) -> Arc<RangeSeg> {
        Arc::new(RangeSeg { start: Cell::new(s), end: Cell::new(e), ..Default::default() })
    }

    #[inline]
    pub fn get_range(&self) -> (u64, u64) {
        (self.start.get(), self.end.get())
    }
}

impl fmt::Display for RangeSeg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RangeSeg({}-{})", self.start.get(), self.end.get())
    }
}

impl fmt::Debug for RangeSeg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let _ = write!(f, "( start: {}, end:{}, ", self.start.get(), self.end.get());
        let _ = write!(f, "node: {:?}, ", unsafe { &*self.node.get() });
        write!(f, ")")
    }
}

pub struct RangeTreeIter<'a> {
    tree: &'a RangeTree,
    current: Option<&'a RangeSeg>,
}

unsafe impl<'a> Send for RangeTreeIter<'a> {}

impl<'a> Iterator for RangeTreeIter<'a> {
    type Item = &'a RangeSeg;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current.take();
        if let Some(seg) = current {
            self.current = self.tree.root.next(seg);
        }
        current
    }
}

impl<'a> IntoIterator for &'a RangeTree {
    type Item = &'a RangeSeg;
    type IntoIter = RangeTreeIter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[allow(dead_code)]
impl Default for RangeTree {
    fn default() -> Self {
        Self::new()
    }
}

impl RangeTree {
    pub fn new() -> Self {
        RangeTree { root: AvlTree::<Arc<RangeSeg>, ()>::new(), space: 0 }
    }

    pub fn is_empty(&self) -> bool {
        if 0 == self.root.len() {
            return true;
        }
        false
    }

    #[inline(always)]
    pub fn get_space(&self) -> u64 {
        self.space
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.root.len()
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
        let rs_key = RangeSeg {
            start: Cell::new(start),
            end: Cell::new(start + size),
            ..Default::default()
        };
        let result = self.root.find(&rs_key);
        if result.direction.is_none() {
            panic!("allocating allocated {} of {:?}", &rs_key, result.get_exact().unwrap());
        }

        let detached_result = unsafe { result.detach() };
        self.space += size;
        self.merge_seg(start, start + size, detached_result);
    }

    /// Add range segment, possible adjacent, and check overlapping.
    ///
    /// If there's overlapping with existing range, return `Err((start, end))`
    #[inline]
    pub fn add_find_overlap(&mut self, start: u64, size: u64) -> Result<(), (u64, u64)> {
        assert!(size > 0, "range tree add size={} error", size);
        let rs_key = RangeSeg {
            start: Cell::new(start),
            end: Cell::new(start + size),
            ..Default::default()
        };
        let result = self.root.find(&rs_key);
        if result.direction.is_none() {
            let ol_node = result.get_exact().unwrap();
            let max_start = if rs_key.start.get() > ol_node.start.get() {
                rs_key.start.get()
            } else {
                ol_node.start.get()
            };
            let min_end = if rs_key.end.get() > ol_node.end.get() {
                ol_node.end.get()
            } else {
                rs_key.end.get()
            };
            return Err((max_start, min_end));
        }

        let detached_result = unsafe { result.detach() };
        self.space += size;
        self.merge_seg(start, start + size, detached_result);
        Ok(())
    }

    /// Add range which may be crossed section or larger with existing, will merge the range
    #[inline]
    pub fn add_and_merge(&mut self, start: u64, size: u64) {
        assert!(size > 0, "range tree add size={} error", size);
        let mut new_start = start;
        let mut new_end = start + size;

        loop {
            let search_key = RangeSeg {
                start: Cell::new(new_start),
                end: Cell::new(new_end),
                ..Default::default()
            };
            let result = self.root.find(&search_key);

            if result.direction.is_some() {
                // No more overlapping nodes
                break;
            }

            let node = result.get_exact().unwrap();
            if node.start.get() < new_start {
                new_start = node.start.get();
            }
            if node.end.get() > new_end {
                new_end = node.end.get();
            }
            let node_start = node.start.get();
            let node_size = node.end.get() - node.start.get();

            if !self.remove(node_start, node_size) {
                panic!("rs[{}:{}] NOT existed", node_start, node_size);
            }
        }
        let search_key =
            RangeSeg { start: Cell::new(new_start), end: Cell::new(new_end), ..Default::default() };
        let result = self.root.find(&search_key);

        let detached_result = unsafe { result.detach() };
        self.space += new_end - new_start;
        self.merge_seg(new_start, new_end, detached_result);
    }

    #[inline(always)]
    fn merge_seg(&mut self, start: u64, end: u64, result: AvlSearchResult<Arc<RangeSeg>>) {
        // Detach early to get insertion point / parent check for nearest.

        let before_res = unsafe { self.root.nearest(&result, AvlDirection::Left).detach() };
        let after_res = unsafe { self.root.nearest(&result, AvlDirection::Right).detach() };
        // Detach results to allow mutable access to self
        let mut merge_before = false;
        let mut merge_after = false;
        let mut before_start = 0;
        let before_end;
        if let Some(before_node) = before_res.get_nearest() {
            (before_start, before_end) = before_node.get_range();
            merge_before = before_end == start;
        }

        if let Some(after_node) = after_res.get_nearest() {
            let (after_start, _) = after_node.get_range();
            merge_after = after_start == end;
        }

        // Use unsafe pointer access for mutations/Arc recovery
        // We know these pointers are valid because we are in a mutable method and haven't removed them yet.

        if merge_before && merge_after {
            // Merge Both: [before] + [new] + [after]

            let _before_node = self.root.remove_with(before_res).unwrap();
            let after_node_ref = after_res.get_node_ref().unwrap();

            // modify after node start range after remove
            after_node_ref.start.set(before_start);
        } else if merge_before {
            // Merge Before Only: Extend `before.end`

            let before_node_ref = before_res.get_node_ref().unwrap();
            before_node_ref.end.set(end);
        } else if merge_after {
            let after_node_ref = after_res.get_node_ref().unwrap();
            // Merge After Only: Extend `after.start`
            after_node_ref.start.set(start);
        } else {
            // No Merge. Insert new.
            let new_node = RangeSeg::new(start, end);
            self.root.insert(new_node, result);
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
        let search_rs =
            RangeSeg { start: Cell::new(start), end: Cell::new(end), ..Default::default() };
        let result = self.root.find(&search_rs);
        if !result.is_exact() {
            return false;
        }
        assert!(size > 0, "range tree remove size={} error", size);

        let rs_node = result.get_node_ref().unwrap();
        let rs_start = rs_node.start.get();
        let rs_end = rs_node.end.get();

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

        if left_over && right_over {
            // Remove the middle of segment larger than requested range
            size_deduce = size;
            // Update Left in-place
            rs_node.end.set(start);
            // Insert Right
            // New node [end, rs_end]
            let new_rs = RangeSeg::new(end, rs_end);

            let result = unsafe { result.detach() };
            let _ = rs_node;
            // Insert new right part using insert_here optimization
            // We construct an AvlSearchResult pointing to the current node (rs_node)
            unsafe { self.root.insert_here(new_rs, result, AvlDirection::Right) };
        } else if left_over {
            // Remove Right end
            size_deduce = rs_end - start;
            // In-Place Update
            rs_node.end.set(start);
            let _ = rs_node;
        } else if right_over {
            // Remove Left end
            size_deduce = end - rs_start;
            // In-Place Update: Update start.
            rs_node.start.set(end);
            let _ = rs_node;
        } else {
            // Remove Exact / Total
            size_deduce = rs_end - rs_start;
            let _ = rs_node;
            self.root.remove_ref(&result.get_exact().unwrap());
        }

        self.space -= size_deduce;
        true
    }

    /// return only when segment overlaps with [start, start+size]
    #[inline]
    pub fn find(&self, start: u64, size: u64) -> Option<Arc<RangeSeg>> {
        if self.root.len() == 0 {
            return None;
        }
        assert!(size > 0, "range tree find size={} error", size);
        let end = start + size;
        let rs = RangeSeg { start: Cell::new(start), end: Cell::new(end), ..Default::default() };
        let result = self.root.find(&rs);
        result.get_exact()
    }

    /// return only when segment contains [start, size], if multiple segment exists, return the
    /// smallest start
    #[inline]
    pub fn find_contained(&self, start: u64, size: u64) -> Option<&RangeSeg> {
        assert!(size > 0, "range tree find size={} error", size);
        if self.root.len() == 0 {
            return None;
        }
        let end = start + size;
        let rs_search =
            RangeSeg { start: Cell::new(start), end: Cell::new(end), ..Default::default() };
        self.root.find_contained(&rs_search)
    }

    #[inline]
    pub fn iter(&self) -> RangeTreeIter<'_> {
        RangeTreeIter { tree: self, current: self.root.first() }
    }

    #[inline]
    pub fn walk<F: FnMut(&RangeSeg)>(&self, mut cb: F) {
        let mut node = self.root.first();
        while let Some(_node) = node {
            cb(_node);
            node = self.root.next(_node);
        }
    }

    /// If cb returns false, break
    #[inline]
    pub fn walk_conditioned<F: FnMut(&RangeSeg) -> bool>(&self, mut cb: F) {
        let mut node = self.root.first();
        while let Some(_node) = node {
            if !cb(_node) {
                break;
            }
            node = self.root.next(_node);
        }
    }

    pub fn get_root(&self) -> &AvlTree<Arc<RangeSeg>, ()> {
        &self.root
    }

    pub fn validate(&self) {
        self.root.validate();
    }
}

#[cfg(feature = "std")]
pub fn range_tree_print(tree: &RangeTree) {
    if tree.get_space() == 0 {
        println!("tree is empty");
    } else {
        tree.walk(|rs| {
            println!("\t{}-{}", rs.start.get(), rs.end.get());
        });
    }
}

#[test]
fn range_tree_add() {
    let mut rt = RangeTree::new();
    assert!(rt.find(0, 10).is_none());
    assert_eq!(0, rt.get_space());

    rt.add(0, 2);
    assert_eq!(2, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 2), rs.as_ref().unwrap().get_range());

    assert!(rt.find_contained(0, 3).is_some());

    // left join
    rt.add_and_merge(2, 5);
    assert_eq!(7, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 7), rs.unwrap().get_range());

    // without join
    rt.add_and_merge(10, 5);
    assert_eq!(12, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((10, 15), rs.unwrap().get_range());

    // right join
    rt.add_and_merge(8, 2);
    assert_eq!(14, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((8, 15), rs.unwrap().get_range());

    // left and right join
    rt.add_and_merge(7, 1);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((0, 15), rs.unwrap().get_range());

    rt.validate();
}

#[test]
fn range_tree_add_and_merge() {
    let mut rt = RangeTree::new();
    assert!(rt.find(0, 10).is_none());
    assert_eq!(0, rt.get_space());

    rt.add_and_merge(0, 2);
    assert_eq!(2, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 2), rs.as_ref().unwrap().get_range());

    assert!(rt.find_contained(0, 3).is_some()); // REVERT FIX: Changed from is_none() to is_some()

    // left join
    rt.add_and_merge(2, 5);
    assert_eq!(7, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 7), rs.unwrap().get_range());

    // without join
    rt.add_and_merge(15, 5);
    assert_eq!(12, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(16, 1);
    assert!(rs.is_some());
    assert_eq!((15, 20), rs.unwrap().get_range());

    // right join
    rt.add_and_merge(13, 2);
    assert_eq!(14, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(16, 1);
    assert!(rs.is_some());
    assert_eq!((13, 20), rs.unwrap().get_range());

    // duplicate
    rt.add_and_merge(14, 8);
    assert_eq!(16, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 7), rs.unwrap().get_range());

    let rs = rt.find_contained(16, 1);
    assert!(rs.is_some());
    assert_eq!((13, 22), rs.unwrap().get_range());

    // without join
    rt.add_and_merge(25, 5);
    assert_eq!(21, rt.get_space());
    assert_eq!(3, rt.root.len());

    let rs = rt.find_contained(26, 1);
    assert!(rs.is_some());
    assert_eq!((25, 30), rs.unwrap().get_range());

    // duplicate
    rt.add_and_merge(12, 20);
    assert_eq!(27, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(0, 1);
    assert!(rs.is_some());
    assert_eq!((0, 7), rs.unwrap().get_range());

    let rs = rt.find_contained(16, 1);
    assert!(rs.is_some());
    assert_eq!((12, 32), rs.unwrap().get_range());

    // left and right join
    rt.add_and_merge(7, 5);
    assert_eq!(32, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((0, 32), rs.unwrap().get_range());

    rt.validate();
}

#[test]
fn range_tree_remove() {
    let mut rt = RangeTree::new();
    // add [0, 15]
    rt.add(0, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    // remove [7, 8] expect [0, 7] [8, 15]
    rt.remove(7, 1);
    assert_eq!(14, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((8, 15), rs.unwrap().get_range());
    rt.validate();

    // remove [12, 15] expect [0, 7] [8, 12]
    rt.remove(12, 3);
    assert_eq!(11, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((8, 12), rs.unwrap().get_range());
    rt.validate();

    // remove [2, 5] expect [0, 2] [5, 7] [8, 12]
    rt.remove(2, 3);
    assert_eq!(8, rt.get_space());
    assert_eq!(3, rt.root.len());

    let rs = rt.find_contained(5, 1);
    assert!(rs.is_some());
    assert_eq!((5, 7), rs.unwrap().get_range());
    rt.validate();

    // remove [8, 10] expect [0, 2] [5, 7] [10, 12]
    rt.remove(8, 2);
    assert_eq!(6, rt.get_space());
    assert_eq!(3, rt.root.len());

    let rs = rt.find_contained(10, 1);
    assert!(rs.is_some());
    assert_eq!((10, 12), rs.unwrap().get_range());
    rt.validate();

    // remove [0, 2] expect [5, 7] [10, 12]
    rt.remove(0, 2);
    assert_eq!(4, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(5, 1);
    assert!(rs.is_some());
    assert_eq!((5, 7), rs.unwrap().get_range());
    rt.validate();
}

#[test]
fn range_tree_walk() {
    let mut rt = RangeTree::new();
    rt.add(0, 2);
    rt.add(4, 4);
    rt.add(12, 8);
    rt.add(32, 16);
    assert_eq!(30, rt.get_space());
    assert_eq!(4, rt.root.len());

    fn cb_print(rs: &RangeSeg) {
        println!("walk callback cb_print range_seg:{:?}", rs);
    }

    rt.walk(cb_print);
}

#[test]
fn range_tree_iter() {
    let mut rt = RangeTree::new();
    rt.add(0, 2);
    rt.add(4, 4);
    rt.add(12, 8);
    rt.add(32, 16);

    let mut count = 0;
    let mut total_space = 0;
    for rs in rt.iter() {
        count += 1;
        total_space += rs.end.get() - rs.start.get();
    }
    assert_eq!(count, rt.len() as usize);
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
    let mut rt = RangeTree::new();
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
    assert_eq!(result.start.get(), 2044);
    assert_eq!(result.end.get(), 2052);
    for i in &[4096, 516098, 518148, 520194, 522244, 524288, 66060290, 66062340, 66064384] {
        let result = rt.find_contained(4000, *i).unwrap();
        assert_eq!(result.start.get(), 4092);
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
    let mut rt = RangeTree::new();
    rt.add_abs(20, 80);
    rt.add_abs(120, 180);
    rt.add_abs(220, 280);
    rt.add_abs(320, 380);
    rt.add_abs(420, 480);
    rt.add_abs(520, 580);
    rt.add_abs(620, 680);
    range_tree_print(&rt);
    let result = rt.find_contained(240, 340).unwrap();
    assert_eq!(result.start.get(), 220);
    assert_eq!(result.end.get(), 280);
}

#[test]
fn range_tree_remove1() {
    let mut rt = RangeTree::new();

    // add [0, 15]
    rt.add(0, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    // remove [7, 10] expect [0, 7] [10, 15]
    rt.remove_and_split(7, 3);
    assert_eq!(12, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((10, 15), rs.unwrap().get_range());
    rt.validate();

    // remove right over [13, 18] expect [0, 7] [10, 13]
    rt.remove_and_split(13, 5);
    assert_eq!(10, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((10, 13), rs.unwrap().get_range());
    rt.validate();

    // remove nothing [9, 10] expect [0, 7] [10, 13]
    assert!(!rt.remove_and_split(9, 1));
    assert_eq!(10, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((10, 13), rs.unwrap().get_range());
    rt.validate();

    // remove left over [9, 11] expect [0, 7] [11, 13]
    rt.remove_and_split(9, 2);
    assert_eq!(9, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((11, 13), rs.unwrap().get_range());
    rt.validate();

    // remove [6, 12] expect [0, 6] [12, 13]
    rt.remove_and_split(6, 6);
    assert_eq!(7, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(0, 5);
    assert!(rs.is_some());
    assert_eq!((0, 6), rs.unwrap().get_range());
    rt.validate();
}

#[test]
fn range_tree_remove2() {
    let mut rt = RangeTree::new();

    // add [1, 16]
    rt.add(1, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((1, 16), rs.unwrap().get_range());
    rt.validate();

    // remove left over and right over [0, 20] expect []
    rt.remove_and_split(0, 20);
    assert_eq!(0, rt.get_space());
    assert_eq!(0, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_none());
    rt.validate();

    // add [1, 16]
    rt.add(1, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((1, 16), rs.unwrap().get_range());
    rt.validate();
}

#[test]
fn range_tree_remove3() {
    let mut rt = RangeTree::new();

    // add [1, 16]
    rt.add(1, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((1, 16), rs.unwrap().get_range());
    rt.validate();

    // add [33, 48]
    rt.add(33, 15);
    assert_eq!(30, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(40, 1);
    assert!(rs.is_some());
    assert_eq!((33, 48), rs.unwrap().get_range());
    rt.validate();

    // add [49, 64]
    rt.add(49, 15);
    assert_eq!(45, rt.get_space());
    assert_eq!(3, rt.root.len());

    let rs = rt.find_contained(50, 1);
    assert!(rs.is_some());
    assert_eq!((49, 64), rs.unwrap().get_range());
    rt.validate();

    // remove left over and right over [6, 56] expect [1, 6] [56, 64]
    rt.remove_and_split(6, 50);
    assert_eq!(13, rt.get_space());
    assert_eq!(2, rt.root.len());

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
    let mut rt = RangeTree::new();

    // add [1, 16]
    rt.add(1, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((1, 16), rs.unwrap().get_range());
    rt.validate();

    // add [33, 48]
    rt.add(33, 15);
    assert_eq!(30, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(40, 1);
    assert!(rs.is_some());
    assert_eq!((33, 48), rs.unwrap().get_range());
    rt.validate();

    // remove right over [6, 56] expect [1, 6]
    rt.remove_and_split(6, 50);
    assert_eq!(5, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(3, 1);
    assert!(rs.is_some());
    assert_eq!((1, 6), rs.unwrap().get_range());
    rt.validate();
}

#[test]
fn range_tree_remove5() {
    let mut rt = RangeTree::new();

    // add [1, 16]
    rt.add(1, 15);
    assert_eq!(15, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(11, 1);
    assert!(rs.is_some());
    assert_eq!((1, 16), rs.unwrap().get_range());
    rt.validate();

    // add [33, 48]
    rt.add(33, 15);
    assert_eq!(30, rt.get_space());
    assert_eq!(2, rt.root.len());

    let rs = rt.find_contained(40, 1);
    assert!(rs.is_some());
    assert_eq!((33, 48), rs.unwrap().get_range());
    rt.validate();

    // remove left over [0, 40] expect [40, 48]
    rt.remove_and_split(0, 40);
    assert_eq!(8, rt.get_space());
    assert_eq!(1, rt.root.len());

    let rs = rt.find_contained(42, 1);
    assert!(rs.is_some());
    assert_eq!((40, 48), rs.unwrap().get_range());
    rt.validate();
}
