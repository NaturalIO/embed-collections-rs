mod api;
mod borrow;
mod inter;
mod leaf;
mod merge;
mod split;

use crate::btree::{BTreeMap, BTreeState};

/// Test stats implementation for tracking node counts
#[derive(Default, Debug)]
pub struct TestStats {
    pub leaf_count: usize,
    pub inter_count: usize,
}

impl TestStats {
    pub fn new() -> Self {
        Self { leaf_count: 0, inter_count: 0 }
    }
    pub fn with_counts(leaf_count: usize, inter_count: usize) -> Self {
        Self { leaf_count, inter_count }
    }
    pub fn total(&self) -> usize {
        self.leaf_count + self.inter_count
    }
}

impl<K, V> BTreeState<K, V> for TestStats {
    fn on_leaf_alloc(&mut self) {
        self.leaf_count += 1;
    }
    fn on_leaf_dealloc(&mut self) {
        self.leaf_count = self.leaf_count.saturating_sub(1);
    }
    fn on_inter_alloc(&mut self) {
        self.inter_count += 1;
    }
    fn on_inter_merge(&mut self, delta: usize) {
        self.inter_count = self.inter_count.saturating_sub(delta);
    }
    fn on_leaf_split(&mut self) {
        self.leaf_count += 1;
    }
    fn on_leaf_merge(&mut self, delta: usize) {
        self.leaf_count = self.leaf_count.saturating_sub(delta);
    }
    fn on_inter_split(&mut self) {
        self.inter_count += 1;
    }
    fn leaf_count(&self) -> usize {
        self.leaf_count
    }
    fn inter_count(&self) -> usize {
        self.inter_count
    }
}

/// Type alias for BTreeMap with TestStats
pub type TestBTreeMap<K, V> = BTreeMap<K, V, TestStats>;

/// Macro to create a TestBTreeMap with manual field initialization
#[macro_export]
macro_rules! test_btree_map {
    ($root:expr, $len:expr) => {{
        use crate::btree::PathCache;
        use crate::btree::tests::TestStats;
        use core::cell::UnsafeCell;
        $crate::btree::BTreeMap {
            root: $root,
            len: $len,
            cache: UnsafeCell::new(PathCache::new()),
            state: UnsafeCell::new(TestStats::new()),
        }
    }};
}
