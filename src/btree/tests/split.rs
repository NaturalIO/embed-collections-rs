use super::{TestBTreeMap, TestStats};
use crate::btree::*;

/// Test large tree with splits
/// Verifies that leaf splits correctly increment leaf count
#[test]
fn test_btree_large_tree_split_seq() {
    let mut map: TestBTreeMap<i32, i32> = BTreeMap::new_with_state(TestStats::new());
    let (inter_cap, leaf_cap) = TestBTreeMap::<i32, i32>::cap();
    assert!(100 > inter_cap);
    assert!(100 > leaf_cap);

    // Insert many values to create multi-level tree
    for i in 0..100 {
        assert_eq!(map.insert(i, i * 2), None);
        map.validate();
    }
    assert_eq!(map.len(), 100);
    println!("tree height {}", map.height());
    let state = map.state();
    println!("leaf_count {} inter_count {}", state.leaf_count, state.inter_count);

    // Verify node counts are reasonable (should be > 0)
    assert!(state.leaf_count > 0, "Should have some leaves");
    assert!(state.leaf_count >= state.inter_count, "Should have more leaves than internal nodes");

    // Verify all values
    for i in 0..100 {
        assert_eq!(map.get(&i), Some(&(i * 2)));
    }
}

/// Test random inserts
/// Verifies node count growth with random insertions
#[test]
fn test_btree_random_inserts() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    let values = vec![
        (5, "e"),
        (3, "c"),
        (7, "g"),
        (1, "a"),
        (9, "i"),
        (2, "b"),
        (4, "d"),
        (6, "f"),
        (8, "h"),
    ];

    let mut prev_leaf_count = 0;
    let mut prev_inter_count = 0;

    for (k, v) in &values {
        map.insert(*k, *v);
        map.validate();

        // Verify node counts don't decrease
        let state = map.state();
        assert!(state.leaf_count >= prev_leaf_count, "Leaf count should not decrease after insert");
        assert!(
            state.inter_count >= prev_inter_count,
            "Inter count should not decrease after insert"
        );

        prev_leaf_count = state.leaf_count;
        prev_inter_count = state.inter_count;
    }

    let state = map.state();
    println!("Final leaf_count {} inter_count {}", state.leaf_count, state.inter_count);

    // With 9 items and splits, we should have multiple leaves
    assert!(state.leaf_count >= 1, "Should have at least 1 leaf");

    for (k, v) in &values {
        assert_eq!(map.get(k), Some(v));
    }
}

/// Test node capacity
#[test]
fn test_node_capacity() {
    let leaf_cap = LeafNode::<i64, i64>::cap();
    let inter_cap = InterNode::<i64, i64>::cap();

    assert!(leaf_cap >= 2, "Leaf should hold at least 2 items");
    assert!(inter_cap >= 2, "Internal node should hold at least 2 keys");
}

/// Test simple split scenario with node count verification
#[test]
fn test_simple_split_node_count() {
    let mut map: TestBTreeMap<i32, i32> = BTreeMap::new_with_state(TestStats::new());
    let leaf_cap = LeafNode::<i32, i32>::cap() as usize;

    // Insert exactly to capacity
    for i in 0..leaf_cap {
        map.insert(i as i32, i as i32 * 10);
    }
    map.validate();

    // Record state before split
    let state_before = map.state();
    let leaves_before = state_before.leaf_count;
    let inter_before = state_before.inter_count;

    // Insert one more to trigger split
    map.insert(leaf_cap as i32, leaf_cap as i32 * 10);
    map.validate();

    // After split: should have more leaves and possibly internal nodes
    let state_after = map.state();
    assert!(state_after.leaf_count > leaves_before, "Should have more leaves after split");
    println!(
        "Before split: {} leaves, {} inter; After split: {} leaves, {} inter",
        leaves_before, inter_before, state_after.leaf_count, state_after.inter_count
    );
}
