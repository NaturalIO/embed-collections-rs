use super::*;
use captains_log::logfn;
use rstest::rstest;
use std::println;

// =============================================================================
// Direct handle_inter_underflow Tests
// =============================================================================
// These tests directly call handle_inter_underflow to verify its behavior
// in complex tree structures without going through the remove() interface.
// This allows testing specific edge cases that are hard to trigger naturally.
// =============================================================================

/// Test: Handle internal node underflow with left merge (loop once internally)
///
/// Tree structure before:
///   root(h=2) -> [internal_a | key | internal_b]
///   internal_a(h=1) -> [leaf_1 | key | leaf_2]  <- target node, key_count=1
///   internal_b(h=1) -> [leaf_3 | key | leaf_4]  <- left sibling with space
///
/// After merge:
///   root(h=2) -> [internal_a] (key_count=1, needs another merge)
///   internal_a(h=1) -> merged with internal_b
///
/// Key test: Verifies handle_inter_underflow when merging internal_a with right sibling internal_b
/// causes parent to collapse (loop once).
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_merge_right_height_3_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create leaves for internal_a (target node)
        let mut leaf_1 = builder.new_leaf();
        let mut leaf_2 = builder.new_leaf();

        // Create leaves for internal_b (left sibling)
        let mut leaf_3 = builder.new_leaf();
        let mut leaf_4 = builder.new_leaf();

        // Fill leaves with minimal data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
            builder.insert_leaf(
                &mut leaf_2,
                CounterI32::new((10 + i) * 2),
                CounterI32::new((10 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_3,
                CounterI32::new((20 + i) * 2),
                CounterI32::new((20 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_4,
                CounterI32::new((30 + i) * 2),
                CounterI32::new((30 + i) * 10),
            );
        }

        let leaf_1_first = leaf_1.get_keys()[0].clone();
        let leaf_2_first = leaf_2.get_keys()[0].clone();
        let leaf_3_first = leaf_3.get_keys()[0].clone();

        // Create internal_a (height=1) with key_count=1 (target node)
        let mut internal_a = builder.new_inter(1);
        internal_a.set_left_ptr(leaf_1.get_ptr_mut());
        internal_a.insert_no_split(leaf_2_first, leaf_2.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 1);

        // Create internal_b (height=1) with key_count=1 (left sibling with space)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_3.get_ptr_mut());
        internal_b.insert_no_split(leaf_4.get_keys()[0].clone(), leaf_4.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 1);

        // Create root (height=2) with key_count=1
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_a.get_ptr_mut());
        root.insert_no_split(leaf_3_first, internal_b.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 1);

        // Record alive count before underflow handling
        let alive_before = alive_count();
        println!("Alive count before handle_inter_underflow: {}", alive_before);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 12);
        map.validate();
        //map.dump();
        assert_eq!(map.height(), 3);

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        let _ = map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, &leaf_1_first);

        // Pop height=1 InterNode (internal_a) from cache
        let (popped_node, _) = cache.pop().unwrap();
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 1);
        assert_eq!(popped_node, internal_a);

        // Directly call handle_inter_underflow
        map.handle_inter_underflow(internal_a);

        // Verify tree structure is complete
        map.validate();

        // After merge: internal_a merged into internal_b
        assert_eq!(map.height(), 2, "Tree height should be 2 after merge");

        // Verify all data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
            assert!(
                map.contains_key(&CounterI32::new((10 + i) * 2)),
                "Key {} should exist",
                (10 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((20 + i) * 2)),
                "Key {} should exist",
                (20 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((30 + i) * 2)),
                "Key {} should exist",
                (30 + i) * 2
            );
        }
        //map.dump();
        // height collapse from 3 to 2
        assert_eq!(map.height(), 2);
        assert_eq!(map.leaf_count(), 4);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::InterMergeRight as u32);
    }
    // After map is dropped, all CounterI32 should be dropped
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Handle internal node underflow with right merge (loop once internally)
///
/// Tree structure before:
///   root(h=2) -> [internal_a | key | internal_b]
///   internal_a(h=1) -> [leaf_1 | key | leaf_2]  <- right sibling with space
///   internal_b(h=1) -> [leaf_3 | key | leaf_4]  <- target node, key_count=1
///
/// After merge:
///   root(h=2) -> [internal_a] (key_count=1, needs another merge)
///   internal_a(h=1) -> merged with internal_b
///
/// Key test: Verifies handle_inter_underflow when internal_b merging left sibling (internal_a)
/// causes parent to callaps
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_merge_left_height_3_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create leaves for internal_a (right sibling)
        let mut leaf_1 = builder.new_leaf();
        let mut leaf_2 = builder.new_leaf();

        // Create leaves for internal_b (target node)
        let mut leaf_3 = builder.new_leaf();
        let mut leaf_4 = builder.new_leaf();

        // Fill leaves with minimal data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
            builder.insert_leaf(
                &mut leaf_2,
                CounterI32::new((10 + i) * 2),
                CounterI32::new((10 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_3,
                CounterI32::new((20 + i) * 2),
                CounterI32::new((20 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_4,
                CounterI32::new((30 + i) * 2),
                CounterI32::new((30 + i) * 10),
            );
        }

        let _leaf_1_first = leaf_1.get_keys()[0].clone();
        let leaf_2_first = leaf_2.get_keys()[0].clone();
        let leaf_3_first = leaf_3.get_keys()[0].clone();

        // Create internal_a (height=1) with key_count=1 (right sibling with space)
        let mut internal_a = builder.new_inter(1);
        internal_a.set_left_ptr(leaf_1.get_ptr_mut());
        internal_a.insert_no_split(leaf_2_first, leaf_2.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 1);

        // Create internal_b (height=1) with key_count=1 (target node)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_3.get_ptr_mut());
        internal_b.insert_no_split(leaf_4.get_keys()[0].clone(), leaf_4.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 1);

        // Create root (height=2) with key_count=1
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_a.get_ptr_mut());
        root.insert_no_split(leaf_3_first, internal_b.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 1);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 12);
        map.validate();
        assert_eq!(map.height(), 3);
        //map.dump();

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        // Use a reference to leaf_3's first key for lookup
        let leaf_3_lookup = &leaf_3.get_keys()[0];
        let _ = map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, leaf_3_lookup);

        // Pop height=1 InterNode (internal_b) from cache
        let (popped_node, _) = cache.pop().unwrap();
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 1);
        assert_eq!(popped_node, internal_b);

        // Directly call handle_inter_underflow
        map.handle_inter_underflow(internal_b);

        // Verify tree structure is complete
        map.validate();

        assert_eq!(map.height(), 2, "Tree height should be 2 after merge");

        // Verify all data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
            assert!(
                map.contains_key(&CounterI32::new((10 + i) * 2)),
                "Key {} should exist",
                (10 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((20 + i) * 2)),
                "Key {} should exist",
                (20 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((30 + i) * 2)),
                "Key {} should exist",
                (30 + i) * 2
            );
        }
        //map.dump();
        // height collapse from 3 to 2
        assert_eq!(map.height(), 2);

        assert_eq!(map.leaf_count(), 4);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::InterMergeLeft as u32);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Handle internal node underflow with left merge (no cascade)
///
/// Tree structure:
///   root(h=2) -> [internal_a | key | internal_b | key | internal_c]
///   internal_a(h=1) -> [leaf_1 | key | leaf_2]  <- target node
///   internal_b(h=1) -> [leaf_3 | key | leaf_4]  <- left sibling with space
///   internal_c(h=1) -> [leaf_5 | key | leaf_6]
///
/// Key test: Verifies handle_inter_underflow when merging internal_a with left sibling (internal_b)
/// but parent has enough keys to not need merging (no internal loop).
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_merge_right_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create leaves for all internal nodes
        let mut leaf_1 = builder.new_leaf();
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();
        let mut leaf_4 = builder.new_leaf();
        let mut leaf_5 = builder.new_leaf();
        let mut leaf_6 = builder.new_leaf();

        // Fill leaves with minimal data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
            builder.insert_leaf(
                &mut leaf_2,
                CounterI32::new((10 + i) * 2),
                CounterI32::new((10 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_3,
                CounterI32::new((20 + i) * 2),
                CounterI32::new((20 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_4,
                CounterI32::new((30 + i) * 2),
                CounterI32::new((30 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_5,
                CounterI32::new((40 + i) * 2),
                CounterI32::new((40 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_6,
                CounterI32::new((50 + i) * 2),
                CounterI32::new((50 + i) * 10),
            );
        }

        let _leaf_1_first = leaf_1.get_keys()[0].clone();
        let leaf_2_first = leaf_2.get_keys()[0].clone();
        let leaf_3_first = leaf_3.get_keys()[0].clone();
        let leaf_4_first = leaf_4.get_keys()[0].clone();
        let leaf_5_first = leaf_5.get_keys()[0].clone();
        let leaf_6_first = leaf_6.get_keys()[0].clone();

        // Create internal_a (height=1) with key_count=1 (target node)
        let mut internal_a = builder.new_inter(1);
        internal_a.set_left_ptr(leaf_1.get_ptr_mut());
        internal_a.insert_no_split(leaf_2_first, leaf_2.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 1);

        // Create internal_b (height=1) with key_count=1 (left sibling with space)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_3.get_ptr_mut());
        internal_b.insert_no_split(leaf_4_first, leaf_4.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 1);

        // Create internal_c (height=1) with key_count=1
        let mut internal_c = builder.new_inter(1);
        internal_c.set_left_ptr(leaf_5.get_ptr_mut());
        internal_c.insert_no_split(leaf_6_first, leaf_6.get_ptr_mut());
        debug_assert_eq!(internal_c.key_count(), 1);

        // Create root (height=2) with key_count=2
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_a.get_ptr_mut());
        root.insert_no_split(leaf_3_first, internal_b.get_ptr_mut());
        root.insert_no_split(leaf_5_first, internal_c.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 2);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 18);
        map.validate();
        assert_eq!(map.height(), 3, "Tree height should remain 3");
        // map.dump();

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        let _ =
            map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, &leaf_1.get_keys()[0]);

        // Pop height=1 InterNode (internal_a) from cache
        let (popped_node, _) = cache.pop().unwrap();
        assert_eq!(popped_node, internal_a);
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 1);

        // Directly call handle_inter_underflow
        map.handle_inter_underflow(internal_a);

        // Verify tree structure is complete
        map.validate();

        assert_eq!(map.height(), 3, "Tree height should remain 3");
        // map.dump();

        // Verify all data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
            assert!(
                map.contains_key(&CounterI32::new((10 + i) * 2)),
                "Key {} should exist",
                (10 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((20 + i) * 2)),
                "Key {} should exist",
                (20 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((30 + i) * 2)),
                "Key {} should exist",
                (30 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((40 + i) * 2)),
                "Key {} should exist",
                (40 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((50 + i) * 2)),
                "Key {} should exist",
                (50 + i) * 2
            );
            assert_eq!(map.leaf_count(), 6);
            #[cfg(feature = "trace_log")]
            assert_eq!(map.triggers, TestFlag::InterMergeRight as u32);
        }
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Handle internal node underflow with right merge (no cascade)
///
/// Tree structure:
///   root(h=2) -> [internal_a | key | internal_b | key | internal_c]
///   internal_a(h=1) -> [leaf_1 | key | leaf_2]
///   internal_b(h=1) -> [leaf_3 | key | leaf_4]  <- target node
///   internal_c(h=1) -> [leaf_5 | key | leaf_6]  <- right sibling with space
///
/// Key test: Verifies handle_inter_underflow when merging internal_b with left sibling
/// but parent has enough keys to not need merging (no internal loop).
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_merge_left_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create leaves for all internal nodes
        let mut leaf_1 = builder.new_leaf();
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();
        let mut leaf_4 = builder.new_leaf();
        let mut leaf_5 = builder.new_leaf();
        let mut leaf_6 = builder.new_leaf();

        // Fill leaves with minimal data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
            builder.insert_leaf(
                &mut leaf_2,
                CounterI32::new((10 + i) * 2),
                CounterI32::new((10 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_3,
                CounterI32::new((20 + i) * 2),
                CounterI32::new((20 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_4,
                CounterI32::new((30 + i) * 2),
                CounterI32::new((30 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_5,
                CounterI32::new((40 + i) * 2),
                CounterI32::new((40 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_6,
                CounterI32::new((50 + i) * 2),
                CounterI32::new((50 + i) * 10),
            );
        }

        let _leaf_1_first = leaf_1.get_keys()[0].clone();
        let leaf_2_first = leaf_2.get_keys()[0].clone();
        let leaf_3_first = leaf_3.get_keys()[0].clone();
        let leaf_4_first = leaf_4.get_keys()[0].clone();
        let leaf_5_first = leaf_5.get_keys()[0].clone();
        let leaf_6_first = leaf_6.get_keys()[0].clone();

        // Create internal_a (height=1) with key_count=1
        let mut internal_a = builder.new_inter(1);
        internal_a.set_left_ptr(leaf_1.get_ptr_mut());
        internal_a.insert_no_split(leaf_2_first, leaf_2.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 1);

        // Create internal_b (height=1) with key_count=1 (target node)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_3.get_ptr_mut());
        internal_b.insert_no_split(leaf_4_first, leaf_4.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 1);

        // Create internal_c (height=1) with key_count=1 (right sibling with space)
        let mut internal_c = builder.new_inter(1);
        internal_c.set_left_ptr(leaf_5.get_ptr_mut());
        internal_c.insert_no_split(leaf_6_first, leaf_6.get_ptr_mut());
        debug_assert_eq!(internal_c.key_count(), 1);

        // Create root (height=2) with key_count=2
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_a.get_ptr_mut());
        root.insert_no_split(leaf_3_first, internal_b.get_ptr_mut());
        root.insert_no_split(leaf_5_first, internal_c.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 2);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 18);
        map.validate();
        //map.dump();
        assert_eq!(map.height(), 3, "Tree height should remain 3");

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        // Use a reference to leaf_3's first key for lookup
        let leaf_3_lookup = &leaf_3.get_keys()[0];
        let _ = map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, leaf_3_lookup);

        // Pop height=1 InterNode (internal_b) from cache
        let (popped_node, _) = cache.pop().unwrap();
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 1);
        assert_eq!(popped_node, internal_b);

        // Directly call handle_inter_underflow
        map.handle_inter_underflow(internal_b);

        // Verify tree structure is complete
        map.validate();
        //map.dump();

        assert_eq!(map.height(), 3, "Tree height should remain 3");

        // Verify all data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
            assert!(
                map.contains_key(&CounterI32::new((10 + i) * 2)),
                "Key {} should exist",
                (10 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((20 + i) * 2)),
                "Key {} should exist",
                (20 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((30 + i) * 2)),
                "Key {} should exist",
                (30 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((40 + i) * 2)),
                "Key {} should exist",
                (40 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((50 + i) * 2)),
                "Key {} should exist",
                (50 + i) * 2
            );

            assert_eq!(map.leaf_count(), 6);
            #[cfg(feature = "trace_log")]
            assert_eq!(map.triggers, TestFlag::InterMergeLeft as u32);
        }
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Handle internal node underflow causing root to become leaf
///
/// Tree structure before:
///   root(h=3) -> [internal_a]
///   internal_a(h=2) -> [internal_b]
///   internal_b(h=1) -> [leaf_1]  <- target node (only one child)
///
/// This creates a degenerate tree where each internal node has only 1 child.
/// When handle_inter_underflow is called on internal_b:
/// - internal_b has key_count=0, height=1 != root_height
/// - root has key_count=0, so peek_ancenstor returns None
/// - This should trigger root replacement
///
/// Key test: Verifies handle_inter_underflow when a node has only 1 child
/// and all ancestors also have only 1 child, causing root to be replaced.
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_root_becomes_leaf(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create single leaf
        let mut leaf_1 = builder.new_leaf();

        // Fill leaf with data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }

        let leaf_1_first = leaf_1.get_keys()[0].clone();

        // Create internal_b (height=1) with key_count=0 (only left child)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_1.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 0);

        // Create internal_a (height=2) with key_count=0 (only left child)
        let mut internal_a = builder.new_inter(2);
        internal_a.set_left_ptr(internal_b.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 0);

        // Create root (height=3) with key_count=0 (only left child)
        let mut root = builder.new_inter(3);
        root.set_left_ptr(internal_a.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 0);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 3);
        map.validate();
        assert_eq!(map.height(), 4);
        // map.dump();

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        let _ = map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, &leaf_1_first);

        // Pop height=1 InterNode (internal_b) from cache
        let (popped_node, _) = cache.pop().unwrap();
        assert_eq!(popped_node, internal_b);
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 0);

        // Directly call handle_inter_underflow on internal_b
        map.handle_inter_underflow(internal_b);

        // Verify tree structure is complete
        map.validate();
        // map.dump();

        // After all merges, root should become the leaf (height=1)
        assert_eq!(map.height(), 1, "Root should become leaf after cascade merge");

        // Verify remaining data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
        }
        assert_eq!(map.leaf_count(), 1);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, 0);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Handle internal node underflow with single-leaf InterNodes at height=1
///
/// Based on test_inter_underflow_merge_right_height_3, but each height=1 InterNode
/// has only one leaf (no keys, just a left child pointer).
///
/// Tree structure:
///   root(h=2) -> [internal_a | key | internal_b | key | internal_c]
///   internal_a(h=1) -> [leaf_1]  <- target node (only left child, 0 keys)
///   internal_b(h=1) -> [leaf_2]  <- left sibling with space (only left child, 0 keys)
///   internal_c(h=1) -> [leaf_3]  (only left child, 0 keys)
///
/// Key test: Verifies handle_inter_underflow internal_a when each height=1 InterNode has only
/// one leaf child. This tests the edge case where InterNodes have 0 keys.
/// NOTE: Nothing change afterwards.
/// Uses CounterI32 to verify key memory management.
#[logfn]
#[rstest]
fn test_inter_underflow_single_leaf_inter_nodes_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    {
        // Create 3 leaves (each InterNode will have exactly one leaf)
        let mut leaf_1 = builder.new_leaf();
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();

        // Fill leaves with minimal data
        for i in 0..3 {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
            builder.insert_leaf(
                &mut leaf_2,
                CounterI32::new((10 + i) * 2),
                CounterI32::new((10 + i) * 10),
            );
            builder.insert_leaf(
                &mut leaf_3,
                CounterI32::new((20 + i) * 2),
                CounterI32::new((20 + i) * 10),
            );
        }

        let leaf_1_first = leaf_1.get_keys()[0].clone();
        let leaf_2_first = leaf_2.get_keys()[0].clone();
        let leaf_3_first = leaf_3.get_keys()[0].clone();

        // Create internal_a (height=1) with 0 keys, only left child (target node)
        let mut internal_a = builder.new_inter(1);
        internal_a.set_left_ptr(leaf_1.get_ptr_mut());
        debug_assert_eq!(internal_a.key_count(), 0);

        // Create internal_b (height=1) with 0 keys, only left child (left sibling)
        let mut internal_b = builder.new_inter(1);
        internal_b.set_left_ptr(leaf_2.get_ptr_mut());
        debug_assert_eq!(internal_b.key_count(), 0);

        // Create internal_c (height=1) with 0 keys, only left child
        let mut internal_c = builder.new_inter(1);
        internal_c.set_left_ptr(leaf_3.get_ptr_mut());
        debug_assert_eq!(internal_c.key_count(), 0);

        // Create root (height=2) with 2 keys
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_a.get_ptr_mut());
        root.insert_no_split(leaf_2_first, internal_b.get_ptr_mut());
        root.insert_no_split(leaf_3_first, internal_c.get_ptr_mut());
        debug_assert_eq!(root.key_count(), 2);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), 9);
        map.validate();
        assert_eq!(map.height(), 3, "Tree height should be 3");
        // map.dump();

        // Use find_leaf_with_cache to populate cache
        let cache = map.clear_cache();
        let _ = map.get_root_unwrap().into_inter().find_leaf_with_cache(cache, &leaf_1_first);

        // Pop height=1 InterNode (internal_a) from cache
        let (popped_node, _) = cache.pop().unwrap();
        assert_eq!(popped_node, internal_a);
        debug_assert_eq!(popped_node.height(), 1);
        debug_assert_eq!(popped_node.key_count(), 0);

        // Record alive count before underflow handling
        let alive_before = alive_count();
        println!("Alive count before handle_inter_underflow: {}", alive_before);

        // Directly call handle_inter_underflow
        map.handle_inter_underflow(internal_a);

        // Verify tree structure is complete
        map.validate();

        assert_eq!(map.height(), 3, "Tree height should remain 3");
        // map.dump();

        println!("Alive count after handle_inter_underflow: {}", alive_count());

        // Verify all data is accessible
        for i in 0..3 {
            assert!(map.contains_key(&CounterI32::new(i * 2)), "Key {} should exist", i * 2);
            assert!(
                map.contains_key(&CounterI32::new((10 + i) * 2)),
                "Key {} should exist",
                (10 + i) * 2
            );
            assert!(
                map.contains_key(&CounterI32::new((20 + i) * 2)),
                "Key {} should exist",
                (20 + i) * 2
            );
        }
        assert_eq!(map.leaf_count(), 3);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, 0);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}
