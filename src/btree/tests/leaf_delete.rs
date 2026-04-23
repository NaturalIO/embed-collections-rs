use super::*;
use captains_log::logfn;
use rstest::rstest;

/// Test: Merge middle leaf with left sibling in height=2 tree
///
/// Scenario: Three leaves (left, middle, right) under root. Middle leaf underflows
/// and merges with left sibling. Right sibling remains unchanged.
///
/// Before: [left_leaf | middle_first_key | middle_leaf | right_first_key | right_leaf]
/// After:  [left_leaf+middle_leaf | right_first_key | right_leaf]
///
/// Coverage:
/// - Merge content to left brother
/// - delete mid 1 from InterNode at root level
/// - change_key skip as right node does not change
#[logfn]
#[rstest]
fn test_leaf_del_merge_with_left_height_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    {
        assert!(min_count > 2);

        // Create three leaf nodes
        let mut left_leaf = builder.new_leaf();
        let mut middle_leaf = builder.new_leaf();
        let mut right_leaf = builder.new_leaf();

        // Fill left leaf to min_count (can accept merge)
        for i in 0..min_count {
            builder.insert_leaf(&mut left_leaf, (i as i32 * 2).into(), (i as i32 * 10).into());
        }

        // Fill middle leaf to just above underflow threshold
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            builder.insert_leaf(&mut middle_leaf, key.into(), ((min_count + i) as i32 * 10).into());
        }

        // Fill right leaf to min_count
        for i in 0..leaf_cap {
            let key = (2 * min_count + i) as i32 * 2;
            builder.insert_leaf(
                &mut right_leaf,
                key.into(),
                ((2 * min_count + i) as i32 * 10).into(),
            );
        }

        let middle_first_key = middle_leaf.get_keys()[0].clone();
        let right_first_key = right_leaf.get_keys()[0].clone();
        let left_last_key = left_leaf.get_keys()[left_leaf.key_count() as usize - 1].clone();

        // Create root internal node with height=1
        let mut root =
            builder.new_root(1, middle_first_key, left_leaf.get_ptr(), middle_leaf.get_ptr());
        root.insert_no_split(right_first_key.clone(), right_leaf.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (2 * min_count + leaf_cap) as usize);
        assert_eq!(map.inter_count(), 1);
        map.validate();

        // Record the key that will remain in middle after removals
        let middle_remaining_key = middle_leaf.get_keys()[0].clone();
        //map.dump();
        println!("begin test");
        // Remove one element from middle leaf triggers underflow
        let delete_key = (1 + min_count) as i32 * 2;
        println!("remove {delete_key}");
        assert!(map.remove(&delete_key).is_some());

        // Now middle leaf should have underflowed and merged with left
        map.validate();

        // Verify the merged structure
        let root = map.get_root_unwrap().into_inter();
        assert_eq!(root.key_count(), 1); // Two leaves left after merge
        assert_eq!(map.len(), (2 * min_count - 1 + leaf_cap) as usize);

        // Verify parent split key changed: should now be right_first_key
        // (was middle_first_key before merge)
        assert_eq!(
            root.get_keys()[0],
            right_first_key,
            "Parent split key should change from middle_first_key to right_first_key after merge"
        );

        // Verify all data is accessible and merged correctly
        // Left leaf should now contain: original left keys + remaining middle key
        for i in 0..(min_count * 2 + leaf_cap) {
            let key = i as i32 * 2;
            if key != delete_key {
                assert_eq!(
                    map.get(&key).map(|v| **v),
                    Some(i as i32 * 10),
                    "Original left leaf key {} should be accessible",
                    key
                );
            }
        }
        // The one remaining key from middle leaf should be in left leaf now
        assert_eq!(
            map.get(&middle_remaining_key).map(|v| **v),
            Some(*middle_remaining_key * 10 / 2),
            "Remaining middle leaf key {} should be merged into left leaf",
            middle_remaining_key
        );
        // Verify key ordering: left_last_key < middle_remaining_key < right_first_key
        assert!(
            left_last_key < middle_remaining_key,
            "Left last key should be less than merged middle key"
        );
        assert!(
            middle_remaining_key < right_first_key,
            "Merged middle key should be less than right first key"
        );

        assert_eq!(map.height(), 2);
        assert_eq!(map.leaf_count(), 2);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::LeafMergeLeft as u32 | TestFlag::RemoveChildMid as u32);
        // Cleanup
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Merge middle leaf with right sibling in height=2 tree
///
/// Scenario: Three leaves (left, middle, right) under root. Middle leaf underflows
/// and merges with right sibling. Left sibling remains unchanged.
///
/// Key difference from merge-with-left:
/// - Middle leaf merges INTO right sibling (not the other way around)
/// - Right sibling's first key becomes the new split key in parent
/// - Original right_first_key is pushed to the right
///
/// Before: [left_leaf | middle_first_key | middle_leaf | right_first_key | right_leaf]
/// After:  [left_leaf | middle_first_key | middle_leaf+right_leaf]
///
/// Coverage:
/// - Merge content to right brother
/// - delete mid 1 from InterNode at root level
/// - Change sep key of right leaf after shifting left
#[logfn]
#[rstest]
fn test_merge_left_with_right_height_2(setup_log: ()) {
    reset_alive_count();

    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create three leaf nodes
        let mut left_leaf = builder.new_leaf();
        let mut middle_leaf = builder.new_leaf();
        let mut right_leaf = builder.new_leaf();

        // Fill left leaf to min_count
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            builder.insert_leaf(&mut left_leaf, (i as i32 * 2).into(), (key * 10).into());
        }

        // Fill middle leaf to just above underflow threshold
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            builder.insert_leaf(&mut middle_leaf, key.into(), (key * 10).into());
        }

        // Fill right leaf to min_count (can accept merge)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            builder.insert_leaf(&mut right_leaf, key.into(), (key * 10).into());
        }

        let middle_first_key = middle_leaf.get_keys()[0].clone();
        let right_first_key = right_leaf.get_keys()[0].clone();

        // Create root internal node with height=1
        let mut root = builder.new_inter(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key.clone(), right_leaf.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (leaf_cap + 2 * min_count) as usize);
        assert_eq!(map.height(), 2);
        map.validate();

        // Remove elements from middle leaf to trigger merge with right
        let delete_key = (leaf_cap) as i32 * 2;
        assert!(map.remove(&delete_key).is_some());

        map.validate();

        // Verify structure - should have merged middle into right
        let root = map.get_root_unwrap().into_inter();
        assert_eq!(root.key_count(), 1);
        assert_eq!(map.len(), (leaf_cap + 2 * min_count - 1) as usize);

        // Verify parent split key: should now be right_first_key
        // After middle+right merge, the split key between left and merged node
        // should be the first key of the merged node (which was right_first_key)
        assert!(
            root.get_keys()[0] != right_first_key,
            "root sep key should changed, expected {}",
            root.get_keys()[0]
        );

        // Verify all data is accessible
        // Left leaf unchanged
        for i in 0..(min_count * 2 + leaf_cap) {
            let key = i as i32 * 2;
            if key != delete_key {
                assert_eq!(map.get(&key).map(|v| **v), Some(key * 10));
            }
        }
        assert_eq!(map.height(), 2);
        assert_eq!(map.leaf_count(), 2);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::LeafMergeRight as u32
                | TestFlag::RemoveChildMid as u32
                | TestFlag::UpdateSepKey as u32
        );
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Three-way merge (left + middle + right -> left + right)
///
/// Scenario: Three small leaves where left+middle <= cap but also
/// left+middle+right <= 2*cap, allowing a 3-way merge into single leaf.
///
/// Key difference from 2-way merge:
/// - All three leaves are merged into one
/// - Parent loses two child pointers
/// - Most aggressive space consolidation
///
/// Before: [left_leaf | key1 | middle_leaf | key2 | right_leaf]
/// After:  [left_leaf+middle_leaf+right_leaf]
/// Coverage:
/// - Merge with left and right brothers
/// - delete child at mid idx=1 of root level
/// - change_key for right leaf after shifting left
#[logfn]
#[rstest]
fn test_leaf_del_merge_3_2_height_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // For 3-way merge, we need small nodes
        // left + middle + right should be <= 2 * cap
        let small_count = leaf_cap / 3;
        if small_count == 0 {
            return; // Skip if cap is too small
        }
        println!("leaf_cap {leaf_cap}");

        // Create three leaf nodes with small counts
        let mut left_leaf = builder.new_leaf();
        let mut middle_leaf = builder.new_leaf();
        let mut right_leaf = builder.new_leaf();

        // Fill left leaf
        for i in 0..leaf_cap - 1 {
            let key = i as i32 * 2;
            builder.insert_leaf(&mut left_leaf, key.into(), (key * 10).into());
        }
        // Fill middle leaf
        for i in 0..3 {
            let key = (leaf_cap - 1 + i) as i32 * 2;
            builder.insert_leaf(&mut middle_leaf, key.into(), (key * 10).into());
        }
        // Fill right leaf
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap - 1 + 3 + i) as i32 * 2;
            builder.insert_leaf(&mut right_leaf, key.into(), (key * 10).into());
        }

        let middle_first_key = middle_leaf.get_keys()[0].clone();
        let right_first_key = right_leaf.get_keys()[0].clone();

        // Create root internal node with height=1
        let mut root = builder.new_inter(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key.clone(), right_leaf.get_ptr());

        let total_keys = leaf_cap * 2 - 2 + 3;
        let mut map = builder.build(root.clone().into());
        assert_eq!(map.len(), total_keys as usize);
        assert_eq!(map.height(), 2);
        map.validate();

        // map.dump();

        let delete_key = (leaf_cap - 1) as i32 * 2;
        // Remove elements from middle leaf to trigger 3-way merge
        assert!(map.remove(&delete_key).is_some());
        println!("delete key {delete_key}");

        map.validate();

        // After 3-way merge, should have only one leaf with all data
        assert_eq!(map.len(), total_keys as usize - 1);

        // Verify all remaining data
        for i in 0..total_keys {
            let key = i as i32 * 2;
            if key != delete_key {
                assert_eq!(map.get(&key).map(|v| **v), Some(key * 10), "key {key}");
            } else {
                assert_eq!(map.get(&key), None);
            }
        }
        //map.dump();
        assert_eq!(root.get_keys()[0], (leaf_cap as i32 + 1) * 2);
        assert!(root.get_keys()[0] != right_first_key);
        assert_eq!(map.height(), 2);
        assert_eq!(map.leaf_count(), 2);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::LeafMergeLeft as u32
                | TestFlag::LeafMergeRight as u32
                | TestFlag::RemoveChildMid as u32
                | TestFlag::UpdateSepKey as u32
        );
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Merge at the leftmost leaf (no left sibling, must merge with right)
///
/// Scenario: Leftmost leaf underflows. It has no left sibling, so must merge
/// with right sibling. This tests the boundary condition at the start of leaf chain.
///
/// Key difference from middle leaf merge:
/// - Leftmost leaf has idx=0 in parent
/// - No left sibling exists to merge with
/// - Must merge with right sibling (leaf_idx+1)
///
/// Before: [leftmost_leaf | split_key | right_leaf]
/// After:  [leftmost_leaf+right_leaf]
///
/// Coverage:
/// - delete first child from InterNode
/// - merge to right node
/// - update_ancestor_sep_key skip as root is only key
/// - downgrade root to the only leaf
#[logfn]
#[rstest]
fn test_leaf_del_leftmost_merge_right_height_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create two leaf nodes
        let mut left_leaf = builder.new_leaf();
        let mut right_leaf = builder.new_leaf();

        // Fill left leaf to just above underflow
        for i in 0..min_count {
            builder.insert_leaf(&mut left_leaf, (i as i32 * 2).into(), (i as i32 * 10).into());
        }

        // Fill right leaf to min_count (can accept merge)
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            builder.insert_leaf(&mut right_leaf, key.into(), ((min_count + i) as i32 * 10).into());
        }

        let right_first_key = right_leaf.get_keys()[0].clone();
        let left_first_key = left_leaf.get_keys()[0].clone();

        // Create root internal node with height=1
        let mut root = builder.new_inter(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(right_first_key.clone(), right_leaf.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (2 * min_count) as usize);
        assert_eq!(map.height(), 2);
        map.validate();

        // Remove elements from left leaf to trigger merge with right
        for i in 1..min_count {
            let key = i as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();
        println!("alive count after remove: {}", alive_count());

        // Verify structure
        assert_eq!(map.len(), (min_count + 1) as usize);

        // Verify all remaining data is accessible
        // Leftmost key should still be accessible
        assert_eq!(
            map.get(&left_first_key).map(|v| **v),
            Some(*left_first_key * 10 / 2),
            "Leftmost key {} should be accessible after merge",
            left_first_key
        );

        // Right leaf keys should be merged
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(key * 5),
                "Right leaf key {} should be accessible after merge",
                key
            );
        }

        // Verify ordering: left_first_key < right_leaf keys
        for i in 0..min_count {
            let right_key = (min_count + i) as i32 * 2;
            assert!(
                *left_first_key < right_key,
                "Leftmost key {} should be less than right key {}",
                left_first_key,
                right_key
            );
        }
        assert_eq!(map.height(), 1);
        println!("before drop map, alive count: {}", alive_count());

        assert_eq!(map.leaf_count(), 1);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::LeafMergeRight as u32 | TestFlag::RemoveChildFirst as u32
        );
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Merge at the rightmost leaf (no right sibling, must merge with left)
///
/// Scenario: Rightmost leaf underflows. It has no right sibling, so must merge
/// with left sibling. This tests the boundary condition at the end of leaf chain.
///
/// Key difference from middle leaf merge:
/// - Rightmost leaf has idx=count in parent
/// - No right sibling exists to merge with
/// - Must merge with left sibling (leaf_idx-1)
///
/// Before: [left_leaf | split_key | rightmost_leaf]
/// After:  [left_leaf+rightmost_leaf]
///
/// Coverage:
/// - delete last child from InterNode
/// - no right brother
/// - downgrade root to the only leaf
#[logfn]
#[rstest]
fn test_leaf_del_merge_left_with_rightmost_height_2(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create two leaf nodes
        let mut left_leaf = builder.new_leaf();
        let mut right_leaf = builder.new_leaf();

        // Fill left leaf to min_count (can accept merge)
        for i in 0..min_count {
            builder.insert_leaf(&mut left_leaf, (i as i32 * 2).into(), (i as i32 * 10).into());
        }

        // Fill right leaf to just above underflow
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            builder.insert_leaf(&mut right_leaf, key.into(), ((min_count + i) as i32 * 10).into());
        }

        let right_first_key = right_leaf.get_keys()[0].clone();
        let left_last_key = left_leaf.get_keys()[left_leaf.key_count() as usize - 1].clone();

        // Create root internal node with height=1
        let mut root = builder.new_inter(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(right_first_key.clone(), right_leaf.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (2 * min_count) as usize);
        assert_eq!(map.height(), 2);
        map.validate();
        //map.dump();

        // Record rightmost key that will remain after removals
        let right_remaining_key = right_leaf.get_keys()[0].clone();

        // Remove elements from right leaf to trigger merge with left
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // Verify structure
        assert_eq!(map.len(), (min_count + 1) as usize);

        // Verify all remaining data
        // Left leaf unchanged
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(i as i32 * 10),
                "Left leaf key {} should be accessible",
                key
            );
        }
        // Right leaf's remaining key should be merged into left
        assert_eq!(
            map.get(&right_remaining_key).map(|v| **v),
            Some(*right_remaining_key * 10 / 2),
            "Right leaf remaining key {} should be merged into left",
            right_remaining_key
        );

        // Verify ordering: left_last_key < right_remaining_key
        assert!(
            *left_last_key < *right_remaining_key,
            "Left last key {} should be less than right remaining key {}",
            left_last_key,
            right_remaining_key
        );
        assert_eq!(map.height(), 1);

        assert_eq!(map.leaf_count(), 1);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::LeafMergeLeft as u32 | TestFlag::RemoveChildLast as u32);

        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Merge in height=3 tree (root -> internal nodes -> leaves)
///
/// Scenario: Four leaves organized under two internal nodes under root.
/// Leaf_1 underflows and merges with leaf_0. Tests PathCache navigation
/// through multiple levels of internal nodes.
///
/// Key difference from height=2 tests:
/// - Requires PathCache to navigate up through internal nodes
/// - Tests parent lookup across internal node boundaries
/// - More complex tree structure
///
/// Before: root -> [internal_left | key | internal_right]
///         internal_left -> [leaf_0 | key1 | leaf_1]
///         internal_right -> [leaf_2 | key2 | leaf_3]
/// After:  root -> [internal_left | key | internal_right]
///         internal_left -> [leaf_0+leaf_1]
///         internal_right -> [leaf_2 | key2 | leaf_3]
///
/// Coverage:
/// - Delete last child (leaf_1) from InterNode
/// - merge with left brother, right is not touch
#[logfn]
#[rstest]
fn test_leaf_del_merge_with_left_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create leaf nodes for left branch
        let mut leaf_0 = builder.new_leaf();
        let mut leaf_1 = builder.new_leaf();
        for i in 0..min_count {
            builder.insert_leaf(&mut leaf_0, (i as i32 * 2).into(), (i as i32 * 10).into());
        }
        for i in 0..min_count {
            builder.insert_leaf(
                &mut leaf_1,
                ((min_count + i) as i32 * 2).into(),
                ((min_count + i) as i32 * 10).into(),
            );
        }

        // Create leaf nodes for right branch
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();
        for i in 0..min_count {
            builder.insert_leaf(
                &mut leaf_2,
                ((2 * min_count + i) as i32 * 2).into(),
                ((2 * min_count + i) as i32 * 10).into(),
            );
            builder.insert_leaf(
                &mut leaf_3,
                ((3 * min_count + i) as i32 * 2).into(),
                ((3 * min_count + i) as i32 * 10).into(),
            );
        }

        let leaf1_first_key = leaf_1.get_keys()[0].clone();
        let leaf2_first_key = leaf_2.get_keys()[0].clone();
        let leaf3_first_key = leaf_3.get_keys()[0].clone();

        // Create left internal node (height=1)
        let mut internal_left = builder.new_inter(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = builder.new_inter(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = builder.new_inter(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(leaf2_first_key.clone(), internal_right.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (4 * min_count) as usize);
        map.validate();
        assert_eq!(map.inter_count(), 3);
        assert_eq!(map.height(), 3);
        //map.dump();

        // Record the key that will remain in leaf_1 after removals
        let leaf_1_remaining_key = leaf_1.get_keys()[0].clone();
        let leaf_0_last_key = leaf_0.get_keys()[leaf_0.key_count() as usize - 1].clone();

        // Remove elements from leaf_1 to trigger merge with leaf_0
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }
        println!("removed");
        //map.dump();
        map.validate();

        // Verify structure
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), (3 * min_count + 1) as usize);

        // Verify internal_left now has only one key (leaf_0+leaf_1 merged)
        assert_eq!(internal_left.key_count(), 0, "internal_left should have 1 child after merge");

        // Verify root keys unchanged (merge happened below root)
        let root_node = map.get_root_unwrap().into_inter();
        assert_eq!(root_node.key_count(), 1, "Root should still have 2 children");

        // Verify all remaining data
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(i as i32 * 10),
                "leaf_0 key {} should be accessible",
                key
            );
        }
        // The one remaining key from leaf_1
        assert_eq!(
            map.get(&leaf_1_remaining_key).map(|v| **v),
            Some(*leaf_1_remaining_key * 10 / 2),
            "leaf_1 remaining key {} should be merged into leaf_0",
            leaf_1_remaining_key
        );

        // Verify key ordering
        assert!(
            *leaf_0_last_key < *leaf_1_remaining_key,
            "leaf_0 last key {} should be less than merged leaf_1 key {}",
            leaf_0_last_key,
            leaf_1_remaining_key
        );
        assert_eq!(map.leaf_count(), 3);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::LeafMergeLeft as u32 | TestFlag::RemoveChildLast as u32);

        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Merge with right sibling in different subtree (height=3)
///
/// Scenario: Four leaves organized under two internal nodes under root.
/// Leaf_1 (in left subtree) underflows and needs to merge with right sibling.
/// But leaf_2 (the right sibling) is in a different internal node (internal_right),
/// which is a different subtree under root.
///
/// Tree structure:
///   root(h=2) -> [internal_left | key | internal_right]
///   internal_left(h=1) -> [leaf_0 | key | leaf_1]
///   internal_right(h=1) -> [leaf_2 | key | leaf_3]
///
/// Where:
/// - leaf_0: full (leaf_cap keys)
/// - leaf_1: half-full (min_count keys) - will underflow after delete
/// - leaf_2: half-full (min_count keys) - can accept merge from leaf_1
/// - leaf_3: not used in this test
///
/// Delete from leaf_1 triggers underflow, must merge with leaf_2.
/// This tests PathCache navigation across internal node boundaries
/// when the right sibling is not in the same parent.
///
/// Coverage:
/// - Merge content to right brother in different subtree
/// - PathCache navigation across internal node boundaries
/// - Delete last child (leaf_1) from internal_left
/// - Update root sep key of right after merge
#[logfn]
#[rstest]
fn test_leaf_del_merge_with_right_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create leaf nodes
        let mut leaf_0 = builder.new_leaf(); // Full
        let mut leaf_1 = builder.new_leaf(); // Half-full, will underflow
        let mut leaf_2 = builder.new_leaf(); // Half-full, can accept merge
        let mut leaf_3 = builder.new_leaf(); // Not used in merge

        // Fill leaf_0 to capacity (full)
        for i in 0..leaf_cap {
            builder.insert_leaf(&mut leaf_0, (i as i32 * 2).into(), (i as i32 * 10).into());
        }

        // Fill leaf_1 to min_count (half-full, will underflow after delete)
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_1, key.into(), (key * 10).into());
        }

        // Fill leaf_2 to min_count (half-full, can accept merge)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_2, key.into(), (key * 10).into());
        }

        // Fill leaf_3 with some data
        for i in 0..min_count {
            let key = (leaf_cap + 2 * min_count + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_3, key.into(), (key * 10).into());
        }

        let leaf_1_first_key = leaf_1.get_keys()[0].clone();
        let leaf_2_first_key = leaf_2.get_keys()[0].clone();
        let leaf_3_first_key = leaf_3.get_keys()[0].clone();

        // Create internal_left (height=1) with leaf_0 (full) and leaf_1 (half-full)
        let mut internal_left = builder.new_inter(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf_1_first_key, leaf_1.get_ptr());

        // Create internal_right (height=1) with leaf_2 and leaf_3
        let mut internal_right = builder.new_inter(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf_3_first_key, leaf_3.get_ptr());

        // Create root (height=2)
        let root = builder.new_root(
            2,
            leaf_2_first_key.clone(),
            internal_left.get_ptr(),
            internal_right.get_ptr(),
        );

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), (leaf_cap + 3 * min_count) as usize);
        map.validate();
        // map.dump();
        assert_eq!(map.height(), 3);

        println!("leaf_2_first_key = {}", leaf_2_first_key);

        // Delete one element from leaf_1 to trigger underflow
        // leaf_1 has min_count keys, delete one to make it underflow
        let delete_key = (leaf_cap + 1) as i32 * 2;
        println!("delete_key = {}", delete_key);
        assert!(map.remove(&delete_key).is_some());

        // map.dump();
        map.validate();

        // Verify structure after merge
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), (leaf_cap + 3 * min_count - 1) as usize);
        // leaf_0 data should be unchanged
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(i as i32 * 10),
                "leaf_0 key {} should be accessible",
                key
            );
        }

        // After merge, all remaining keys should be accessible
        // Don't check specific leaf location, just verify data exists
        for i in 0..(3 * min_count) {
            let key = (leaf_cap + i) as i32 * 2;
            if key != delete_key {
                // Value should be key * 10 for leaf_1/leaf_2/leaf_3 data
                let expected_value = key * 10;
                assert_eq!(
                    map.get(&key).map(|v| **v),
                    Some(expected_value),
                    "key {} should be accessible after merge",
                    key
                );
            }
        }
        assert_eq!(map.leaf_count(), 3);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::LeafMergeRight as u32
                | TestFlag::RemoveChildLast as u32
                | TestFlag::UpdateSepKey as u32
        );

        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Three-way merge in height=3 tree (leaf_1 + leaf_2 + leaf_3 -> leaf_1 + leaf_3)
///
/// Scenario: Four leaves organized under two internal nodes under root.
/// leaf_2 underflows after deletion and triggers a 3-way merge with leaf_1 and leaf_3.
///
/// Tree structure:
///   root(h=2) -> [internal_left | key | internal_right]
///   internal_left(h=1) -> [leaf_0 | key | leaf_1]
///   internal_right(h=1) -> [leaf_2 | key | leaf_3]
///
/// Where:
/// - leaf_0: full (leaf_cap keys)
/// - leaf_1: one less than full (leaf_cap - 1 keys)
/// - leaf_2: 3 keys - will underflow after delete
/// - leaf_3: leaf_cap - 2 keys (adjusted so leaf_1+leaf_2+leaf_3 = 2*leaf_cap)
///
/// Delete from leaf_2 triggers underflow. Since leaf_1+leaf_2+leaf_3 = 2*cap,
/// all three leaves merge into two leaves (leaf_1 gets merged content).
///
/// Coverage:
/// - delete first child (leaf_2) from inter_right
/// - 3-way merge with (leaf_1, leaf_3)
/// - change leaf_3 sep key at root level
#[logfn]
#[rstest]
fn test_leaf_del_merge_2_3_height_3(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create leaf nodes
        let mut leaf_0 = builder.new_leaf(); // Full
        let mut leaf_1 = builder.new_leaf(); // One less than full (leaf_cap - 1)
        let mut leaf_2 = builder.new_leaf(); // Only 3 keys, will underflow
        let mut leaf_3 = builder.new_leaf(); // leaf_cap - 2 keys

        // Fill leaf_0 to capacity (full)
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            builder.insert_leaf(&mut leaf_0, key.into(), (key * 5).into());
        }
        // Fill leaf_1 to leaf_cap - 1 (one less than full)
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_1, key.into(), (key * 5).into());
        }

        // Fill leaf_2 with only 3 keys (will underflow after delete)
        for i in 0..3 {
            let key = (leaf_cap + leaf_cap - 1 + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_2, key.into(), (key * 5).into());
        }
        // Fill leaf_3 to leaf_cap - 2 (adjusted for 3-way merge condition)
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap + leaf_cap - 1 + 3 + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_3, key.into(), (key * 5).into());
        }

        let leaf_1_first_key = leaf_1.get_keys()[0].clone();
        let leaf_2_first_key = leaf_2.get_keys()[0].clone();
        let leaf_3_first_key = leaf_3.get_keys()[0].clone();
        // Create internal_left (height=1) with leaf_0 (full) and leaf_1
        let mut internal_left = builder.new_inter(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf_1_first_key, leaf_1.get_ptr());
        // Create internal_right (height=1) with leaf_2 and leaf_3
        let mut internal_right = builder.new_inter(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf_3_first_key, leaf_3.get_ptr());

        // Create root (height=2)
        let root = builder.new_root(
            2,
            leaf_2_first_key.clone(),
            internal_left.get_ptr(),
            internal_right.get_ptr(),
        );
        // Calculate total keys: leaf_cap + (leaf_cap - 1) + 3 + (leaf_cap-2) = 3*leaf_cap

        let total_keys = leaf_cap + (leaf_cap - 1) + 3 + (leaf_cap - 1);

        let mut map = builder.build(root.into());
        assert_eq!(map.len(), total_keys as usize);
        map.validate();
        assert_eq!(map.height(), 3);

        // Delete one element from leaf_2 to trigger underflow and 3-way merge
        // leaf_2 has 3 keys, delete one to make it underflow (2 keys < min_count)
        let delete_key = (leaf_cap + leaf_cap - 1 + 1) as i32 * 2;
        println!("delete_key = {}", delete_key);
        assert!(map.remove(&delete_key).is_some());

        map.validate();
        // After 3-way merge, leaf_1, leaf_2, and leaf_3 should be merged
        // Total remaining keys = total_keys - 1
        assert_eq!(map.len(), (total_keys - 1) as usize);
        // Verify all remaining data is accessible
        // All values are stored as key * 5
        for i in 0..total_keys {
            let key = i as i32 * 2;
            if key != delete_key {
                let expected_value = key * 5;
                assert_eq!(
                    map.get(&key).map(|v| **v),
                    Some(expected_value),
                    "key {} should be accessible after merge",
                    key
                );
            }
        }
        assert_eq!(map.leaf_count(), 3);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::LeafMergeRight as u32
                | TestFlag::LeafMergeLeft as u32
                | TestFlag::RemoveChildFirst as u32
                | TestFlag::UpdateSepKey as u32
        );
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

/// Test: Remove only child cascade when middle leaf merges to right
///
/// Tree structure:
///   root(h=3) -> [inter_left | key_ab | inter_min | key_bc | inter_right]
///   inter_left(h=2) -> [inter_left1]  <- single child (no keys)
///     inter_left1(h=1) -> [leaf_left] (full)
///   inter_min(h=2) -> [inter_min1]  <- single child (no keys)
///     inter_min1(h=1) -> [leaf_mid] (half-full, will underflow)
///   inter_right(h=2) -> [inter_right1]  <- single child (no keys)
///     inter_right1(h=1) -> [leaf_right] (half-full)
///
/// Scenario: Delete one element from leaf_mid, causing it to underflow.
/// Since leaf_left is full, leaf_mid must merge/move to leaf_right.
/// After leaf_mid is deleted, inter_min1 has no children (or only empty child),
/// triggering remove_only_child cascade up to root.
///
/// Coverage:
/// - Leaf underflow triggers migration to right sibling
/// - Parent InterNode (inter_min1) becomes empty after leaf deletion
/// - remove_only_child is triggered to clean up empty InterNode
/// - Cascade removal of single-child internal nodes up the tree
#[logfn]
#[rstest]
fn test_leaf_del_remove_only_child_cascade(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let min_count = (leaf_cap + 1) / 2;
    assert!(min_count > 2);
    {
        // Create three leaves: left (full), mid (half-full), right (half-full)
        let mut leaf_left = builder.new_leaf();
        let mut leaf_mid = builder.new_leaf();
        let mut leaf_right = builder.new_leaf();

        // Fill leaf_left to capacity (full - cannot accept merge)
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            builder.insert_leaf(&mut leaf_left, key.into(), (key * 10).into());
        }

        // Fill leaf_mid to min_count (half-full - will underflow after delete)
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_mid, key.into(), (key * 10).into());
        }

        // Fill leaf_right to min_count (half-full - can accept merge from mid)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            builder.insert_leaf(&mut leaf_right, key.into(), (key * 10).into());
        }

        let leaf_mid_first_key = leaf_mid.get_keys()[0].clone();
        let leaf_right_first_key = leaf_right.get_keys()[0].clone();

        // Create inter_left1 (height=1) with single child leaf_left, no keys
        let mut inter_left1 = builder.new_inter(1);
        inter_left1.set_left_ptr(leaf_left.get_ptr());

        // Create inter_min1 (height=1) with single child leaf_mid, no keys
        let mut inter_min1 = builder.new_inter(1);
        inter_min1.set_left_ptr(leaf_mid.get_ptr());

        // Create inter_right1 (height=1) with single child leaf_right, no keys
        let mut inter_right1 = builder.new_inter(1);
        inter_right1.set_left_ptr(leaf_right.get_ptr());

        // Create inter_left (height=2) with single child inter_left1, no keys
        let mut inter_left = builder.new_inter(2);
        inter_left.set_left_ptr(inter_left1.get_ptr());

        // Create inter_min (height=2) with single child inter_min1, no keys
        let mut inter_min = builder.new_inter(2);
        inter_min.set_left_ptr(inter_min1.get_ptr());

        // Create inter_right (height=2) with single child inter_right1, no keys
        let mut inter_right = builder.new_inter(2);
        inter_right.set_left_ptr(inter_right1.get_ptr());
        debug_assert_eq!(inter_right.key_count(), 0);

        // Create root (height=3) with 2 keys and 3 children
        let mut root = builder.new_inter(3);
        root.set_left_ptr(inter_left.get_ptr());
        root.insert_no_split(leaf_mid_first_key.clone(), inter_min.get_ptr());
        root.insert_no_split(leaf_right_first_key.clone(), inter_right.get_ptr());
        debug_assert_eq!(root.key_count(), 2);

        let total_keys = leaf_cap + 2 * min_count;
        let mut map = builder.build(root.into());
        assert_eq!(map.len(), total_keys as usize);
        map.validate();
        assert_eq!(map.height(), 4, "Initial tree height should be 4");
        // map.dump();

        // Delete one element from leaf_mid to trigger underflow
        // leaf_mid has min_count keys, delete one to make it underflow
        let delete_key = (leaf_cap + 1) as i32 * 2;
        assert!(map.remove(&delete_key).is_some(), "Should remove key successfully");

        map.validate();

        // After merge, total keys should be total_keys - 1
        assert_eq!(map.len(), (total_keys - 1) as usize, "Total keys should decrease by 1");

        // Verify that inter_min and inter_min1 were removed (remove_only_child cascade)
        // The root should now have only 2 children (inter_left and inter_right)
        let root_node = map.get_root_unwrap().into_inter();
        assert_eq!(
            root_node.key_count(),
            1,
            "Root should have only 1 key (2 children) after remove_only_child cascade"
        );
        // map.dump();

        // Verify all remaining data is accessible
        // leaf_left data unchanged
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(key * 10),
                "leaf_left key {} should be accessible",
                key
            );
        }

        // leaf_mid remaining data merged into leaf_right
        // leaf_mid had min_count keys, one deleted, remaining min_count-1 keys
        // After merge, they should be in leaf_right (or merged leaf)
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            if key != delete_key {
                assert_eq!(
                    map.get(&key).map(|v| **v),
                    Some(key * 10),
                    "leaf_mid remaining key {} should be accessible after merge",
                    key
                );
            }
        }

        // leaf_right data unchanged (plus merged data from leaf_mid)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            assert_eq!(
                map.get(&key).map(|v| **v),
                Some(key * 10),
                "leaf_right key {} should be accessible",
                key
            );
        }
        // map.dump();
        assert_eq!(map.leaf_count(), 2);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::RemoveOnlyChild as u32
                | TestFlag::RemoveChildMid as u32
                | TestFlag::LeafMergeRight as u32
                | TestFlag::UpdateSepKey as u32
        );
        drop(map);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}
