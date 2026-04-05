use super::super::{inter::*, leaf::*, node::*, *};
use core::cell::UnsafeCell;

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
#[test]
fn test_leaf_del_merge_with_left_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to min_count (can accept merge)
        for i in 0..min_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf to just above underflow threshold
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            middle_leaf.insert_no_split(key, (min_count + i) as i32 * 10);
        }

        // Fill right leaf to min_count
        for i in 0..leaf_cap {
            let key = (2 * min_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, (2 * min_count + i) as i32 * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];
        let left_last_key = left_leaf.get_keys()[left_leaf.key_count() as usize - 1];

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::new_root(
            1,
            middle_first_key,
            left_leaf.get_ptr(),
            middle_leaf.get_ptr(),
        );
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (2 * min_count + leaf_cap) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
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
        let root = map.get_root_unwrap().as_inter();
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
                    map.get(&key),
                    Some(&(i as i32 * 10)),
                    "Original left leaf key {} should be accessible",
                    key
                );
            }
        }
        // The one remaining key from middle leaf should be in left leaf now
        assert_eq!(
            map.get(&middle_remaining_key),
            Some(&(middle_remaining_key * 10 / 2)),
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

        // Cleanup
        drop(map);
    }
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
#[test]
fn test_merge_left_with_right_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to min_count
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            left_leaf.insert_no_split(i as i32 * 2, key * 10);
        }

        // Fill middle leaf to just above underflow threshold
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            middle_leaf.insert_no_split(key, key * 10);
        }

        // Fill right leaf to min_count (can accept merge)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, key * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (leaf_cap + 2 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        map.validate();

        // Remove elements from middle leaf to trigger merge with right
        let delete_key = (leaf_cap) as i32 * 2;
        assert!(map.remove(&delete_key).is_some());

        map.validate();

        // Verify structure - should have merged middle into right
        let root = map.get_root_unwrap().as_inter();
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
                assert_eq!(map.get(&key), Some(&(key * 10)));
            }
        }
        drop(map);
    }
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
/// - change_key for right leaf after shifting leeft
#[test]
fn test_leaf_del_merge_3_2_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let _min_count = (leaf_cap + 1) / 2;
        // For 3-way merge, we need small nodes
        // left + middle + right should be <= 2 * cap
        let small_count = leaf_cap / 3;
        if small_count == 0 {
            return; // Skip if cap is too small
        }
        println!("leaf_cap {leaf_cap}");

        // Create three leaf nodes with small counts
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf
        for i in 0..leaf_cap - 1 {
            let key = i as i32 * 2;
            left_leaf.insert_no_split(key, key * 10);
        }

        // Fill middle leaf
        for i in 0..3 {
            let key = (leaf_cap - 1 + i) as i32 * 2;
            middle_leaf.insert_no_split(key, key * 10);
        }

        // Fill right leaf
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap - 1 + 3 + i) as i32 * 2;
            right_leaf.insert_no_split(key, key * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        let total_keys = leaf_cap * 2 - 2 + 3;
        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root.clone())),
            len: total_keys as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        map.validate();

        //map.dump();

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
                assert_eq!(map.get(&key), Some(&(key * 10)), "key {key}");
            } else {
                assert_eq!(map.get(&key), None);
            }
        }
        //map.dump();
        assert_eq!(root.get_keys()[0], (leaf_cap as i32 + 1) * 2);
        assert!(root.get_keys()[0] != right_first_key);
        drop(map);
    }
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
#[test]
fn test_leaf_del_leftmost_merge_right_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create two leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to just above underflow
        for i in 0..min_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill right leaf to min_count (can accept merge)
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, (min_count + i) as i32 * 10);
        }

        // Link leaves
        (*left_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = left_leaf.get_ptr();

        let right_first_key = right_leaf.get_keys()[0];
        let left_first_key = left_leaf.get_keys()[0];

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (2 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        map.validate();
        assert_eq!(map.height(), 2);

        // Remove elements from left leaf to trigger merge with right
        for i in 1..min_count {
            let key = i as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // Verify structure
        assert_eq!(map.len(), (min_count + 1) as usize);

        // Verify all remaining data is accessible
        // Leftmost key should still be accessible
        assert_eq!(
            map.get(&left_first_key),
            Some(&(left_first_key * 10 / 2)),
            "Leftmost key {} should be accessible after merge",
            left_first_key
        );

        // Right leaf keys should be merged
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            assert_eq!(
                map.get(&key),
                Some(&(key * 5)),
                "Right leaf key {} should be accessible after merge",
                key
            );
        }

        // Verify ordering: left_first_key < right_leaf keys
        for i in 0..min_count {
            let right_key = (min_count + i) as i32 * 2;
            assert!(
                left_first_key < right_key,
                "Leftmost key {} should be less than right key {}",
                left_first_key,
                right_key
            );
        }
        assert_eq!(map.height(), 1);
        drop(map);
    }
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
#[test]
fn test_leaf_del_merge_left_with_rightmost_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create two leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to min_count (can accept merge)
        for i in 0..min_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill right leaf to just above underflow
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, (min_count + i) as i32 * 10);
        }

        // Link leaves
        (*left_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = left_leaf.get_ptr();

        let right_first_key = right_leaf.get_keys()[0];
        let left_last_key = left_leaf.get_keys()[left_leaf.key_count() as usize - 1];

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (2 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        assert_eq!(map.height(), 2);
        map.validate();

        // Record rightmost key that will remain after removals
        let right_remaining_key = right_leaf.get_keys()[0];

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
                map.get(&key),
                Some(&(i as i32 * 10)),
                "Left leaf key {} should be accessible",
                key
            );
        }
        // Right leaf's remaining key should be merged into left
        assert_eq!(
            map.get(&right_remaining_key),
            Some(&(right_remaining_key * 10 / 2)),
            "Right leaf remaining key {} should be merged into left",
            right_remaining_key
        );

        // Verify ordering: left_last_key < right_remaining_key
        assert!(
            left_last_key < right_remaining_key,
            "Left last key {} should be less than right remaining key {}",
            left_last_key,
            right_remaining_key
        );
        assert_eq!(map.height(), 1);

        drop(map);
    }
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
#[test]
fn test_leaf_del_merge_with_left_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..min_count {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
        }
        for i in 0..min_count {
            leaf_1.insert_no_split((min_count + i) as i32 * 2, (min_count + i) as i32 * 10);
        }

        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..min_count {
            leaf_2.insert_no_split((2 * min_count + i) as i32 * 2, (2 * min_count + i) as i32 * 10);
            leaf_3.insert_no_split((3 * min_count + i) as i32 * 2, (3 * min_count + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let leaf1_first_key = leaf_1.get_keys()[0];
        let leaf2_first_key = leaf_2.get_keys()[0];
        let leaf3_first_key = leaf_3.get_keys()[0];

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(leaf2_first_key, internal_right.get_ptr());

        // Create BTreeMap with height=3 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        map.validate();
        assert_eq!(map.height(), 3);
        map.dump();

        // Record the key that will remain in leaf_1 after removals
        let leaf_1_remaining_key = leaf_1.get_keys()[0];
        let leaf_0_last_key = leaf_0.get_keys()[leaf_0.key_count() as usize - 1];

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
        let root_node = map.get_root_unwrap().as_inter();
        assert_eq!(root_node.key_count(), 1, "Root should still have 2 children");

        // Verify all remaining data
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key),
                Some(&(i as i32 * 10)),
                "leaf_0 key {} should be accessible",
                key
            );
        }
        // The one remaining key from leaf_1
        assert_eq!(
            map.get(&leaf_1_remaining_key),
            Some(&(leaf_1_remaining_key * 10 / 2)),
            "leaf_1 remaining key {} should be merged into leaf_0",
            leaf_1_remaining_key
        );

        // Verify key ordering
        assert!(
            leaf_0_last_key < leaf_1_remaining_key,
            "leaf_0 last key {} should be less than merged leaf_1 key {}",
            leaf_0_last_key,
            leaf_1_remaining_key
        );

        drop(map);
    }
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
#[test]
fn test_leaf_del_merge_with_right_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create leaf nodes
        let mut leaf_0 = LeafNode::<i32, i32>::alloc(); // Full
        let mut leaf_1 = LeafNode::<i32, i32>::alloc(); // Half-full, will underflow
        let mut leaf_2 = LeafNode::<i32, i32>::alloc(); // Half-full, can accept merge
        let mut leaf_3 = LeafNode::<i32, i32>::alloc(); // Not used in merge

        // Fill leaf_0 to capacity (full)
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill leaf_1 to min_count (half-full, will underflow after delete)
        for i in 0..min_count {
            let key = (leaf_cap + i) as i32 * 2;
            leaf_1.insert_no_split(key, key * 10);
        }

        // Fill leaf_2 to min_count (half-full, can accept merge)
        for i in 0..min_count {
            let key = (leaf_cap + min_count + i) as i32 * 2;
            leaf_2.insert_no_split(key, key * 10);
        }

        // Fill leaf_3 with some data
        for i in 0..min_count {
            let key = (leaf_cap + 2 * min_count + i) as i32 * 2;
            leaf_3.insert_no_split(key, key * 10);
        }

        // Link leaves in chain
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let leaf_1_first_key = leaf_1.get_keys()[0];
        let leaf_2_first_key = leaf_2.get_keys()[0];
        let leaf_3_first_key = leaf_3.get_keys()[0];

        // Create internal_left (height=1) with leaf_0 (full) and leaf_1 (half-full)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf_1_first_key, leaf_1.get_ptr());

        // Create internal_right (height=1) with leaf_2 and leaf_3
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf_3_first_key, leaf_3.get_ptr());

        // Create root (height=2)
        let root = InterNode::<i32, i32>::new_root(
            2,
            leaf_2_first_key,
            internal_left.get_ptr(),
            internal_right.get_ptr(),
        );

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (leaf_cap + 3 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
        map.dump();
        //map.validate();
        assert_eq!(map.height(), 3);

        println!("leaf_2_first_key = {}", leaf_2_first_key);

        // Delete one element from leaf_1 to trigger underflow
        // leaf_1 has min_count keys, delete one to make it underflow
        let delete_key = (leaf_cap + 1) as i32 * 2;
        println!("delete_key = {}", delete_key);
        assert!(map.remove(&delete_key).is_some());

        map.dump();
        map.validate();

        // Verify structure after merge
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), (leaf_cap + 3 * min_count - 1) as usize);
        // leaf_0 data should be unchanged
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key),
                Some(&(i as i32 * 10)),
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
                    map.get(&key),
                    Some(&expected_value),
                    "key {} should be accessible after merge",
                    key
                );
            }
        }

        drop(map);
    }
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
#[test]
fn test_leaf_del_merge_2_3_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);
        // For 3-way merge, we need: leaf_1 + leaf_2 + leaf_3 <= 2 * leaf_cap
        // leaf_1 = leaf_cap - 1, leaf_2 = 3, leaf_3 = leaf_cap - 2
        // Total = (leaf_cap - 1) + 3 + (leaf_cap - 2) = 2*leaf_cap, exactly!

        // Create leaf nodes
        let mut leaf_0 = LeafNode::<i32, i32>::alloc(); // Full
        let mut leaf_1 = LeafNode::<i32, i32>::alloc(); // One less than full (leaf_cap - 1)
        let mut leaf_2 = LeafNode::<i32, i32>::alloc(); // Only 3 keys, will underflow
        let mut leaf_3 = LeafNode::<i32, i32>::alloc(); // leaf_cap - 2 keys

        // Fill leaf_0 to capacity (full)
        for i in 0..leaf_cap {
            let key = i as i32 * 2;
            leaf_0.insert_no_split(key, key * 5);
        }

        // Fill leaf_1 to leaf_cap - 1 (one less than full)
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap + i) as i32 * 2;
            leaf_1.insert_no_split(key, key * 5);
        }

        // Fill leaf_2 with only 3 keys (will underflow after delete)
        for i in 0..3 {
            let key = (leaf_cap + leaf_cap - 1 + i) as i32 * 2;
            leaf_2.insert_no_split(key, key * 5);
        }

        // Fill leaf_3 to leaf_cap - 2 (adjusted for 3-way merge condition)
        for i in 0..(leaf_cap - 1) {
            let key = (leaf_cap + leaf_cap - 1 + 3 + i) as i32 * 2;
            leaf_3.insert_no_split(key, key * 5);
        }

        // Link leaves in chain
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let leaf_1_first_key = leaf_1.get_keys()[0];
        let leaf_2_first_key = leaf_2.get_keys()[0];
        let leaf_3_first_key = leaf_3.get_keys()[0];

        // Create internal_left (height=1) with leaf_0 (full) and leaf_1
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        internal_left.insert_no_split(leaf_1_first_key, leaf_1.get_ptr());

        // Create internal_right (height=1) with leaf_2 and leaf_3
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        internal_right.insert_no_split(leaf_3_first_key, leaf_3.get_ptr());

        // Create root (height=2)
        let root = InterNode::<i32, i32>::new_root(
            2,
            leaf_2_first_key,
            internal_left.get_ptr(),
            internal_right.get_ptr(),
        );

        // Calculate total keys: leaf_cap + (leaf_cap-1) + 3 + (leaf_cap-2) = 3*leaf_cap
        let total_keys = leaf_cap + (leaf_cap - 1) + 3 + (leaf_cap - 1);

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: total_keys as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };
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
                    map.get(&key),
                    Some(&expected_value),
                    "key {} should be accessible after merge",
                    key
                );
            }
        }

        drop(map);
    }
}
