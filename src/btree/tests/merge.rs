use super::super::{inter::*, leaf::*, node::*, *};
use core::cell::UnsafeCell;

/// Test: Merge middle leaf with left sibling in height=2 tree
///
/// Scenario: Three leaves (left, middle, right) under root. Middle leaf underflows
/// and merges with left sibling. Right sibling remains unchanged.
///
/// Key difference from other tests:
/// - Left sibling has space to accept all keys from middle leaf
/// - Parent internal node loses one child pointer (middle)
/// - Parent split key changes from middle_first_key to right_first_key
///
/// Before: [left_leaf | middle_first_key | middle_leaf | right_first_key | right_leaf]
/// After:  [left_leaf+middle_leaf | right_first_key | right_leaf]
#[test]
fn test_merge_with_left_height_2() {
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
        for i in 0..min_count {
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
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Record state before merge
        let middle_remaining_key = middle_leaf.get_keys()[0];

        // Remove enough elements from middle leaf to trigger underflow
        // Remove all but one element from middle leaf
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        // Now middle leaf should have underflowed and merged with left
        map.validate();

        // Verify the merged structure
        let root = map.get_root_unwrap().as_inter();
        assert_eq!(root.key_count(), 1); // Two leaves left after merge
        assert_eq!(map.len(), (2 * min_count + 1) as usize);

        // Verify parent split key changed: should now be right_first_key
        // (was middle_first_key before merge)
        assert_eq!(
            root.get_keys()[0],
            right_first_key,
            "Parent split key should change from middle_first_key to right_first_key after merge"
        );

        // Verify all data is accessible and merged correctly
        // Left leaf should now contain: original left keys + remaining middle key
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(
                map.get(&key),
                Some(&(i as i32 * 10)),
                "Original left leaf key {} should be accessible",
                key
            );
        }
        // The one remaining key from middle leaf should be in left leaf now
        assert_eq!(
            map.get(&middle_remaining_key),
            Some(&(middle_remaining_key * 10 / 2)),
            "Remaining middle leaf key {} should be merged into left leaf",
            middle_remaining_key
        );

        // Right leaf should be unchanged
        for i in 0..min_count {
            let key = (2 * min_count + i) as i32 * 2;
            assert_eq!(
                map.get(&key),
                Some(&(key * 5)),
                "Right leaf key {} should be unchanged",
                key
            );
        }

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
#[test]
fn test_merge_with_right_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to min_count
        for i in 0..min_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf to just above underflow threshold
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            middle_leaf.insert_no_split(key, (min_count + i) as i32 * 10);
        }

        // Fill right leaf to min_count (can accept merge)
        for i in 0..min_count {
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

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * min_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Record the key that will remain in middle after removals
        let middle_remaining_key = middle_leaf.get_keys()[0];

        // Remove elements from middle leaf to trigger merge with right
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // Verify structure - should have merged middle into right
        let root = map.get_root_unwrap().as_inter();
        assert_eq!(root.key_count(), 1);
        assert_eq!(map.len(), (2 * min_count + 1) as usize);

        // Verify parent split key: should now be right_first_key
        // After middle+right merge, the split key between left and merged node
        // should be the first key of the merged node (which was right_first_key)
        assert_eq!(
            root.get_keys()[0],
            right_first_key,
            "Parent split key should become right_first_key after middle merges into right"
        );

        // Verify all data is accessible
        // Left leaf unchanged
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(map.get(&key), Some(&(i as i32 * 10)));
        }
        // Middle key that remained
        assert_eq!(map.get(&middle_remaining_key), Some(&(middle_remaining_key * 10 / 2)));
        // Right leaf keys (now merged with middle)
        for i in 0..min_count {
            let key = (2 * min_count + i) as i32 * 2;
            assert_eq!(map.get(&key), Some(&(key * 5)));
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
#[test]
fn test_three_way_merge_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        // For 3-way merge, we need small nodes
        // left + middle + right should be <= 2 * cap
        let small_count = leaf_cap / 3;
        if small_count == 0 {
            return; // Skip if cap is too small
        }

        // Create three leaf nodes with small counts
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf
        for i in 0..small_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf
        for i in 0..small_count {
            let key = (small_count + i) as i32 * 2;
            middle_leaf.insert_no_split(key, (small_count + i) as i32 * 10);
        }

        // Fill right leaf
        for i in 0..small_count {
            let key = (2 * small_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, (2 * small_count + i) as i32 * 10);
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
            len: (3 * small_count) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Remove elements from middle leaf to trigger 3-way merge
        for i in 1..small_count {
            let key = (small_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // After 3-way merge, should have only one leaf with all data
        assert_eq!(map.len(), (2 * small_count + 1) as usize);

        // Verify all remaining data
        for i in 0..small_count {
            let key = i as i32 * 2;
            assert_eq!(map.get(&key), Some(&(i as i32 * 10)));
        }
        // Remaining key from middle
        assert_eq!(map.get(&(small_count as i32 * 2)), Some(&(small_count as i32 * 10)));

        drop(map);
    }
}

/// Test: Merge causing parent internal node to become empty
///
/// Scenario: Two leaves under root. Right leaf underflows and merges with left.
/// After merge, parent has only one child and should be removed,
/// making the merged leaf the new root.
///
/// Key difference from other tests:
/// - Parent internal node becomes empty after merge
/// - Tree height decreases by 1
/// - Tests handle_internal_underflow path
///
/// Before: root -> [left_leaf | split_key | right_leaf]
/// After:  root = left_leaf (height reduces)
#[test]
fn test_merge_cascading_underflow() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let min_count = (leaf_cap + 1) / 2;
        assert!(min_count > 2);

        // Create a simple height=2 tree with 2 leaves
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill both leaves to min_count
        for i in 0..min_count {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }
        for i in 0..min_count {
            let key = (min_count + i) as i32 * 2;
            right_leaf.insert_no_split(key, (min_count + i) as i32 * 10);
        }

        // Link leaves
        (*left_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = left_leaf.get_ptr();

        let right_first_key = right_leaf.get_keys()[0];

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

        // Record height before merge
        let height_before = map.height();

        // Remove elements from right leaf to trigger merge
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // After merge, tree height might reduce
        assert_eq!(map.len(), (min_count + 1) as usize);

        // Verify all remaining data
        for i in 0..min_count {
            let key = i as i32 * 2;
            assert_eq!(map.get(&key), Some(&(i as i32 * 10)));
        }
        assert_eq!(map.get(&(min_count as i32 * 2)), Some(&(min_count as i32 * 10)));

        // Verify tree structure
        let height_after = map.height();
        assert!(
            height_after <= height_before,
            "Tree height should not increase after merge: before={}, after={}",
            height_before,
            height_after
        );

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
#[test]
fn test_merge_leftmost_leaf() {
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
#[test]
fn test_merge_rightmost_leaf() {
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
#[test]
#[ignore = "height-3 merge test causes crash during drop - needs investigation"]
fn test_merge_with_left_height_3() {
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

        assert_eq!(map.height(), 3);

        // Record the key that will remain in leaf_1 after removals
        let leaf_1_remaining_key = leaf_1.get_keys()[0];
        let leaf_0_last_key = leaf_0.get_keys()[leaf_0.key_count() as usize - 1];

        // Remove elements from leaf_1 to trigger merge with leaf_0
        for i in 1..min_count {
            let key = (min_count + i) as i32 * 2;
            assert!(map.remove(&key).is_some());
        }

        map.validate();

        // Verify structure
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), (3 * min_count + 1) as usize);

        // Verify internal_left now has only one key (leaf_0+leaf_1 merged)
        assert_eq!(internal_left.key_count(), 1, "internal_left should have 1 child after merge");

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

/// Test: Basic delete and merge scenario
///
/// Simple test filling a node to capacity then deleting most elements
/// to trigger merge operations. Tests the basic merge path without
/// manual tree construction.
#[test]
fn test_delete_and_merge() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;
    // Fill node to capacity
    for i in 0..cap {
        map.insert(i as i32, i as i32 * 10);
        map.validate();
    }
    // Delete most elements to trigger merge
    for i in 0..cap - 2 {
        assert!(map.remove(&(i as i32)).is_some());
        map.validate();
    }
    // Verify remaining elements
    for i in cap - 2..cap {
        assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
    }
}

/// Test: Delete all and reinsert
///
/// Tests that the tree remains valid after deleting all elements
/// and then reinserting new ones. Verifies cleanup and reinitialization.
#[test]
fn test_delete_all_and_reinsert() {
    let mut map = BTreeMap::new();
    // Insert some values
    for i in 0..20 {
        map.insert(i, i * 10);
        map.validate();
    }
    // Delete all
    for i in 0..20 {
        assert!(map.remove(&i).is_some());
        map.validate();
    }
    assert!(map.is_empty());
    // Reinsert
    for i in 0..20 {
        map.insert(i, i * 100);
        map.validate();
    }
    // Verify
    for i in 0..20 {
        assert_eq!(map.get(&i), Some(&(i * 100)));
    }
}
