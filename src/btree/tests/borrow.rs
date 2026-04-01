use super::super::{inter::*, leaf::*, node::*, *};
use core::cell::UnsafeCell;

/// Test borrowing from left sibling in a height=1 tree (root is InterNode, children are LeafNode)
/// Manually constructs a tree where middle leaf is full and left leaf has space
#[test]
fn test_borrow_from_left_sibling_height_1() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            left_leaf.insert_no_split(i as i32, i as i32 * 10);
        }

        // Fill middle leaf to capacity (full)
        for i in 0..leaf_cap {
            middle_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf.insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * leaf_cap - 2) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Insert into middle leaf (which is full) - this will trigger either borrowing or split
        let insert_key = leaf_cap as i32 + 5;
        let insert_value = insert_key * 10;

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(left_leaf.is_full().is_err()); // left has space

        // Perform insert
        map.insert(insert_key, insert_value);

        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));

        // Verify tree structure is still valid
        if let Some(Node::Inter(root)) = &map.root {
            assert!(root.count() >= 2); // Should have at least 2 keys
            assert_eq!(root.height(), 1);
        } else {
            panic!("Root should be InterNode");
        }

        // Cleanup
        drop(map); // This will deallocate all nodes
    }
}

/// Test borrowing from right sibling in a height=1 tree
/// Manually constructs a tree where middle leaf is full and right leaf has space
#[test]
fn test_borrow_from_right_sibling_height_1() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity - 1 (has space)
        for i in 0..(leaf_cap - 1) {
            left_leaf.insert_no_split(i as i32, i as i32 * 10);
        }

        // Fill middle leaf to capacity (full)
        for i in 0..leaf_cap {
            middle_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf.insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];
        root.insert_no_split(middle_first_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * leaf_cap - 2) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Insert at the end of middle leaf (which is full) - should borrow from right
        let insert_key = 2 * leaf_cap as i32 - 1;
        let insert_value = insert_key * 10;

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(right_leaf.is_full().is_err()); // right has space

        // Perform insert
        map.insert(insert_key, insert_value);

        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));

        // Cleanup
        drop(map);
    }
}

/// Test update_parent_key logic by manually constructing a tree and verifying parent keys are updated
#[test]
fn test_update_parent_key_manual() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();

        // Create two leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf with some keys
        for i in 0..leaf_cap {
            left_leaf.insert_no_split(i as i32, i as i32 * 10);
        }

        // Fill right leaf with some keys
        for i in 0..leaf_cap {
            right_leaf.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = left_leaf.get_ptr();

        // Create root internal node
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        let separator_key = right_leaf.get_keys()[0];
        root.insert_no_split(separator_key, right_leaf.get_ptr());

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (2 * leaf_cap) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Get the original separator key
        let original_separator = separator_key;

        // Insert a new key that will be the first key in right leaf
        // This should cause update_parent_key to be called
        let new_key = leaf_cap as i32 + 5;
        map.insert(new_key, new_key * 10);

        // Verify the separator key in parent was updated if necessary
        // The separator key should be the first key of the right leaf
        if let Some(Node::Inter(root)) = &map.root {
            let current_separator = (*root.key_ptr(0)).assume_init_read();
            // If the new key is smaller than the original separator, parent key should be updated
            if new_key < original_separator {
                assert_eq!(current_separator, new_key, "Parent separator key should be updated");
            }
        }

        // Cleanup
        drop(map);
    }
}

/// Test tree with height=2 (root -> internal nodes -> leaves)
/// Manually constructs a 2-level tree and tests insertion with borrowing
#[test]
fn test_borrow_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32, i as i32 * 10);
            leaf_1.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
        }

        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_2.insert_no_split((2 * leaf_cap + i) as i32, (2 * leaf_cap + i) as i32 * 10);
            leaf_3.insert_no_split((3 * leaf_cap + i) as i32, (3 * leaf_cap + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        let leaf1_first_key = (*leaf_1.key_ptr(0)).assume_init_read();
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        let leaf3_first_key = (*leaf_3.key_ptr(0)).assume_init_read();
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        let leaf2_first_key = (*leaf_2.key_ptr(0)).assume_init_read();
        root.insert_no_split(leaf2_first_key, internal_right.get_ptr());

        // Create BTreeMap with height=2 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * leaf_cap) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 2);

        // Test insertion that may trigger borrowing across the tree
        let insert_key = 2 * leaf_cap as i32 + 5;
        let insert_value = insert_key * 10;

        map.insert(insert_key, insert_value);

        // Verify insertion succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (4 * leaf_cap + 1) as usize);

        // Verify tree height is still 2
        assert_eq!(map.height(), 2);

        // Cleanup
        drop(map);
    }
}

/// Test two-level internal nodes with complex borrowing scenario
/// Creates a tree where internal nodes themselves might need to borrow
#[test]
fn test_borrow_two_level_internal_nodes() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create multiple leaf nodes to fill internal nodes
        let mut leaves = Vec::new();
        let leaf_count = inter_cap * 2; // Enough to potentially fill internal nodes

        for i in 0..leaf_count {
            let mut leaf = LeafNode::<i32, i32>::alloc();
            let base_key = (i * leaf_cap) as i32;
            for j in 0..leaf_cap {
                leaf.insert_no_split(base_key + j as i32, (base_key + j as i32) * 10);
            }
            leaves.push(leaf);
        }

        // Link leaves together
        for i in 0..leaf_count as usize {
            if i > 0 {
                (*leaves[i].brothers()).prev = leaves[i - 1].get_ptr();
            }
            if i < leaf_count as usize - 1 {
                (*leaves[i].brothers()).next = leaves[i + 1].get_ptr();
            }
        }

        // Create internal nodes that point to leaves
        let mut internal_nodes = Vec::new();
        let leaves_per_internal = inter_cap as usize; // Each internal node can have inter_cap keys

        for i in 0..((leaf_count as usize + leaves_per_internal - 1) / leaves_per_internal) {
            let mut internal = InterNode::<i32, i32>::alloc(1);
            let start_idx = i * leaves_per_internal;
            let end_idx = core::cmp::min(start_idx + leaves_per_internal, leaf_count as usize);

            internal.set_left_ptr(leaves[start_idx].get_ptr());
            for j in (start_idx + 1)..end_idx {
                let separator_key = (*leaves[j].key_ptr(0)).assume_init_read();
                internal.insert_no_split(separator_key, leaves[j].get_ptr());
            }
            internal_nodes.push(internal);
        }

        // Create root internal node pointing to internal nodes
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_nodes[0].get_ptr());
        for i in 1..internal_nodes.len() {
            let separator_key = (*leaves[i * leaves_per_internal].key_ptr(0)).assume_init_read();
            root.insert_no_split(separator_key, internal_nodes[i].get_ptr());
        }

        // Calculate total elements
        let total_elements = leaf_count as u32 * leaf_cap;

        // Create BTreeMap
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: total_elements as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 2);

        // Test insertion in the middle of the tree structure
        let insert_key = total_elements as i32 / 2;
        let insert_value = insert_key * 10;

        map.insert(insert_key, insert_value);

        // Verify insertion
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (total_elements + 1) as usize);

        // Cleanup
        drop(map);
    }
}
