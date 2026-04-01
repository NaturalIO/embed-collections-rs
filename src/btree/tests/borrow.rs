use super::super::{inter::*, leaf::*, node::*, *};
use core::cell::UnsafeCell;

/// Test borrowing from left sibling in a height=2 tree (root is InterNode, children are LeafNode)
/// Manually constructs a tree where middle leaf is full and left leaf has space, insert to
/// middle_leaf[0], the original middle_leaf[0] is moved to left
#[test]
fn test_borrow_from_left_insert_first_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        assert!(5 < leaf_cap);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            let key = i as i32 * 2;
            //println!("insert {key} leaf_leaf {i}");
            left_leaf.insert_no_split(key, i as i32 * 10);
        }

        // Fill middle leaf to capacity (full)
        for i in 0..leaf_cap {
            let key = (leaf_cap + i) as i32 * 2;
            //println!("insert {key} middle_leaf {i}");
            middle_leaf.insert_no_split(key, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf
                .insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
        }

        // Link leaf nodes
        (*left_leaf.brothers()).next = middle_leaf.get_ptr();
        (*middle_leaf.brothers()).prev = left_leaf.get_ptr();
        (*middle_leaf.brothers()).next = right_leaf.get_ptr();
        (*right_leaf.brothers()).prev = middle_leaf.get_ptr();

        let insert_key = leaf_cap as i32 * 2 - 1;
        // Insert into middle leaf (which is full) - this will trigger borrow, but the insert_key
        // will promote
        println!("insert_key {insert_key}");
        let insert_value = insert_key * 2 * 10 - 1;
        assert!(insert_key > left_leaf.get_keys()[left_leaf.count() as usize - 1]);
        let middle_first_key = middle_leaf.get_keys()[0];
        let right_first_key = right_leaf.get_keys()[0];
        assert!(insert_key < middle_first_key);
        let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, 0);
        println!("inserting key {insert_key} into middle_leaf idx {insert_idx}");

        // Create root internal node with height=1
        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(left_leaf.get_ptr());
        // make sure insert key will go into middle_leaf
        root.insert_no_split(insert_key, middle_leaf.get_ptr());
        root.insert_no_split(right_first_key, right_leaf.get_ptr());
        assert!(insert_key < middle_first_key);
        assert!(insert_key > left_leaf.get_keys()[left_leaf.count() as usize - 1]);
        assert!(middle_first_key < right_first_key);

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * leaf_cap - 2) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(left_leaf.is_full().is_err()); // left has space
        let old_middle_leaf_key1 = middle_leaf.get_keys()[1];

        assert!(!map.contains_key(&insert_key));
        // Perform insert
        map.insert(insert_key, insert_value);
        // middle_leaf is not changed
        assert_eq!(middle_leaf.get_keys()[0], middle_first_key);

        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));

        // Verify tree structure is still valid
        let root = map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 2);
        assert_eq!(root.height(), 1);
        // verify the spliter of middle_leaf has not changed
        assert_eq!(root.get_keys()[0], middle_first_key);

        assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);

        // Cleanup
        drop(map); // This will deallocate all nodes
    }
}

/// Test borrowing from left sibling in a height=2 tree (root is InterNode, children are LeafNode)
/// Manually constructs a tree where middle leaf is full and left leaf has space.
/// insert to the middle of middle_leaf, with middle_leaf.keys[0] moved to the left.
#[test]
fn test_borrow_from_left_insert_mid_height_2() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        assert!(5 < leaf_cap);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf to capacity (full)
        for i in 0..leaf_cap {
            let key = (leaf_cap + i) as i32 * 2;
            //println!("insert {key} middle_leaf {i}");
            middle_leaf.insert_no_split(key, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf
                .insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
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
        assert!(left_leaf.get_keys()[0] < middle_first_key);
        assert!(middle_first_key < right_first_key);

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * leaf_cap - 2) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Insert into middle leaf (which is full) - this will trigger either borrowing or split
        let insert_key = leaf_cap as i32 * 2 + 5;
        let insert_value = insert_key * 10;
        assert!(insert_key > middle_first_key);
        let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
        assert!(insert_idx > 0);
        assert!(!is_equal);
        println!("inserting key {insert_key} into middle_leaf idx {insert_idx}");

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(left_leaf.is_full().is_err()); // left has space
        let old_middle_leaf_key1 = middle_leaf.get_keys()[1];

        assert!(!map.contains_key(&insert_key));
        // Perform insert
        map.insert(insert_key, insert_value);
        assert!(middle_leaf.get_keys()[0] != middle_first_key);
        assert_eq!(middle_leaf.get_keys()[0], old_middle_leaf_key1);
        println!("middle_leaf keys[0] {}", middle_leaf.get_keys()[0]);

        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);

        // Verify tree structure is still valid
        let root = &map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 2);
        assert_eq!(root.height(), 1);
        // verify the spliter of middle_leaf has changed
        assert_eq!(root.get_keys()[0], old_middle_leaf_key1);

        // Cleanup
        drop(map); // This will deallocate all nodes
    }
}

/// Test borrowing from right sibling in a height=2 tree.
/// Manually constructs a tree where middle leaf is full and right leaf has space.
/// The insert pos is at middle_leaf, the last node from middle_leaf should move to right_leaf.
#[test]
fn test_borrow_from_right_height_2_not_last() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        println!("cap {}", leaf_cap);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity full
        for i in 0..leaf_cap {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf to capacity full
        for i in 0..leaf_cap {
            middle_leaf.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf
                .insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
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

        let middle_last_key = middle_leaf.get_keys()[middle_leaf.count() as usize - 1];

        // Create BTreeMap with this structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (3 * leaf_cap - 1) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.get_root_unwrap().as_inter().get_keys()[1], right_leaf.get_keys()[0]);

        // Insert at the end of middle leaf (which is full) - should borrow from right
        let insert_key = 2 * leaf_cap as i32 * 2 - 3;
        let insert_value = insert_key * 10;
        let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
        assert!(!is_equal);
        assert!(insert_idx < leaf_cap);
        assert!(!map.contains_key(&insert_key));
        assert!(insert_key < middle_leaf.get_keys()[leaf_cap as usize - 1]);

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(right_leaf.is_full().is_err()); // right has space

        // Perform insert
        assert!(map.insert(insert_key, insert_value).is_none());
        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), 3 * leaf_cap as usize);

        // Verify tree structure is still valid
        let root = &map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 2);
        assert_eq!(root.height(), 1);
        // verify the spliter of right_leaf has changed
        assert_eq!(root.get_keys()[1], middle_last_key);

        // Cleanup
        drop(map);
    }
}

/// Test borrowing from right sibling in a height=2 tree.
/// Manually constructs a tree where middle leaf is full and right leaf has space.
/// The insert pos is beyond middle_leaf, but still < right_leaf.
#[test]
fn test_borrow_from_right_height_2_last() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        println!("cap {}", leaf_cap);

        // Create three leaf nodes
        let mut left_leaf = LeafNode::<i32, i32>::alloc();
        let mut middle_leaf = LeafNode::<i32, i32>::alloc();
        let mut right_leaf = LeafNode::<i32, i32>::alloc();

        // Fill left leaf to capacity full
        for i in 0..leaf_cap {
            left_leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Fill middle leaf to capacity full
        for i in 0..leaf_cap {
            middle_leaf.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }

        // Fill right leaf to capacity - 1 (has space to borrow)
        for i in 0..(leaf_cap - 1) {
            right_leaf
                .insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
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
            len: (3 * leaf_cap - 1) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.get_root_unwrap().as_inter().get_keys()[1], right_leaf.get_keys()[0]);

        // Insert at the end of middle leaf (which is full) - should borrow from right
        let insert_key = (2 * leaf_cap as i32 - 1) * 2 + 1;
        println!("insert_key {insert_key}");
        println!("right_leaf {}", right_leaf.get_keys()[0]);
        let insert_value = insert_key * 10;
        let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, leaf_cap);
        assert!(!map.contains_key(&insert_key));
        assert!(insert_key > middle_leaf.get_keys()[leaf_cap as usize - 1]);
        assert!(insert_key < right_leaf.get_keys()[0]);

        // Verify middle leaf is full before insert
        assert!(middle_leaf.is_full().is_ok());
        assert!(right_leaf.is_full().is_err()); // right has space

        // Perform insert
        assert!(map.insert(insert_key, insert_value).is_none());
        // Verify the insert succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), 3 * leaf_cap as usize);

        // Verify tree structure is still valid
        let root = &map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 2);
        assert_eq!(root.height(), 1);
        // verify the spliter of right_leaf has changed
        assert_eq!(root.get_keys()[1], insert_key);

        // Cleanup
        drop(map);
    }
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing.
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[test]
fn test_borrow_from_left_insert_first_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
        }
        for i in 0..leaf_cap - 1 {
            leaf_1.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }
        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_2.insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
            leaf_3.insert_no_split((3 * leaf_cap + i) as i32 * 2, (3 * leaf_cap + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let insert_key = leaf_cap as i32 * 4 - 1;
        // Insert into leaf_2 (which is full) - this will trigger borrow space from leaf_1 (for insert_key),
        // the leaf_2 first key will promote to root
        println!("insert_key {insert_key}");
        let insert_value = insert_key * 2 * 10 - 1;
        assert!(insert_key > leaf_1.get_keys()[leaf_1.count() as usize - 1]);
        assert!(insert_key < leaf_2.get_keys()[0]);
        let (insert_idx, is_equal) = leaf_2.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, 0);
        println!("inserting key {insert_key} into leaf_2 idx {insert_idx}");

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        let leaf1_first_key = leaf_1.get_keys()[0];
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        let leaf3_first_key = leaf_3.get_keys()[0];
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(insert_key, internal_right.get_ptr());

        // Create BTreeMap with height=2 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * leaf_cap) as usize - 1,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 3);

        map.insert(insert_key, insert_value);

        // Verify insertion succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (4 * leaf_cap) as usize);

        // Verify tree height is still 3
        assert_eq!(map.height(), 3);
        let root = map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 1);
        // the root key has changed
        assert_eq!(root.get_keys()[0], leaf_2.get_keys()[0]);
        assert_eq!(internal_left.count(), 1);
        assert_eq!(internal_right.count(), 1);

        // Cleanup
        drop(map);
    }
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[test]
fn test_borrow_from_left_insert_mid_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
        }
        for i in 0..leaf_cap - 1 {
            leaf_1.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }
        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_2.insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
            leaf_3.insert_no_split((3 * leaf_cap + i) as i32 * 2, (3 * leaf_cap + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let insert_key = leaf_cap as i32 * 4 + 1;
        // Insert into leaf_2 (which is full) - this will trigger borrow into leaf_1 for leaf_2 first key,
        // the insert_key will promote to root
        println!("insert_key {insert_key}");
        let insert_value = insert_key * 2 * 10 - 1;
        assert!(insert_key > leaf_1.get_keys()[leaf_1.count() as usize - 1]);
        let old_leaf_2_first = leaf_2.get_keys()[0];
        assert!(insert_key > old_leaf_2_first);
        let (insert_idx, is_equal) = leaf_2.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, 1);
        println!("inserting key {insert_key} into leaf_2 idx {insert_idx}");

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        let leaf1_first_key = leaf_1.get_keys()[0];
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        let leaf3_first_key = leaf_3.get_keys()[0];
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(old_leaf_2_first, internal_right.get_ptr());

        // Create BTreeMap with height=2 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * leaf_cap) as usize - 1,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 3);

        map.insert(insert_key, insert_value);

        // Verify insertion succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (4 * leaf_cap) as usize);

        // Verify tree height is still 3
        assert_eq!(map.height(), 3);
        let root = map.get_root_unwrap().as_inter();
        // no split
        assert_eq!(root.count(), 1);
        // the root key has changed
        assert_eq!(root.get_keys()[0], insert_key);
        assert_eq!(internal_left.count(), 1);
        assert_eq!(internal_right.count(), 1);

        // Cleanup
        drop(map);
    }
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[test]
fn test_borrow_from_right_insert_not_last_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
            leaf_1.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }
        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap - 1 {
            leaf_2.insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
        }
        for i in 0..leaf_cap {
            leaf_3.insert_no_split((3 * leaf_cap + i) as i32 * 2, (3 * leaf_cap + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let old_leaf_1_last = leaf_1.get_keys()[leaf_1.count() as usize - 1];
        let insert_key = old_leaf_1_last - 1;
        // Insert into leaf_1 (which is full) - this will trigger borrow space from leaf_2,
        // but the moved key to leaf_2 will be promoted
        println!("insert_key {insert_key}");
        let insert_value = insert_key * 2 * 10 - 1;
        let old_leaf_2_first = leaf_2.get_keys()[0];
        assert!(insert_key < old_leaf_2_first);
        let (insert_idx, is_equal) = leaf_1.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, leaf_cap - 1);
        println!("inserting key {insert_key} into leaf_1 idx {insert_idx}");

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        let leaf1_first_key = leaf_1.get_keys()[0];
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        let leaf3_first_key = leaf_3.get_keys()[0];
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(old_leaf_2_first, internal_right.get_ptr());
        println!("old_leaf_2_first {old_leaf_2_first}");

        // Create BTreeMap with height=2 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * leaf_cap) as usize - 1,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 3);

        map.insert(insert_key, insert_value);

        assert_eq!(leaf_2.get_keys()[0], old_leaf_1_last);
        let root = map.get_root_unwrap().as_inter();
        assert_eq!(root.get_keys()[0], old_leaf_1_last);

        // Verify insertion succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (4 * leaf_cap) as usize);

        // Verify tree height is still 3
        assert_eq!(map.height(), 3);
        // no split
        assert_eq!(root.count(), 1);
        // the root key has changed
        assert_eq!(internal_left.count(), 1);
        assert_eq!(internal_right.count(), 1);

        // Cleanup
        drop(map);
    }
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[test]
fn test_borrow_from_right_insert_last_height_3() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();
        let inter_cap = InterNode::<i32, i32>::cap();

        // Create leaf nodes for left branch
        let mut leaf_0 = LeafNode::<i32, i32>::alloc();
        let mut leaf_1 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap {
            leaf_0.insert_no_split(i as i32 * 2, i as i32 * 10);
            leaf_1.insert_no_split((leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
        }
        // Create leaf nodes for right branch
        let mut leaf_2 = LeafNode::<i32, i32>::alloc();
        let mut leaf_3 = LeafNode::<i32, i32>::alloc();
        for i in 0..leaf_cap - 1 {
            leaf_2.insert_no_split((2 * leaf_cap + i) as i32 * 2, (2 * leaf_cap + i) as i32 * 10);
        }
        for i in 0..leaf_cap {
            leaf_3.insert_no_split((3 * leaf_cap + i) as i32 * 2, (3 * leaf_cap + i) as i32 * 10);
        }

        // Link leaves
        (*leaf_0.brothers()).next = leaf_1.get_ptr();
        (*leaf_1.brothers()).prev = leaf_0.get_ptr();
        (*leaf_1.brothers()).next = leaf_2.get_ptr();
        (*leaf_2.brothers()).prev = leaf_1.get_ptr();
        (*leaf_2.brothers()).next = leaf_3.get_ptr();
        (*leaf_3.brothers()).prev = leaf_2.get_ptr();

        let old_leaf_1_last = leaf_1.get_keys()[leaf_1.count() as usize - 1];
        let insert_key = old_leaf_1_last + 1;
        // Insert into leaf_1 (which is full) - this will trigger borrow space from leaf_2,
        // but the insert_key insert into leaf_2, and insert_key will be promoted
        println!("insert_key {insert_key}");
        let insert_value = insert_key * 2 * 10 - 1;
        let old_leaf_2_first = leaf_2.get_keys()[0];
        assert!(insert_key < old_leaf_2_first);
        let (insert_idx, is_equal) = leaf_1.search(&insert_key);
        assert!(!is_equal);
        assert_eq!(insert_idx, leaf_cap);
        println!("inserting key {insert_key} into leaf_1 idx {insert_idx}");

        // Create left internal node (height=1)
        let mut internal_left = InterNode::<i32, i32>::alloc(1);
        internal_left.set_left_ptr(leaf_0.get_ptr());
        let leaf1_first_key = leaf_1.get_keys()[0];
        internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr());

        // Create right internal node (height=1)
        let mut internal_right = InterNode::<i32, i32>::alloc(1);
        internal_right.set_left_ptr(leaf_2.get_ptr());
        let leaf3_first_key = leaf_3.get_keys()[0];
        internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr());

        // Create root internal node (height=2)
        let mut root = InterNode::<i32, i32>::alloc(2);
        root.set_left_ptr(internal_left.get_ptr());
        root.insert_no_split(old_leaf_2_first, internal_right.get_ptr());
        println!("old_leaf_2_first {old_leaf_2_first}");

        // Create BTreeMap with height=2 structure
        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (4 * leaf_cap) as usize - 1,
            cache: UnsafeCell::new(PathCache::new()),
        };

        assert_eq!(map.height(), 3);

        map.insert(insert_key, insert_value);

        assert_eq!(leaf_2.get_keys()[0], insert_key);
        let root = map.get_root_unwrap().as_inter();
        assert_eq!(root.get_keys()[0], insert_key);

        // Verify insertion succeeded
        assert_eq!(map.get(&insert_key), Some(&insert_value));
        assert_eq!(map.len(), (4 * leaf_cap) as usize);

        // Verify tree height is still 3
        assert_eq!(map.height(), 3);
        // no split
        assert_eq!(root.count(), 1);
        // the root key has changed
        assert_eq!(internal_left.count(), 1);
        assert_eq!(internal_right.count(), 1);

        // Cleanup
        drop(map);
    }
}

/*
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
*/
