use super::*;
use captains_log::logfn;
use rstest::rstest;
use std::println;

/// Test borrowing from left sibling in a height=2 tree (root is InterNode, children are LeafNode)
/// Manually constructs a tree where middle leaf is full and left leaf has space, insert to
/// middle_leaf[0], the original middle_leaf[0] is moved to left
#[logfn]
#[rstest]
fn test_borrow_from_left_insert_first_height_2(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();

    let leaf_cap = builder.leaf_cap();
    assert!(5 < leaf_cap);

    // Create three leaf nodes
    let mut left_leaf = builder.new_leaf();
    let mut middle_leaf = builder.new_leaf();
    let mut right_leaf = builder.new_leaf();

    // Fill left leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        let key = i as i32 * 2;
        //println!("insert {key} leaf_leaf {i}");
        builder.insert_leaf(&mut left_leaf, key, i as i32 * 10);
    }

    // Fill middle leaf to capacity (full)
    for i in 0..leaf_cap {
        let key = (leaf_cap + i) as i32 * 2;
        //println!("insert {key} middle_leaf {i}");
        builder.insert_leaf(&mut middle_leaf, key, (leaf_cap + i) as i32 * 10);
    }

    // Fill right leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        builder.insert_leaf(
            &mut right_leaf,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }

    let insert_key = leaf_cap as i32 * 2 - 1;
    // Insert into middle leaf (which is full) - this will trigger borrow, but the insert_key
    // will promote
    println!("insert_key {insert_key}");
    let insert_value = insert_key * 2 * 10 - 1;
    assert!(insert_key > left_leaf.get_keys()[left_leaf.key_count() as usize - 1]);
    let middle_first_key = middle_leaf.get_keys()[0];
    let right_first_key = right_leaf.get_keys()[0];
    assert!(insert_key < middle_first_key);
    let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
    assert!(!is_equal);
    assert_eq!(insert_idx, 0);
    println!("inserting key {insert_key} into middle_leaf idx {insert_idx}");

    // Create root internal node with height=1
    let mut root = builder.new_inter(1);
    root.set_left_ptr(left_leaf.get_ptr_mut());
    // make sure insert key will go into middle_leaf
    root.insert_no_split(insert_key, middle_leaf.get_ptr_mut());
    root.insert_no_split(right_first_key, right_leaf.get_ptr_mut());
    assert!(insert_key < middle_first_key);
    assert!(insert_key > left_leaf.get_keys()[left_leaf.key_count() as usize - 1]);
    assert!(middle_first_key < right_first_key);

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (3 * leaf_cap - 2) as usize);

    map.validate();

    // Verify middle leaf is full before insert
    assert!(middle_leaf.is_full());
    assert!(!left_leaf.is_full()); // left has space

    assert!(!map.contains_key(&insert_key));
    // Perform insert
    map.insert(insert_key, insert_value);
    map.validate();
    // middle_leaf is not changed
    assert_eq!(middle_leaf.get_keys()[0], middle_first_key);

    // Verify the insert succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));

    // Verify tree structure is still valid
    let root = map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 2);
    assert_eq!(root.height(), 1);
    // verify the splitter of middle_leaf has not changed
    assert_eq!(root.get_keys()[0], middle_first_key);

    assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);

    assert_eq!(map.leaf_count(), 3); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveLeft as u32 | TestFlag::UpdateSepKey as u32);
    drop(map); // This will deallocate all nodes
}

/// Test borrowing from left sibling in a height=2 tree (root is InterNode, children are LeafNode)
/// Manually constructs a tree where middle leaf is full and left leaf has space.
/// insert to the middle of middle_leaf, with middle_leaf.keys[0] moved to the left.
#[logfn]
#[rstest]
fn test_borrow_from_left_insert_mid_height_2(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    assert!(leaf_cap > 5);
    // Create three leaf nodes
    let mut left_leaf = builder.new_leaf();
    let mut middle_leaf = builder.new_leaf();
    let mut right_leaf = builder.new_leaf();

    // Fill left leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        builder.insert_leaf(&mut left_leaf, i as i32 * 2, i as i32 * 10);
    }

    // Fill middle leaf to capacity (full)
    for i in 0..leaf_cap {
        let key = (leaf_cap + i) as i32 * 2;
        //println!("insert {key} middle_leaf {i}");
        builder.insert_leaf(&mut middle_leaf, key, (leaf_cap + i) as i32 * 10);
    }

    // Fill right leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        builder.insert_leaf(
            &mut right_leaf,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }

    // Create root internal node with height=1
    let mut root = builder.new_inter(1);
    root.set_left_ptr(left_leaf.get_ptr_mut());
    let middle_first_key = middle_leaf.get_keys()[0];
    let right_first_key = right_leaf.get_keys()[0];
    root.insert_no_split(middle_first_key, middle_leaf.get_ptr_mut());
    root.insert_no_split(right_first_key, right_leaf.get_ptr_mut());
    assert!(left_leaf.get_keys()[0] < middle_first_key);
    assert!(middle_first_key < right_first_key);

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (3 * leaf_cap - 2) as usize);
    map.validate();

    // Insert into middle leaf (which is full) - this will trigger either borrowing or split
    let insert_key = leaf_cap as i32 * 2 + 5;
    let insert_value = insert_key * 10;
    assert!(insert_key > middle_first_key);
    let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
    assert!(insert_idx > 0);
    assert!(!is_equal);
    println!("inserting key {insert_key} into middle_leaf idx {insert_idx}");

    // Verify middle leaf is full before insert
    assert!(middle_leaf.is_full());
    assert!(!left_leaf.is_full()); // left has space
    let old_middle_leaf_key1 = middle_leaf.get_keys()[1];

    assert!(!map.contains_key(&insert_key));
    // Perform insert
    map.insert(insert_key, insert_value);
    map.validate();
    assert!(middle_leaf.get_keys()[0] != middle_first_key);
    assert_eq!(middle_leaf.get_keys()[0], old_middle_leaf_key1);
    println!("middle_leaf keys[0] {}", middle_leaf.get_keys()[0]);

    // Verify the insert succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);

    // Verify tree structure is still valid
    let root = &map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 2);
    assert_eq!(root.height(), 1);
    // verify the splitter of middle_leaf has changed
    assert_eq!(root.get_keys()[0], old_middle_leaf_key1);

    assert_eq!(map.leaf_count(), 3); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveLeft as u32 | TestFlag::UpdateSepKey as u32);

    // Cleanup
    drop(map); // This will deallocate all nodes
}

/// Test borrowing from right sibling in a height=2 tree.
/// Manually constructs a tree where middle leaf is full and right leaf has space.
/// The insert pos is at middle_leaf, the last node from middle_leaf should move to right_leaf.
#[logfn]
#[rstest]
fn test_borrow_from_right_height_2_not_last(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    println!("cap {}", leaf_cap);
    // Create three leaf nodes
    let mut left_leaf = builder.new_leaf();
    let mut middle_leaf = builder.new_leaf();
    let mut right_leaf = builder.new_leaf();

    // Fill left leaf to capacity full
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut left_leaf, i as i32 * 2, i as i32 * 10);
    }

    // Fill middle leaf to capacity full
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut middle_leaf,
            (leaf_cap + i) as i32 * 2,
            (leaf_cap + i) as i32 * 10,
        );
    }

    // Fill right leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        builder.insert_leaf(
            &mut right_leaf,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }

    // Create root internal node with height=1
    let mut root = builder.new_inter(1);
    root.set_left_ptr(left_leaf.get_ptr_mut());
    let middle_first_key = middle_leaf.get_keys()[0];
    let right_first_key = right_leaf.get_keys()[0];
    root.insert_no_split(middle_first_key, middle_leaf.get_ptr_mut());
    root.insert_no_split(right_first_key, right_leaf.get_ptr_mut());

    let middle_last_key = middle_leaf.get_keys()[middle_leaf.key_count() as usize - 1];

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);
    map.validate();

    assert_eq!(map.get_root_unwrap().into_inter().get_keys()[1], right_leaf.get_keys()[0]);

    // Insert at the end of middle leaf (which is full) - should borrow from right
    let insert_key = 2 * leaf_cap as i32 * 2 - 3;
    let insert_value = insert_key * 10;
    let (insert_idx, is_equal) = middle_leaf.search(&insert_key);
    assert!(!is_equal);
    assert!(insert_idx < leaf_cap);
    assert!(!map.contains_key(&insert_key));
    assert!(insert_key < middle_leaf.get_keys()[leaf_cap as usize - 1]);

    // Verify middle leaf is full before insert
    assert!(middle_leaf.is_full());
    assert!(!right_leaf.is_full()); // right has space

    // Perform insert
    assert!(map.insert(insert_key, insert_value).is_none());
    map.validate();
    // Verify the insert succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), 3 * leaf_cap as usize);

    // Verify tree structure is still valid
    let root = &map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 2);
    assert_eq!(root.height(), 1);
    // verify the splitter of right_leaf has changed
    assert_eq!(root.get_keys()[1], middle_last_key);

    assert_eq!(map.leaf_count(), 3); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveRight as u32 | TestFlag::UpdateSepKey as u32);
    // Cleanup
    drop(map);
}

/// Test borrowing from right sibling in a height=2 tree.
/// Manually constructs a tree where middle leaf is full and right leaf has space.
/// The insert pos is beyond middle_leaf, but still < right_leaf.
#[logfn]
#[rstest]
fn test_borrow_from_right_height_2_last(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    println!("cap {}", leaf_cap);

    // Create three leaf nodes
    let mut left_leaf = builder.new_leaf();
    let mut middle_leaf = builder.new_leaf();
    let mut right_leaf = builder.new_leaf();

    // Fill left leaf to capacity full
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut left_leaf, i as i32 * 2, i as i32 * 10);
    }

    // Fill middle leaf to capacity full
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut middle_leaf,
            (leaf_cap + i) as i32 * 2,
            (leaf_cap + i) as i32 * 10,
        );
    }

    // Fill right leaf to capacity - 1 (has space to borrow)
    for i in 0..(leaf_cap - 1) {
        builder.insert_leaf(
            &mut right_leaf,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }
    // Create root internal node with height=1
    let mut root = builder.new_inter(1);
    root.set_left_ptr(left_leaf.get_ptr_mut());
    let middle_first_key = middle_leaf.get_keys()[0];
    let right_first_key = right_leaf.get_keys()[0];
    root.insert_no_split(middle_first_key, middle_leaf.get_ptr_mut());
    root.insert_no_split(right_first_key, right_leaf.get_ptr_mut());

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (3 * leaf_cap - 1) as usize);
    map.validate();
    //map.dump();

    assert_eq!(map.get_root_unwrap().into_inter().get_keys()[1], right_leaf.get_keys()[0]);

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
    assert!(middle_leaf.is_full());
    assert!(!right_leaf.is_full()); // right has space

    // Perform insert
    assert!(map.insert(insert_key, insert_value).is_none());
    //map.dump();
    map.validate();
    // Verify the insert succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), 3 * leaf_cap as usize);

    // Verify tree structure is still valid
    let root = &map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 2);
    assert_eq!(root.height(), 1);
    // verify the splitter of right_leaf has changed
    assert_eq!(root.get_keys()[1], insert_key);

    assert_eq!(map.leaf_count(), 3); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveRight as u32 | TestFlag::UpdateSepKey as u32);
    // Cleanup
    drop(map);
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing.
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[logfn]
#[rstest]
fn test_borrow_from_left_insert_first_height_3(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    // Create leaf nodes for left branch
    let mut leaf_0 = builder.new_leaf();
    let mut leaf_1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf_0, i as i32 * 2, i as i32 * 10);
    }
    for i in 0..leaf_cap - 1 {
        builder.insert_leaf(&mut leaf_1, (leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
    }
    // Create leaf nodes for right branch
    let mut leaf_2 = builder.new_leaf();
    let mut leaf_3 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut leaf_2,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
        builder.insert_leaf(
            &mut leaf_3,
            (3 * leaf_cap + i) as i32 * 2,
            (3 * leaf_cap + i) as i32 * 10,
        );
    }

    let insert_key = leaf_cap as i32 * 4 - 1;
    // Insert into leaf_2 (which is full) - this will trigger borrow space from leaf_1 (for insert_key),
    // the leaf_2 first key will promote to root
    println!("insert_key {insert_key}");
    let insert_value = insert_key * 2 * 10 - 1;
    assert!(insert_key > leaf_1.get_keys()[leaf_1.key_count() as usize - 1]);
    assert!(insert_key < leaf_2.get_keys()[0]);
    let (insert_idx, is_equal) = leaf_2.search(&insert_key);
    assert!(!is_equal);
    assert_eq!(insert_idx, 0);
    println!("inserting key {insert_key} into leaf_2 idx {insert_idx}");

    // Create left internal node (height=1)
    let mut internal_left = builder.new_inter(1);
    internal_left.set_left_ptr(leaf_0.get_ptr_mut());
    let leaf1_first_key = leaf_1.get_keys()[0];
    internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr_mut());

    // Create right internal node (height=1)
    let mut internal_right = builder.new_inter(1);
    internal_right.set_left_ptr(leaf_2.get_ptr_mut());
    let leaf3_first_key = leaf_3.get_keys()[0];
    internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr_mut());

    // Create root internal node (height=2)
    let mut root = builder.new_inter(2);
    root.set_left_ptr(internal_left.get_ptr_mut());
    root.insert_no_split(insert_key, internal_right.get_ptr_mut());

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (4 * leaf_cap - 1) as usize);
    map.validate();

    assert_eq!(map.height(), 3);
    println!("len {}", map.len());

    map.insert(insert_key, insert_value);

    // Verify insertion succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), (4 * leaf_cap) as usize);

    // Verify tree height is still 3
    assert_eq!(map.height(), 3);
    let root = map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 1);
    // the root key has changed
    assert_eq!(root.get_keys()[0], leaf_2.get_keys()[0]);
    assert_eq!(internal_left.key_count(), 1);
    assert_eq!(internal_right.key_count(), 1);
    //map.dump();

    map.validate();
    assert_eq!(map.leaf_count(), 4); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveLeft as u32 | TestFlag::UpdateSepKey as u32);
    // Cleanup
    drop(map);
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[logfn]
#[rstest]
fn test_borrow_from_left_insert_mid_height_3(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    // Create leaf nodes for left branch
    let mut leaf_0 = builder.new_leaf();
    let mut leaf_1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf_0, i as i32 * 2, i as i32 * 10);
    }
    for i in 0..leaf_cap - 1 {
        builder.insert_leaf(&mut leaf_1, (leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
    }
    // Create leaf nodes for right branch
    let mut leaf_2 = builder.new_leaf();
    let mut leaf_3 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut leaf_2,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
        builder.insert_leaf(
            &mut leaf_3,
            (3 * leaf_cap + i) as i32 * 2,
            (3 * leaf_cap + i) as i32 * 10,
        );
    }

    let insert_key = leaf_cap as i32 * 4 + 1;
    // Insert into leaf_2 (which is full) - this will trigger borrow into leaf_1 for leaf_2 first key,
    // the insert_key will promote to root
    println!("insert_key {insert_key}");
    let insert_value = insert_key * 2 * 10 - 1;
    assert!(insert_key > leaf_1.get_keys()[leaf_1.key_count() as usize - 1]);
    let old_leaf_2_first = leaf_2.get_keys()[0];
    assert!(insert_key > old_leaf_2_first);
    let (insert_idx, is_equal) = leaf_2.search(&insert_key);
    assert!(!is_equal);
    assert_eq!(insert_idx, 1);
    println!("inserting key {insert_key} into leaf_2 idx {insert_idx}");

    // Create left internal node (height=1)
    let mut internal_left = builder.new_inter(1);
    internal_left.set_left_ptr(leaf_0.get_ptr_mut());
    let leaf1_first_key = leaf_1.get_keys()[0];
    internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr_mut());

    // Create right internal node (height=1)
    let mut internal_right = builder.new_inter(1);
    internal_right.set_left_ptr(leaf_2.get_ptr_mut());
    let leaf3_first_key = leaf_3.get_keys()[0];
    internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr_mut());

    // Create root internal node (height=2)
    let mut root = builder.new_inter(2);
    root.set_left_ptr(internal_left.get_ptr_mut());
    root.insert_no_split(old_leaf_2_first, internal_right.get_ptr_mut());

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (4 * leaf_cap - 1) as usize);
    map.validate();
    assert_eq!(map.height(), 3);

    map.insert(insert_key, insert_value);
    map.validate();

    // Verify insertion succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), (4 * leaf_cap) as usize);

    // Verify tree height is still 3
    assert_eq!(map.height(), 3);
    let root = map.get_root_unwrap().into_inter();
    // no split
    assert_eq!(root.key_count(), 1);
    // the root key has changed
    assert_eq!(root.get_keys()[0], insert_key);
    assert_eq!(internal_left.key_count(), 1);
    assert_eq!(internal_right.key_count(), 1);

    assert_eq!(map.leaf_count(), 4); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveLeft as u32 | TestFlag::UpdateSepKey as u32);
    // Cleanup
    drop(map);
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[logfn]
#[rstest]
fn test_borrow_from_right_insert_not_last_height_3(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    // Create leaf nodes for left branch
    let mut leaf_0 = builder.new_leaf();
    let mut leaf_1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf_0, i as i32 * 2, i as i32 * 10);
        builder.insert_leaf(&mut leaf_1, (leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
    }
    // Create leaf nodes for right branch
    let mut leaf_2 = builder.new_leaf();
    let mut leaf_3 = builder.new_leaf();
    for i in 0..leaf_cap - 1 {
        builder.insert_leaf(
            &mut leaf_2,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut leaf_3,
            (3 * leaf_cap + i) as i32 * 2,
            (3 * leaf_cap + i) as i32 * 10,
        );
    }

    let old_leaf_1_last = leaf_1.get_keys()[leaf_1.key_count() as usize - 1];
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
    let mut internal_left = builder.new_inter(1);
    internal_left.set_left_ptr(leaf_0.get_ptr_mut());
    let leaf1_first_key = leaf_1.get_keys()[0];
    internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr_mut());

    // Create right internal node (height=1)
    let mut internal_right = builder.new_inter(1);
    internal_right.set_left_ptr(leaf_2.get_ptr_mut());
    let leaf3_first_key = leaf_3.get_keys()[0];
    internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr_mut());

    // Create root internal node (height=2)
    let mut root = builder.new_inter(2);
    root.set_left_ptr(internal_left.get_ptr_mut());
    root.insert_no_split(old_leaf_2_first, internal_right.get_ptr_mut());
    println!("old_leaf_2_first {old_leaf_2_first}");

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (4 * leaf_cap - 1) as usize);
    map.validate();
    assert_eq!(map.height(), 3);

    map.insert(insert_key, insert_value);
    map.validate();

    assert_eq!(leaf_2.get_keys()[0], old_leaf_1_last);
    let root = map.get_root_unwrap().into_inter();
    assert_eq!(root.get_keys()[0], old_leaf_1_last);

    // Verify insertion succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), (4 * leaf_cap) as usize);

    // Verify tree height is still 3
    assert_eq!(map.height(), 3);
    // no split
    assert_eq!(root.key_count(), 1);
    // the root key has changed
    assert_eq!(internal_left.key_count(), 1);
    assert_eq!(internal_right.key_count(), 1);

    assert_eq!(map.leaf_count(), 4); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveRight as u32 | TestFlag::UpdateSepKey as u32);
    drop(map);
}

/// Test tree with height=3 (root -> internal nodes -> leaves)
/// Manually constructs a 3-level tree and tests insertion with borrowing
/// Test update_parent_key of leaf_2, which is the first node of internal_right.
#[logfn]
#[rstest]
fn test_borrow_from_right_insert_last_height_3(setup_log: ()) {
    let mut builder = TreeBuilder::<i32, i32>::default();
    let leaf_cap = builder.leaf_cap();
    // Create leaf nodes for left branch
    let mut leaf_0 = builder.new_leaf();
    let mut leaf_1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf_0, i as i32 * 2, i as i32 * 10);
        builder.insert_leaf(&mut leaf_1, (leaf_cap + i) as i32 * 2, (leaf_cap + i) as i32 * 10);
    }
    // Create leaf nodes for right branch
    let mut leaf_2 = builder.new_leaf();
    let mut leaf_3 = builder.new_leaf();
    for i in 0..leaf_cap - 1 {
        builder.insert_leaf(
            &mut leaf_2,
            (2 * leaf_cap + i) as i32 * 2,
            (2 * leaf_cap + i) as i32 * 10,
        );
    }
    for i in 0..leaf_cap {
        builder.insert_leaf(
            &mut leaf_3,
            (3 * leaf_cap + i) as i32 * 2,
            (3 * leaf_cap + i) as i32 * 10,
        );
    }

    let old_leaf_1_last = leaf_1.get_keys()[leaf_1.key_count() as usize - 1];
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
    let mut internal_left = builder.new_inter(1);
    internal_left.set_left_ptr(leaf_0.get_ptr_mut());
    let leaf1_first_key = leaf_1.get_keys()[0];
    internal_left.insert_no_split(leaf1_first_key, leaf_1.get_ptr_mut());

    // Create right internal node (height=1)
    let mut internal_right = builder.new_inter(1);
    internal_right.set_left_ptr(leaf_2.get_ptr_mut());
    let leaf3_first_key = leaf_3.get_keys()[0];
    internal_right.insert_no_split(leaf3_first_key, leaf_3.get_ptr_mut());

    // Create root internal node (height=2)
    let mut root = builder.new_inter(2);
    root.set_left_ptr(internal_left.get_ptr_mut());
    root.insert_no_split(old_leaf_2_first, internal_right.get_ptr_mut());
    println!("old_leaf_2_first {old_leaf_2_first}");

    let mut map = builder.build(root.into());
    assert_eq!(map.len(), (4 * leaf_cap - 1) as usize);
    map.validate();
    assert_eq!(map.height(), 3);

    map.insert(insert_key, insert_value);
    map.validate();

    assert_eq!(leaf_2.get_keys()[0], insert_key);
    let root = map.get_root_unwrap().into_inter();
    assert_eq!(root.get_keys()[0], insert_key);

    // Verify insertion succeeded
    assert_eq!(map.get(&insert_key), Some(&insert_value));
    assert_eq!(map.len(), (4 * leaf_cap) as usize);

    // Verify tree height is still 3
    assert_eq!(map.height(), 3);
    // no split
    assert_eq!(root.key_count(), 1);
    // the root key has changed
    assert_eq!(internal_left.key_count(), 1);
    assert_eq!(internal_right.key_count(), 1);
    assert_eq!(map.leaf_count(), 4); // unchanged
    #[cfg(feature = "trace_log")]
    assert_eq!(map.triggers, TestFlag::LeafMoveRight as u32 | TestFlag::UpdateSepKey as u32);
    drop(map);
}
