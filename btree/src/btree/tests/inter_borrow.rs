use super::*;
use captains_log::logfn;
use rstest::rstest;
use std::println;
use std::vec::Vec;
use test_common::{CounterI32, alive_count, reset_alive_count};

/// Test Case 1: idx == 0, borrow from left sibling
/// When the first child of parent splits, and left sibling has space
#[logfn]
#[rstest]
fn test_inter_borrow_case1_rotate_left_first_child(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let inter_cap = builder.inter_cap();
    println!("leaf_cap {leaf_cap} inter_cap {inter_cap}");
    {
        // Create leaves for left_inter (has space)
        let mut leaf_0 = builder.new_leaf();
        let mut leaf_1 = builder.new_leaf();

        // Fill leaf_0 half capacity (has space)
        for i in 0..leaf_cap {
            builder.insert_leaf(
                &mut leaf_0,
                CounterI32::new(i as i32 * 2),
                CounterI32::new(i as i32 * 10),
            );
            builder.insert_leaf(
                &mut leaf_1,
                CounterI32::new((leaf_cap + i) as i32 * 2),
                CounterI32::new((leaf_cap + i) as i32 * 10),
            );
        }

        // Create left_inter with space
        let mut left_inter = builder.new_inter(1);
        left_inter.set_left_ptr(leaf_0.get_ptr());
        let leaf_1_first = leaf_1.get_keys()[0].clone();
        left_inter.insert_no_split(leaf_1_first, leaf_1.get_ptr());

        // Create leaves for right_inter
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();

        // Fill leaf_2 to capacity (will split)
        for i in 0..leaf_cap {
            let _k = (leaf_cap * 2 + i) as i32;
            builder.insert_leaf(&mut leaf_2, CounterI32::new(_k * 2), CounterI32::new(_k * 10));
        }
        for i in 0..leaf_cap {
            let _k = (leaf_cap * 3 + i) as i32;
            builder.insert_leaf(&mut leaf_3, CounterI32::new(_k * 2), CounterI32::new(_k * 10));
        }

        // Create right_inter full of keys
        let mut right_inter = builder.new_inter(1);
        right_inter.set_left_ptr(leaf_2.get_ptr());
        let leaf_3_split = leaf_3.get_keys()[0].clone();
        right_inter.insert_no_split(leaf_3_split, leaf_3.get_ptr());
        let base = (leaf_cap * 4) as i32;

        // Fill right_inter to capacity
        let mut dummy_leaves: Vec<LeafNode<CounterI32, CounterI32>> = Vec::new();
        for i in 0..(inter_cap - 1) as usize {
            let mut dummy = builder.new_leaf();
            let key = base + i as i32;
            builder.insert_leaf(&mut dummy, CounterI32::new(key * 2), CounterI32::new(key * 10));
            dummy_leaves.push(dummy);
        }
        for dummy in dummy_leaves.iter() {
            right_inter.insert_no_split(dummy.get_keys()[0].clone(), dummy.get_ptr());
        }
        // NOTE: dummy_leaves link is not setup

        // Create root
        let mut root = builder.new_inter(2);
        root.set_left_ptr(left_inter.get_ptr());
        // sep_key is just before leaf_2's first key
        let sep_key = CounterI32::new(*leaf_2.get_keys()[0] - 1);
        root.insert_no_split(sep_key.clone(), right_inter.get_ptr());

        let total_elements = (leaf_cap * 4 + (inter_cap - 1)) as usize;

        let mut map = builder.build(root.into());
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), total_elements);

        // map.dump();

        map.validate();

        // Insert into leaf_2's first position to trigger Case 1
        let insert_key = sep_key; // Just before leaf_2's first key
        let insert_key_raw = *insert_key;
        println!("Insert key: {}", insert_key);
        let insert_value = CounterI32::new(insert_key_raw * 10);
        map.insert(insert_key, insert_value);
        map.validate();
        // map.dump();

        assert_eq!(
            map.get(&CounterI32::new(insert_key_raw)),
            Some(&CounterI32::new(insert_key_raw * 10))
        );
        for i in 0..leaf_cap {
            let k = i as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap * 2) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap * 3) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
        }
        for dummy in dummy_leaves.iter() {
            let k = dummy.get_keys()[0].clone();
            assert_eq!(map.get(&k), Some(&CounterI32::new(*k * 5)));
        }
        drop(dummy_leaves);
        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::InterMoveLeftFirst as u32
                | TestFlag::InterMoveLeft as u32
                | TestFlag::LeafSplit as u32
        );
        assert_eq!(map.leaf_count(), 4 + inter_cap as usize);
        drop(map);
    }
    assert_eq!(alive_count(), 0, "alive_count should be 0 at end of test");
}

/// Test Case 2: idx == 2, borrow from left sibling
#[logfn]
#[rstest]
fn test_inter_borrow_case2_rotate_left(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let inter_cap = builder.inter_cap();
    println!("leaf_cap {leaf_cap} inter_cap {inter_cap}");
    {
        // Create leaves for left_inter (has space)
        let mut leaf_0 = builder.new_leaf();
        let mut leaf_1 = builder.new_leaf();

        // Fill leaf_0 half capacity (has space)
        for i in 0..leaf_cap {
            builder.insert_leaf(
                &mut leaf_0,
                CounterI32::new(i as i32 * 2),
                CounterI32::new(i as i32 * 10),
            );
            builder.insert_leaf(
                &mut leaf_1,
                CounterI32::new((leaf_cap + i) as i32 * 2),
                CounterI32::new((leaf_cap + i) as i32 * 10),
            );
        }

        // Create left_inter with space
        let mut left_inter = builder.new_inter(1);
        left_inter.set_left_ptr(leaf_0.get_ptr());
        let leaf_1_first = leaf_1.get_keys()[0].clone();
        left_inter.insert_no_split(leaf_1_first, leaf_1.get_ptr());

        // Create leaves for right_inter
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();
        let mut leaf_4 = builder.new_leaf();

        // Fill leaf_2 to capacity (will split)
        for i in 0..leaf_cap {
            let _k = (leaf_cap * 2 + i) as i32;
            builder.insert_leaf(&mut leaf_2, CounterI32::new(_k * 2), CounterI32::new(_k * 10));
            let _k = (leaf_cap * 3 + i) as i32;
            builder.insert_leaf(&mut leaf_3, CounterI32::new(_k * 2), CounterI32::new(_k * 10));
            let _k = (leaf_cap * 4 + i) as i32;
            builder.insert_leaf(&mut leaf_4, CounterI32::new(_k * 2), CounterI32::new(_k * 10));
        }

        // Create right_inter full of keys
        let mut right_inter = builder.new_inter(1);
        right_inter.set_left_ptr(leaf_2.get_ptr());
        let leaf_3_split = leaf_3.get_keys()[0].clone();
        right_inter.insert_no_split(leaf_3_split, leaf_3.get_ptr());
        let leaf_4_split = leaf_4.get_keys()[0].clone();
        right_inter.insert_no_split(leaf_4_split, leaf_4.get_ptr());
        let base = (leaf_cap * 5) as i32;

        // Fill right_inter to capacity
        let mut dummy_leaves: Vec<LeafNode<CounterI32, CounterI32>> = Vec::new();
        for i in 0..(inter_cap - 2) as usize {
            let mut dummy = builder.new_leaf();
            let key = base + i as i32;
            builder.insert_leaf(&mut dummy, CounterI32::new(key * 2), CounterI32::new(key * 10));
            dummy_leaves.push(dummy);
        }
        for dummy in dummy_leaves.iter() {
            right_inter.insert_no_split(dummy.get_keys()[0].clone(), dummy.get_ptr());
        }

        // Create root
        let mut root = builder.new_inter(2);
        root.set_left_ptr(left_inter.get_ptr());
        let sep_key = leaf_2.get_keys()[0].clone();
        root.insert_no_split(sep_key, right_inter.get_ptr());

        let mut map = builder.build(root.into());
        assert_eq!(map.height(), 3);
        // map.dump();

        map.validate();

        let _key = (leaf_cap * 3 + 2) as i32; // Just before leaf_2's first key
        let insert_key = CounterI32::new(_key * 2 + 1);
        let insert_value = CounterI32::new(_key * 10);
        println!("Insert key: {}", insert_key);
        map.insert(insert_key.clone(), insert_value.clone());
        map.validate();
        // map.dump();

        assert_eq!(map.get(&insert_key), Some(&insert_value));
        for i in 0..leaf_cap {
            let k = i as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap * 2) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap * 3) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
            let k = (i + leaf_cap * 4) as i32;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
        }
        for dummy in dummy_leaves.iter() {
            let k = dummy.get_keys()[0].clone();
            assert_eq!(map.get(&k), Some(&CounterI32::new(*k * 5)));
        }
        drop(dummy_leaves);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::InterMoveLeft as u32 | TestFlag::LeafSplit as u32);
        assert_eq!(map.leaf_count(), 4 + inter_cap as usize);
        drop(map);
    }
    assert_eq!(alive_count(), 0, "alive_count should be 0 at end of test");
}

/// Test Case 3: idx == key_count, borrow space from right sibling
///
/// Structure: root(grand) has [parent_inter | sep | right_inter]
/// - parent_inter: full, idx 0
/// - right_inter: has space (can receive rotated key)
#[logfn]
#[rstest]
fn test_inter_borrow_case3_rotate_right_last_child(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let inter_cap = builder.inter_cap();
    println!("leaf_cap {leaf_cap} inter_cap {inter_cap}");
    {
        let min_count = (leaf_cap + 1) / 2;

        let mut parent_inter = builder.new_inter(1);

        // Fill parent_inter to capacity (leave 0 space - it's full)
        let mut dummy_leaves: Vec<LeafNode<CounterI32, CounterI32>> = Vec::new();
        for i in 0..(inter_cap as i32 - 1) {
            let mut d = builder.new_leaf();
            builder.insert_leaf(&mut d, CounterI32::new(i * 2), CounterI32::new(i * 10));
            if i == 0 {
                parent_inter.set_left_ptr(d.get_ptr());
            } else {
                parent_inter.insert_no_split(CounterI32::new(i * 2), d.get_ptr());
            }
            dummy_leaves.push(d);
        }

        // parent_inter is full, its last child will split

        let mut leaf_0 = builder.new_leaf();
        let mut leaf_1 = builder.new_leaf(); // This will be the last child that splits

        let mut base = inter_cap as i32 - 1;
        for i in base..(base + leaf_cap as i32) {
            builder.insert_leaf(&mut leaf_0, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }

        parent_inter.insert_no_split(leaf_0.get_keys()[0].clone(), leaf_0.get_ptr());

        base += leaf_cap as i32;
        for i in base..(base + leaf_cap as i32) {
            builder.insert_leaf(&mut leaf_1, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }
        base += leaf_cap as i32;
        parent_inter.insert_no_split(leaf_1.get_keys()[0].clone(), leaf_1.get_ptr());

        // === Build right_inter with space ===
        let mut leaf_2 = builder.new_leaf();

        let mut leaf_3 = builder.new_leaf();

        for i in base..(base + leaf_cap as i32) {
            builder.insert_leaf(&mut leaf_2, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }
        base += leaf_cap as i32;
        for i in base..(base + min_count as i32) {
            builder.insert_leaf(&mut leaf_3, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }
        // right_inter: [leaf_2 | sep | leaf_3] has space for more keys
        let mut right_inter = builder.new_inter(1);
        right_inter.set_left_ptr(leaf_2.get_ptr());
        right_inter.insert_no_split(leaf_3.get_keys()[0].clone(), leaf_3.get_ptr());
        // right_inter has only 1 key, space for more

        // Create root
        let mut root = builder.new_inter(2);
        root.set_left_ptr(parent_inter.get_ptr());
        root.insert_no_split(leaf_2.get_keys()[0].clone(), right_inter.get_ptr());

        let total_elements = (leaf_cap * 3 + (inter_cap - 1) + min_count) as usize;

        let mut map = builder.build(root.into());
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), total_elements);
        // map.dump();

        map.validate();

        // Insert into leaf_1 (last child of parent_inter)
        let _key = (inter_cap - 1 + leaf_cap + leaf_cap / 2) as i32;
        let insert_key = CounterI32::new(_key * 2 - 1);
        let insert_value = CounterI32::new(_key * 10 - 1);
        println!("Insert key: {}", insert_key);
        map.insert(insert_key.clone(), insert_value.clone());
        map.validate();

        assert_eq!(map.get(&insert_key), Some(&insert_value));
        for k in 0..(inter_cap as i32 - 1) {
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
        }
        let mut base = inter_cap as i32 - 1;
        for i in base..(base + leaf_cap as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        base += leaf_cap as i32;
        for i in base..(base + leaf_cap as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        base += leaf_cap as i32;
        for i in base..(base + leaf_cap as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        base += leaf_cap as i32;
        for i in base..(base + min_count as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        drop(dummy_leaves);

        #[cfg(feature = "trace_log")]
        assert_eq!(
            map.triggers,
            TestFlag::InterMoveRightLast as u32
                | TestFlag::InterMoveRight as u32
                | TestFlag::LeafSplit as u32
        );
        assert_eq!(map.leaf_count(), 4 + inter_cap as usize);
        drop(map);
    }
    assert_eq!(alive_count(), 0, "alive_count should be 0 at end of test");
}

/// Test Case 4: idx < key_count, borrow space from right sibling
///
/// Structure: root(grand) has [parent_inter | sep | right_inter]
/// - parent_inter: full, idx 0
/// - right_inter: has space (can receive rotated key)
#[logfn]
#[rstest]
fn test_inter_borrow_case4_rotate_right(setup_log: ()) {
    reset_alive_count();
    let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
    let leaf_cap = builder.leaf_cap();
    let inter_cap = builder.inter_cap();
    println!("leaf_cap {leaf_cap} inter_cap {inter_cap}");
    {
        let min_count = (leaf_cap + 1) / 2;

        // === Build parent_inter (left sibling in grand) ===
        // parent_inter is full, its last child will split

        let mut leaf_0 = builder.new_leaf();
        let mut leaf_1 = builder.new_leaf(); // This will be the last child that splits

        for i in 0..leaf_cap {
            builder.insert_leaf(
                &mut leaf_0,
                CounterI32::new(i as i32 * 2),
                CounterI32::new(i as i32 * 10),
            );
            let k = (leaf_cap + i) as i32;
            builder.insert_leaf(&mut leaf_1, CounterI32::new(k * 2), CounterI32::new(k * 10));
        }

        let mut parent_inter = builder.new_inter(1);
        parent_inter.set_left_ptr(leaf_0.get_ptr());
        parent_inter.insert_no_split(leaf_1.get_keys()[0].clone(), leaf_1.get_ptr());

        let mut base = (leaf_cap * 2) as i32;
        // Fill parent_inter to capacity (leave 0 space - it's full)
        let mut dummy_leaves: Vec<LeafNode<CounterI32, CounterI32>> = Vec::new();
        for i in base..(base + inter_cap as i32 - 1) {
            let mut d = builder.new_leaf();
            builder.insert_leaf(&mut d, CounterI32::new(i * 2), CounterI32::new(i * 10));
            parent_inter.insert_no_split(CounterI32::new(i * 2), d.get_ptr());
            dummy_leaves.push(d);
        }
        base += inter_cap as i32 - 1;

        // === Build right_inter with space ===
        let mut leaf_2 = builder.new_leaf();
        let mut leaf_3 = builder.new_leaf();

        for i in base..(base + min_count as i32) {
            builder.insert_leaf(&mut leaf_2, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }
        base += min_count as i32;
        for i in base..(base + min_count as i32) {
            builder.insert_leaf(&mut leaf_3, CounterI32::new(i * 2), CounterI32::new(i * 10));
        }

        // right_inter: [leaf_2 | sep | leaf_3] has space for more keys
        let mut right_inter = builder.new_inter(1);
        right_inter.set_left_ptr(leaf_2.get_ptr());
        right_inter.insert_no_split(leaf_3.get_keys()[0].clone(), leaf_3.get_ptr());
        // right_inter has only 1 key, space for more

        // Create root
        let mut root = builder.new_inter(2);
        root.set_left_ptr(parent_inter.get_ptr());
        root.insert_no_split(leaf_2.get_keys()[0].clone(), right_inter.get_ptr());

        let total_elements = (leaf_cap * 2 + (inter_cap - 1) + min_count * 2) as usize;

        let mut map = builder.build(root.into());
        map.validate();
        assert_eq!(map.height(), 3);
        assert_eq!(map.len(), total_elements);

        // map.dump();

        // Insert into leaf_0 (last child of parent_inter)
        let _key = (leaf_cap / 2) as i32; // leaf_0 mid
        let insert_key = CounterI32::new(_key * 2 - 1);
        let insert_value = CounterI32::new(_key * 10 - 1);
        println!("Insert key: {}", insert_key);
        map.insert(insert_key.clone(), insert_value.clone());
        map.validate();

        assert_eq!(map.get(&insert_key), Some(&insert_value));
        for i in 0..leaf_cap as i32 {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
            let k = leaf_cap as i32 + i;
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)));
        }
        let mut base = (leaf_cap * 2) as i32;
        for k in base..(base + inter_cap as i32 - 1) {
            assert_eq!(map.get(&CounterI32::new(k * 2)), Some(&CounterI32::new(k * 10)), "{k}");
        }
        for i in base..(base + min_count as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        base += min_count as i32;
        for i in base..(base + min_count as i32) {
            assert_eq!(map.get(&CounterI32::new(i * 2)), Some(&CounterI32::new(i * 10)));
        }
        drop(dummy_leaves);
        #[cfg(feature = "trace_log")]
        assert_eq!(map.triggers, TestFlag::InterMoveRight as u32 | TestFlag::LeafSplit as u32);
        assert_eq!(map.leaf_count(), 4 + inter_cap as usize);
        drop(map);
    }
    assert_eq!(alive_count(), 0, "alive_count should be 0 at end of test");
}
