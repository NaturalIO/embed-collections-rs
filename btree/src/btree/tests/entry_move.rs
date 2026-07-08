use super::*;

// --- Forward Peaking & Moving Group ---

#[test]
fn test_occupied_move_forward_height_2() {
    let mut builder = TreeBuilder::<u32, u32>::default();
    let leaf_cap = builder.leaf_cap();
    // Construct Root -> [leaf0 | sep1 | leaf1]
    let mut leaf0 = builder.new_leaf();
    let mut leaf1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf0, i * 2, i * 10);
    }
    builder.insert_leaf(&mut leaf1, leaf_cap * 2, leaf_cap * 10);
    let root = builder.new_root(1, leaf1.get_keys()[0], leaf0.get_ptr(), leaf1.get_ptr());
    let mut map = builder.build(root.into());
    assert_eq!(map.len(), leaf_cap as usize + 1);
    assert_eq!(map.leaf_count(), 2);
    assert_eq!(map.inter_count(), 1);
    map.validate();

    if let Entry::Occupied(mut ent) = map.entry(0) {
        ent.validate_cache_path();
        assert_eq!(ent.get(), &0);

        assert_eq!(ent.peek_forward(), Some((&2, &10)));
        ent = ent.move_forward().expect("can move");
        assert_eq!(ent.key(), &2);
        assert_eq!(ent.get(), &10);
        ent.validate_cache_path();
        // multi move delay PathCache adjustment
        for _ in 1..(leaf_cap - 1) {
            ent = ent.move_forward().expect("can move");
        }
        let leaf0_last = leaf_cap - 1;
        assert_eq!(ent.key(), &(leaf0_last * 2));
        assert_eq!(ent.get(), &(leaf0_last * 10));
        ent.validate_cache_path();

        // next leaf
        assert_eq!(ent.peek_forward(), Some((&(leaf_cap * 2), &(leaf_cap * 10))));
        ent = ent.move_forward().expect("can move");
        assert_eq!(ent.key(), &(leaf_cap * 2));
        assert_eq!(ent.get(), &(leaf_cap * 10));
        ent.validate_cache_path();

        // last
        assert_eq!(ent.peek_forward(), None);
        ent = ent.move_forward().unwrap_err();
        assert_eq!(ent.key(), &(leaf_cap * 2));
        assert_eq!(ent.get(), &(leaf_cap * 10));
        ent.validate_cache_path();
    } else {
        unreachable!("0 should exist");
    }
}

#[test]
fn test_occupied_move_backward_height_2() {
    let mut builder = TreeBuilder::<u32, u32>::default();
    let leaf_cap = builder.leaf_cap();
    // Construct Root -> [leaf0 | sep1 | leaf1]
    let mut leaf0 = builder.new_leaf();
    let mut leaf1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf0, i * 2, i * 10);
    }
    builder.insert_leaf(&mut leaf1, leaf_cap * 2, leaf_cap * 10);
    let root = builder.new_root(1, leaf1.get_keys()[0], leaf0.get_ptr(), leaf1.get_ptr());
    let mut map = builder.build(root.into());
    assert_eq!(map.len(), leaf_cap as usize + 1);
    assert_eq!(map.leaf_count(), 2);
    assert_eq!(map.inter_count(), 1);
    map.validate();

    if let Entry::Occupied(mut ent) = map.entry(leaf_cap * 2) {
        ent.validate_cache_path();
        assert_eq!(ent.key(), &(leaf_cap * 2));
        assert_eq!(ent.get(), &(leaf_cap * 10));
        // move cross leaf
        let leaf0_last = leaf_cap - 1;
        assert_eq!(ent.peek_backward(), Some((&(leaf0_last * 2), &(leaf0_last * 10))));
        ent = ent.move_backward().expect("can move");
        assert_eq!(ent.key(), &(leaf0_last * 2));
        assert_eq!(ent.get(), &(leaf0_last * 10));
        ent.validate_cache_path();

        // move adjacent

        let prev = leaf_cap - 2;
        assert_eq!(ent.peek_backward(), Some((&(prev * 2), &(prev * 10))));
        ent = ent.move_backward().expect("can move");
        assert_eq!(ent.key(), &(prev * 2));
        assert_eq!(ent.get(), &(prev * 10));
        ent.validate_cache_path();

        // multi move delay PathCache adjustment
        for _ in 0..(leaf_cap - 2) {
            ent = ent.move_backward().expect("can move");
        }
        assert_eq!(ent.key(), &0);
        assert_eq!(ent.get(), &0);
        ent.validate_cache_path();

        // first
        assert_eq!(ent.peek_backward(), None);
        ent = ent.move_backward().unwrap_err();
        assert_eq!(ent.key(), &0);
        ent.validate_cache_path();
        assert_eq!(ent.get(), &0);
    } else {
        unreachable!("{leaf_cap} should exist");
    }
}

#[test]
fn test_occupied_forward_same_leaf_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10i32, 100i32);
    map.insert(20i32, 200i32);
    map.insert(30i32, 300i32);

    if let Entry::Occupied(oe) = map.entry(10) {
        assert_eq!(*oe.key(), 10);
        // Peak forward
        assert_eq!(*oe.peek_forward().unwrap().0, 20);
        // Move forward
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 20);
        assert_eq!(*oe.peek_forward().unwrap().0, 30);
        // Move forward again
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 30);
        assert!(oe.peek_forward().is_none());
        assert!(oe.move_forward().is_err());
    } else {
        panic!("should be occupied");
    }
}

#[test]
fn test_occupied_forward_cross_leaf_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap();

    // Fill one leaf and start another
    for i in 0..cap + 5 {
        map.insert(i as i32, i as i32 * 10);
    }

    // Get entry at end of first leaf
    let end_of_first = cap as i32 - 1;
    if let Entry::Occupied(oe) = map.entry(end_of_first) {
        assert_eq!(oe.idx as usize, (cap - 1) as usize);
        // Peak should cross leaf
        assert_eq!(*oe.peek_forward().unwrap().0, cap as i32);
        // Move should cross leaf
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), cap as i32);
        assert_eq!(oe.idx, 0); // First element of next leaf
    } else {
        panic!("entry missing");
    }
}

#[test]
fn test_vacent_move_forward_height_2() {
    let mut builder = TreeBuilder::<u32, u32>::default();
    let leaf_cap = builder.leaf_cap();
    // Construct Root -> [leaf0 | sep1 | leaf1]
    let mut leaf0 = builder.new_leaf();
    let mut leaf1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf0, i * 2, i * 10);
    }
    builder.insert_leaf(&mut leaf1, leaf_cap * 2, leaf_cap * 10);
    let root = builder.new_root(1, leaf1.get_keys()[0], leaf0.get_ptr(), leaf1.get_ptr());
    let mut map = builder.build(root.into());
    assert_eq!(map.len(), leaf_cap as usize + 1);
    assert_eq!(map.leaf_count(), 2);
    assert_eq!(map.inter_count(), 1);
    map.validate();

    if let Entry::Vacant(ent) = map.entry(1) {
        assert_eq!(ent.key(), &1);
        assert_eq!(ent.idx, 1);

        // adjacent
        assert_eq!(ent.peek_forward(), Some((&2, &10)));
        let o_ent = ent.move_forward().expect("can move");
        assert_eq!(o_ent.key(), &2);
        assert_eq!(o_ent.get(), &10);
        o_ent.validate_cache_path();
    } else {
        unreachable!("should not exist");
    }

    let bound_key = (leaf_cap - 1) * 2 + 1;
    if let Entry::Vacant(ent) = map.entry(bound_key) {
        assert_eq!(ent.key(), &bound_key);
        // the node is full, so it's on the cap
        assert_eq!(ent.idx, leaf_cap);

        // next leaf
        assert_eq!(ent.peek_forward(), Some((&(leaf_cap * 2), &(leaf_cap * 10))));
        let o_ent = ent.move_forward().expect("can move");
        assert_eq!(o_ent.key(), &(leaf_cap * 2));
        assert_eq!(o_ent.get(), &(leaf_cap * 10));
        o_ent.validate_cache_path();
    } else {
        unreachable!("should not exist");
    }
    if let Entry::Vacant(mut ent) = map.entry(leaf_cap * 2 + 1) {
        assert_eq!(ent.idx, 1);
        // last node
        assert_eq!(ent.peek_forward(), None);
        ent = ent.move_forward().unwrap_err();
        assert_eq!(ent.key(), &(leaf_cap * 2 + 1));
    } else {
        unreachable!("should not exist");
    }
}

#[test]
fn test_vacent_move_backward_height_2() {
    let mut builder = TreeBuilder::<u32, u32>::default();
    let leaf_cap = builder.leaf_cap();
    // Construct Root -> [leaf0 | sep1 | leaf1]
    let mut leaf0 = builder.new_leaf();
    let mut leaf1 = builder.new_leaf();
    for i in 0..leaf_cap {
        builder.insert_leaf(&mut leaf0, i * 2 + 1, i * 10);
    }
    builder.insert_leaf(&mut leaf1, leaf_cap * 2 + 1, leaf_cap * 10);

    // make sure leaf_cap * 2 falls into leaf1, although it does not exist
    let root = builder.new_root(1, leaf_cap * 2, leaf0.get_ptr(), leaf1.get_ptr());
    let mut map = builder.build(root.into());
    assert_eq!(map.len(), leaf_cap as usize + 1);
    assert_eq!(map.leaf_count(), 2);
    assert_eq!(map.inter_count(), 1);
    map.validate();

    if let Entry::Vacant(ent) = map.entry(2) {
        assert_eq!(ent.key(), &2);
        assert_eq!(ent.idx, 1);

        // adjacent
        assert_eq!(ent.peek_backward(), Some((&1, &0)));
        let o_ent = ent.move_backward().expect("can move");
        assert_eq!(o_ent.key(), &1);
        assert_eq!(o_ent.get(), &0);
        o_ent.validate_cache_path();
    } else {
        unreachable!("should not exist");
    }

    let bound_key = leaf_cap * 2;
    if let Entry::Vacant(ent) = map.entry(bound_key) {
        assert_eq!(ent.key(), &bound_key);
        assert_eq!(ent.idx, 0);

        // previous leaf
        let pre_key = (leaf_cap - 1) * 2 + 1;
        let pre_value = (leaf_cap - 1) * 10;
        assert_eq!(ent.peek_backward(), Some((&pre_key, &pre_value)));
        let o_ent = ent.move_backward().expect("can move");
        assert_eq!(o_ent.key(), &pre_key);
        assert_eq!(o_ent.get(), &pre_value);
        o_ent.validate_cache_path();
    } else {
        unreachable!("should not exist");
    }
    // before first node
    if let Entry::Vacant(mut ent) = map.entry(0) {
        assert_eq!(ent.idx, 0);
        // last node
        assert_eq!(ent.peek_backward(), None);
        ent = ent.move_backward().unwrap_err();
        assert_eq!(ent.key(), &(0));
    } else {
        unreachable!("should not exist");
    }
}

#[test]
fn test_vacant_forward_point_to_element_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(30, 300);

    // Vacant entry at 20, idx should point to 30
    if let Entry::Vacant(ve) = map.entry(20) {
        // Point to 30 (same leaf)
        assert_eq!(*ve.peek_forward().unwrap().0, 30);
        let oe = ve.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 30);
    } else {
        panic!("should be vacant");
    }
}

#[test]
fn test_vacant_forward_at_leaf_end_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap();

    // Construct split
    for i in 0..cap {
        map.insert(i as i32 * 2, i as i32);
    }
    // Now leaf is full. Next insert will split.
    // Instead of inserting, we add an element that would be at the end of first leaf or start of second
    let last_key = (cap - 1) as i32 * 2;
    map.insert(1000, 1000); // Trigger split

    // Find where last_key is.
    if let Entry::Occupied(oe) = map.entry(last_key) {
        let leaf = oe.leaf.clone();
        if oe.idx as usize == leaf.key_count() as usize - 1 {
            // It is at the end of its leaf.
            // Vacant entry just after it should be at idx == key_count
            let search_key = last_key + 1;
            if let Entry::Vacant(ve) = map.entry(search_key) {
                assert_eq!(ve.idx as usize, leaf.key_count() as usize);
                // Should peek forward to next leaf
                let next_pair = ve.peek_forward();
                assert!(next_pair.is_some());
                assert!(*next_pair.unwrap().0 > search_key);

                let oe_next = ve.move_forward().ok().unwrap();
                assert!(*oe_next.key() > search_key);
            }
        }
    }
}

// --- Backward Peaking & Moving Group ---

#[test]
fn test_occupied_backward_same_leaf_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(20, 200);
    map.insert(30, 300);

    if let Entry::Occupied(oe) = map.entry(30) {
        assert_eq!(*oe.key(), 30);
        // Peak backward
        assert_eq!(*oe.peek_backward().unwrap().0, 20);
        // Move backward
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 20);
        assert_eq!(*oe.peek_backward().unwrap().0, 10);
        // Move backward again
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 10);
        assert!(oe.peek_backward().is_none());
        assert!(oe.move_backward().is_err());
    } else {
        panic!("should be occupied");
    }
}

#[test]
fn test_occupied_backward_cross_leaf_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap();

    for i in 0..cap + 5 {
        map.insert(i as i32, i as i32 * 10);
    }

    // Get entry at start of second leaf
    let start_of_second = cap as i32;
    if let Entry::Occupied(oe) = map.entry(start_of_second) {
        assert_eq!(oe.idx, 0);
        // Peak should cross leaf to left
        assert_eq!(*oe.peek_backward().unwrap().0, cap as i32 - 1);
        // Move should cross leaf
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), cap as i32 - 1);
        assert_eq!(oe.idx as usize, (cap - 1) as usize); // Last element of previous leaf
    } else {
        panic!("entry missing");
    }
}

#[test]
fn test_vacant_backward_same_leaf_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(30, 300);

    if let Entry::Vacant(ve) = map.entry(20) {
        assert_eq!(*ve.peek_backward().unwrap().0, 10);
        let oe = ve.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 10);
    } else {
        panic!("should be vacant");
    }
}

#[test]
fn test_vacant_backward_at_leaf_start_height1() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap();

    for i in 0..cap + 5 {
        map.insert(i as i32 * 2, i as i32);
    }

    let start_of_second = cap as i32 * 2;
    // search for key that would be at idx=0 of the second leaf
    let search_key = start_of_second - 1; // e.g. if leaf1 ends at 98, leaf2 starts at 100. search 99.

    if let Entry::Vacant(ve) = map.entry(search_key) {
        if ve.idx == 0 {
            // It is at the start of its leaf and root is InterNode
            assert_eq!(*ve.peek_backward().unwrap().0, start_of_second - 2);
            let oe = ve.move_backward().ok().unwrap();
            assert_eq!(*oe.key(), start_of_second - 2);
        }
    }
}

// --- Alter Key Group ---

#[test]
fn test_alter_key_height_1() {
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(20, 200);
    map.insert(30, 300);

    if let Entry::Occupied(mut oe) = map.entry(20) {
        // Violates left neighbor
        assert!(oe.alter_key(9).is_err());
        assert!(oe.alter_key(10).is_err());

        // Violates right neighbor
        assert!(oe.alter_key(30).is_err());
        assert!(oe.alter_key(31).is_err());

        // Safe update
        assert!(oe.alter_key(25).is_ok());
        assert_eq!(*oe.key(), 25);
    } else {
        unreachable!();
    }
    if let Entry::Occupied(mut oe) = map.entry(10) {
        // Safe update
        assert!(oe.alter_key(11).is_ok());
        assert_eq!(*oe.key(), 11);
        assert_eq!(oe.get(), &100);
        assert!(map.get(&10).is_none());
        assert_eq!(map.get(&11), Some(&100));
    } else {
        unreachable!();
    }
}

#[test]
fn test_alter_key_update_sep_height_2() {
    reset_alive_count();
    {
        let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
        // Construct Root -> [leaf0 | sep1 | leaf1]
        let mut leaf0 = builder.new_leaf();
        let mut leaf1 = builder.new_leaf();

        builder.insert_leaf(&mut leaf0, CounterI32::from(10), CounterI32::from(100));
        builder.insert_leaf(&mut leaf1, CounterI32::from(20), CounterI32::from(200));
        builder.insert_leaf(&mut leaf1, CounterI32::from(30), CounterI32::from(300));

        let mut root = builder.new_inter(1);
        root.set_left_ptr(leaf0.get_ptr());
        root.insert_no_split(CounterI32::from(20), leaf1.get_ptr());

        let mut map = builder.build(root.clone().into());
        assert_eq!(map.len(), 3);
        assert_eq!(map.leaf_count(), 2);
        map.validate();

        // Alter key 20 to 25
        if let Entry::Occupied(mut oe) = map.entry(CounterI32::from(20)) {
            assert!(oe.alter_key(CounterI32::from(25)).is_ok());
            // separator in root MUST be updated!
            assert_eq!(root.get_keys()[0], CounterI32::from(25));
        }
        map.validate();

        drop(map);
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_alter_key_after_move_update_sep_height_2() {
    reset_alive_count();
    {
        let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
        // Construct Root -> [leaf0 | sep1 | leaf1 | sep2 | leaf2]
        let mut leaf0 = builder.new_leaf();
        let mut leaf1 = builder.new_leaf();
        let mut leaf2 = builder.new_leaf();

        builder.insert_leaf(&mut leaf0, CounterI32::from(10), CounterI32::from(100));
        builder.insert_leaf(&mut leaf1, CounterI32::from(20), CounterI32::from(200));
        builder.insert_leaf(&mut leaf2, CounterI32::from(30), CounterI32::from(300));

        let mut root = builder.new_inter(1);
        root.set_left_ptr(leaf0.get_ptr());
        root.insert_no_split(CounterI32::from(20), leaf1.get_ptr());
        root.insert_no_split(CounterI32::from(30), leaf2.get_ptr());

        let mut map = builder.build(root.clone().into());
        assert_eq!(map.len(), 3);
        assert_eq!(map.leaf_count(), 3);
        assert_eq!(map.inter_count(), 1);
        map.validate();

        // Alter key 20 to 25
        if let Entry::Occupied(mut oe) = map.entry(CounterI32::from(30)) {
            oe = oe.move_backward().expect("can move");
            assert_eq!(oe.key(), &20);
            assert_eq!(oe.get(), &200);
            assert!(oe.alter_key(CounterI32::from(25)).is_ok());
            oe.validate_cache_path();
            // separator in root MUST be updated!
            assert_eq!(root.get_keys()[0], CounterI32::from(25));
        } else {
            unreachable!();
        }
        map.validate();
        assert_eq!(map.get(&25), Some(&CounterI32::from(200)));

        drop(map);
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_alter_key_update_sep_height_3() {
    reset_alive_count();
    {
        let mut builder = TreeBuilder::<CounterI32, CounterI32>::default();
        /*
          root (h=2) -> [InterL | sep_mid | InterR]
          InterL (h=1) -> [leaf0 | sep1 | leaf1]
          InterR (h=1) -> [leaf2 | sep3 | leaf3]
        */
        let mut leaf0 = builder.new_leaf();
        let mut leaf1 = builder.new_leaf();
        let mut leaf2 = builder.new_leaf();
        let mut leaf3 = builder.new_leaf();

        builder.insert_leaf(&mut leaf0, CounterI32::from(10), CounterI32::from(100));
        builder.insert_leaf(&mut leaf1, CounterI32::from(20), CounterI32::from(200));
        builder.insert_leaf(&mut leaf2, CounterI32::from(30), CounterI32::from(300));
        builder.insert_leaf(&mut leaf3, CounterI32::from(40), CounterI32::from(400));

        let mut inter_l = builder.new_inter(1);
        inter_l.set_left_ptr(leaf0.get_ptr());
        inter_l.insert_no_split(CounterI32::from(20), leaf1.get_ptr());

        let mut inter_r = builder.new_inter(1);
        inter_r.set_left_ptr(leaf2.get_ptr());
        inter_r.insert_no_split(CounterI32::from(40), leaf3.get_ptr());

        // root sep_mid is first key of inter_r (leaf2 first key = 30)
        let mut root = builder.new_inter(2);
        root.set_left_ptr(inter_l.get_ptr());
        root.insert_no_split(CounterI32::from(30), inter_r.get_ptr());

        let mut map = builder.build(root.clone().into());
        assert_eq!(map.len(), 4);
        assert_eq!(map.leaf_count(), 4);
        map.validate();

        // Alter key 30 (leaf2 first key) to 35
        if let Entry::Occupied(mut oe) = map.entry(CounterI32::from(30)) {
            assert!(oe.alter_key(CounterI32::from(35)).is_ok());
            // Root's separator key between InterL and InterR should be updated!
            assert_eq!(root.get_keys()[0], CounterI32::from(35));
        }
        map.validate();

        drop(map);
    }
    assert_eq!(alive_count(), 0);
}

// --- RangeTree Simulator Group ---

#[test]
fn test_rangetree_swallow_forward() {
    let mut map = BTreeMap::<u32, u32>::new();

    // Mimic RangeTree segments: [10, 20], [30, 10], [50, 10]
    map.insert(10, 20);
    map.insert(30, 10);
    map.insert(50, 10);

    // Task: add_and_merge(10, 55).
    // New range is [10, 65]. Should swallow (30, 10) and (50, 10).

    let target_end = 65;
    let mut oe = match map.entry(10) {
        Entry::Occupied(o) => o,
        _ => panic!("missing"),
    };

    while let Some((&ns, _)) = oe.peek_forward() {
        if ns > target_end {
            break;
        }
        // Swallow
        let next_oe = oe.move_forward().ok().expect("move fail");
        next_oe.remove();

        // Refetch/Keep base oe
        oe = match map.entry(10) {
            Entry::Occupied(o) => o,
            _ => panic!("lost"),
        };
    }

    // Final expansion
    *oe.get_mut() = target_end - 10;

    assert_eq!(map.len(), 1);
    assert_eq!(*map.get(&10).unwrap(), 55);
}
