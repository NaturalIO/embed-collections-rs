use super::super::{inter::*, leaf::*, node::*, *};
use super::{CounterI32, alive_count, reset_alive_count};
use core::cell::UnsafeCell;

// --- Forward Peaking & Moving Group ---

#[test]
fn test_occupied_forward_same_leaf() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10i32, 100i32);
    map.insert(20i32, 200i32);
    map.insert(30i32, 300i32);

    if let Entry::Occupied(oe) = map.entry(10) {
        assert_eq!(*oe.key(), 10);
        // Peak forward
        assert_eq!(*oe.peak_forward().unwrap().0, 20);
        // Move forward
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 20);
        assert_eq!(*oe.peak_forward().unwrap().0, 30);
        // Move forward again
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 30);
        assert!(oe.peak_forward().is_none());
        assert!(oe.move_forward().is_err());
    } else {
        panic!("should be occupied");
    }
}

#[test]
fn test_occupied_forward_cross_leaf() {
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
        assert_eq!(*oe.peak_forward().unwrap().0, cap as i32);
        // Move should cross leaf
        let oe = oe.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), cap as i32);
        assert_eq!(oe.idx, 0); // First element of next leaf
    } else {
        panic!("entry missing");
    }
}

#[test]
fn test_vacant_forward_point_to_element() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(30, 300);

    // Vacant entry at 20, idx should point to 30
    if let Entry::Vacant(ve) = map.entry(20) {
        // Point to 30 (same leaf)
        assert_eq!(*ve.peak_forward().unwrap().0, 30);
        let oe = ve.move_forward().ok().unwrap();
        assert_eq!(*oe.key(), 30);
    } else {
        panic!("should be vacant");
    }
}

#[test]
fn test_vacant_forward_at_leaf_end() {
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
                // Should peak forward to next leaf
                let next_pair = ve.peak_forward();
                assert!(next_pair.is_some());
                assert!(*next_pair.unwrap().0 > search_key);

                let oe_next = ve.move_forward().ok().unwrap();
                assert!(*oe_next.key() > search_key);
            }
        }
    }
}

#[test]
fn test_forward_tree_end() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);

    // Occupied at end
    if let Entry::Occupied(oe) = map.entry(10) {
        assert!(oe.peak_forward().is_none());
        assert!(oe.move_forward().is_err());
    }

    // Vacant at end
    if let Entry::Vacant(ve) = map.entry(20) {
        assert!(ve.peak_forward().is_none());
        assert!(ve.move_forward().is_err());
    }
}

// --- Backward Peaking & Moving Group ---

#[test]
fn test_occupied_backward_same_leaf() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(20, 200);
    map.insert(30, 300);

    if let Entry::Occupied(oe) = map.entry(30) {
        assert_eq!(*oe.key(), 30);
        // Peak backward
        assert_eq!(*oe.peak_backward().unwrap().0, 20);
        // Move backward
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 20);
        assert_eq!(*oe.peak_backward().unwrap().0, 10);
        // Move backward again
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 10);
        assert!(oe.peak_backward().is_none());
        assert!(oe.move_backward().is_err());
    } else {
        panic!("should be occupied");
    }
}

#[test]
fn test_occupied_backward_cross_leaf() {
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
        assert_eq!(*oe.peak_backward().unwrap().0, cap as i32 - 1);
        // Move should cross leaf
        let oe = oe.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), cap as i32 - 1);
        assert_eq!(oe.idx as usize, (cap - 1) as usize); // Last element of previous leaf
    } else {
        panic!("entry missing");
    }
}

#[test]
fn test_vacant_backward_same_leaf() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);
    map.insert(30, 300);

    if let Entry::Vacant(ve) = map.entry(20) {
        assert_eq!(*ve.peak_backward().unwrap().0, 10);
        let oe = ve.move_backward().ok().unwrap();
        assert_eq!(*oe.key(), 10);
    } else {
        panic!("should be vacant");
    }
}

#[test]
fn test_vacant_backward_at_leaf_start() {
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
            assert_eq!(*ve.peak_backward().unwrap().0, start_of_second - 2);
            let oe = ve.move_backward().ok().unwrap();
            assert_eq!(*oe.key(), start_of_second - 2);
        }
    }
}

#[test]
fn test_backward_tree_start() {
    reset_alive_count();
    let mut map = BTreeMap::new();
    map.insert(10, 100);

    // Occupied at start
    if let Entry::Occupied(oe) = map.entry(10) {
        assert!(oe.peak_backward().is_none());
        assert!(oe.move_backward().is_err());
    }

    // Vacant at start
    if let Entry::Vacant(ve) = map.entry(5) {
        assert!(ve.peak_backward().is_none());
        assert!(ve.move_backward().is_err());
    }
}

// --- Alter Key Group ---

#[test]
fn test_alter_key_boundary_check() {
    reset_alive_count();
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
    }
}

#[test]
fn test_alter_key_update_sep_height_2() {
    unsafe {
        reset_alive_count();
        // Construct Root -> [leaf0 | sep1 | leaf1]
        let mut leaf0 = LeafNode::<CounterI32, CounterI32>::alloc();
        let mut leaf1 = LeafNode::<CounterI32, CounterI32>::alloc();

        leaf0.insert_no_split(CounterI32::from(10), CounterI32::from(100));
        leaf1.insert_no_split(CounterI32::from(20), CounterI32::from(200));
        leaf1.insert_no_split(CounterI32::from(30), CounterI32::from(300));

        (*leaf0.brothers()).next = leaf1.get_ptr();
        (*leaf1.brothers()).prev = leaf0.get_ptr();

        let mut root = InterNode::<CounterI32, CounterI32>::alloc(1);
        root.set_left_ptr(leaf0.get_ptr());
        root.insert_no_split(CounterI32::from(20), leaf1.get_ptr());

        let mut map = BTreeMap::<CounterI32, CounterI32> {
            root: Some(Node::Inter(root.clone())),
            len: 3,
            cache: UnsafeCell::new(PathCache::new()),
            leaf_count: 2,
            #[cfg(feature = "trace_log")]
            triggers: 0,
        };
        map.validate();

        // Alter key 20 to 25
        if let Entry::Occupied(mut oe) = map.entry(CounterI32::from(20)) {
            assert!(oe.alter_key(CounterI32::from(25)).is_ok());
            // separator in root MUST be updated!
            assert_eq!(root.get_keys()[0], CounterI32::from(25));
        }
        map.validate();

        drop(map);
        assert_eq!(alive_count(), 0);
    }
}

#[test]
fn test_alter_key_update_sep_height_3() {
    unsafe {
        reset_alive_count();
        /*
          root (h=2) -> [InterL | sep_mid | InterR]
          InterL (h=1) -> [leaf0 | sep1 | leaf1]
          InterR (h=1) -> [leaf2 | sep3 | leaf3]
        */
        let mut leaf0 = LeafNode::<CounterI32, CounterI32>::alloc();
        let mut leaf1 = LeafNode::<CounterI32, CounterI32>::alloc();
        let mut leaf2 = LeafNode::<CounterI32, CounterI32>::alloc();
        let mut leaf3 = LeafNode::<CounterI32, CounterI32>::alloc();

        leaf0.insert_no_split(CounterI32::from(10), CounterI32::from(100));
        leaf1.insert_no_split(CounterI32::from(20), CounterI32::from(200));
        leaf2.insert_no_split(CounterI32::from(30), CounterI32::from(300));
        leaf3.insert_no_split(CounterI32::from(40), CounterI32::from(400));

        // link leaves
        (*leaf0.brothers()).next = leaf1.get_ptr();
        (*leaf1.brothers()).prev = leaf0.get_ptr();
        (*leaf1.brothers()).next = leaf2.get_ptr();
        (*leaf2.brothers()).prev = leaf1.get_ptr();
        (*leaf2.brothers()).next = leaf3.get_ptr();
        (*leaf3.brothers()).prev = leaf2.get_ptr();

        let mut inter_l = InterNode::<CounterI32, CounterI32>::alloc(1);
        inter_l.set_left_ptr(leaf0.get_ptr());
        inter_l.insert_no_split(CounterI32::from(20), leaf1.get_ptr());

        let mut inter_r = InterNode::<CounterI32, CounterI32>::alloc(1);
        inter_r.set_left_ptr(leaf2.get_ptr());
        inter_r.insert_no_split(CounterI32::from(40), leaf3.get_ptr());

        // root sep_mid is first key of inter_r (leaf2 first key = 30)
        let mut root = InterNode::<CounterI32, CounterI32>::alloc(2);
        root.set_left_ptr(inter_l.get_ptr());
        root.insert_no_split(CounterI32::from(30), inter_r.get_ptr());

        let mut map = BTreeMap::<CounterI32, CounterI32> {
            root: Some(Node::Inter(root.clone())),
            len: 4,
            cache: UnsafeCell::new(PathCache::new()),
            leaf_count: 4,
            #[cfg(feature = "trace_log")]
            triggers: 0,
        };
        map.validate();

        // Alter key 30 (leaf2 first key) to 35
        if let Entry::Occupied(mut oe) = map.entry(CounterI32::from(30)) {
            assert!(oe.alter_key(CounterI32::from(35)).is_ok());
            // Root's separator key between InterL and InterR should be updated!
            assert_eq!(root.get_keys()[0], CounterI32::from(35));
        }
        map.validate();

        drop(map);
        assert_eq!(alive_count(), 0);
    }
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

    while let Some((&ns, _)) = oe.peak_forward() {
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
