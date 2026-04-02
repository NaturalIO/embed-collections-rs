use super::super::{leaf::*, *};
use core::ptr::NonNull;

#[test]
fn test_leaf_align() {
    {
        let cap = LeafNode::<u8, usize>::cap();
        println!("align u8 {}, cap {}", align_of::<u8>(), cap);
        let mut leaf = unsafe { LeafNode::<u8, usize>::alloc() };
        for i in 0..cap {
            leaf.insert_no_split(i as u8, i as usize);
        }
        for i in 0..cap {
            assert_eq!(leaf.get_keys()[i as usize], i as u8);
            assert_eq!(leaf.get_values()[i as usize], i as usize);
        }
        unsafe { leaf.dealloc() };
    }
    {
        let cap = LeafNode::<u8, u16>::cap();
        println!("align u16 {}, cap {}", align_of::<u16>(), cap);
        let mut leaf = unsafe { LeafNode::<u8, u16>::alloc() };
        for i in 0..cap {
            leaf.insert_no_split(i as u8, i as u16);
        }
        for i in 0..cap {
            assert_eq!(leaf.get_keys()[i as usize], i as u8);
            assert_eq!(leaf.get_values()[i as usize], i as u16);
        }
        unsafe { leaf.dealloc() };
    }
}

#[test]
fn test_leaf_node_search() {
    unsafe {
        let mut leaf = LeafNode::<usize, usize>::alloc();
        let cap = LeafNode::<usize, usize>::cap() as usize;
        // Insert sorted keys: 10, 20, 30, 40
        for k in 10..(cap + 10) {
            leaf.insert_no_split(k * 2, k * 2);
        }
        assert_eq!(leaf.key_count(), cap as u32);
        // Test search - existing key
        for k in 10..(cap + 10) {
            let (idx, found) = leaf.search(&(k * 2));
            assert!(found);
            assert_eq!(idx, (k - 10) as u32);
        }
        // Test search - key smaller than all
        let (idx, found) = leaf.search(&0);
        assert!(!found);
        assert_eq!(idx, 0);
        // non-existing key (should return insertion point)
        let (idx, found) = leaf.search(&21);
        assert!(!found);
        assert_eq!(idx, 1);

        // larger than max key
        let (idx, found) = leaf.search(&((cap + 11) * 2));
        assert!(!found);
        assert_eq!(idx as usize, cap);

        leaf.dealloc();
    }
}

/// Test leaf node split when inserting key at split_idx (new key < old key at split_idx)
#[test]
fn test_leaf_node_split_insert_at_split_idx_left() {
    unsafe {
        let mut leaf = LeafNode::<i32, i32>::alloc();
        let cap = LeafNode::<i32, i32>::cap();

        // Fill the leaf with keys 0..cap
        for i in 0..cap {
            // println!("insert {} {}", i, i*10);
            leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Insert key smaller than the key at split_idx
        let split_idx = (cap >> 1) as u32;
        let new_key = split_idx * 2 - 2 - 2 - 1; // odd key
        let new_value = new_key * 10;
        let (insert_idx, _is_equal) = leaf.search(&(new_key as i32));
        assert_eq!(insert_idx, split_idx - 2);
        assert!(!_is_equal);
        println!(
            "cap {cap} insert_idx {insert_idx} insert ({new_key}, {new_value}) split_idx {split_idx}"
        );

        let (mut new_leaf, _ptr_v) =
            leaf.insert_with_split(insert_idx, new_key as i32, new_value as i32);

        // Verify the split
        let left_count = leaf.key_count();
        let right_count = new_leaf.key_count();

        assert_eq!(left_count, split_idx + 1, "Left node should have keys");
        assert_eq!(left_count, insert_idx + 3, "Left node should have keys");
        assert_eq!(right_count, cap - split_idx, "Right node should have keys");
        assert_eq!(left_count + right_count, cap + 1, "Total keys should be cap + 1");

        for i in 0..insert_idx {
            assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32 * 2);
            assert_eq!((*leaf.value_ptr(i)).assume_init_read(), (i as i32) * 10);
        }
        // New key should be at split_idx in left node
        let found_key = (*leaf.key_ptr(insert_idx)).assume_init_ref();
        let found_value = (*leaf.value_ptr(insert_idx)).assume_init_ref();
        assert_eq!(*found_key, new_key as i32, "New key should be at split_idx in left node");
        assert_eq!(*found_value, new_value as i32, "New value should be at split_idx in left node");

        assert_eq!((*leaf.key_ptr(insert_idx + 1)).assume_init_read(), insert_idx as i32 * 2);
        assert_eq!((*leaf.value_ptr(insert_idx + 1)).assume_init_read(), insert_idx as i32 * 10);
        assert_eq!((*leaf.key_ptr(insert_idx + 2)).assume_init_read(), (insert_idx + 1) as i32 * 2);
        assert_eq!(
            (*leaf.value_ptr(insert_idx + 2)).assume_init_read(),
            (insert_idx + 1) as i32 * 10
        );

        for i in 0..(cap - split_idx) {
            assert_eq!((*new_leaf.key_ptr(i)).assume_init_read(), (i + split_idx) as i32 * 2);
            assert_eq!((*new_leaf.value_ptr(i)).assume_init_read(), (i + split_idx) as i32 * 10);
        }

        // Verify sibling pointers
        assert_eq!(
            (*leaf.brothers()).next,
            new_leaf.get_ptr(),
            "Left node's next should point to right node"
        );
        assert_eq!(
            (*new_leaf.brothers()).prev,
            leaf.get_ptr(),
            "Right node's prev should point to left node"
        );
        assert!((*leaf.brothers()).prev.is_null(), "Left node's prev should be null");
        assert!((*new_leaf.brothers()).next.is_null(), "Right node's next should be null");

        // Cleanup
        leaf.dealloc();
        new_leaf.dealloc();
    }
}

/// Test leaf node split when inserting key at split_idx (new key > old key at split_idx)
#[test]
fn test_leaf_node_split_insert_at_split_idx_right() {
    unsafe {
        let mut leaf = LeafNode::<i32, i32>::alloc();
        let cap = LeafNode::<i32, i32>::cap();
        // Fill the leaf with keys 0..cap
        for i in 0..cap {
            // println!("insert {} {}", i, i*10);
            leaf.insert_no_split(i as i32 * 2, i as i32 * 10);
        }

        // Insert key larger than the key at split_idx
        let split_idx = (cap >> 1) as u32;
        println!("split_idx {split_idx}");
        let new_key = split_idx * 2 + 1; // odd number
        let new_value = new_key * 10;
        let (insert_idx, _is_equal) = leaf.search(&(new_key as i32));
        assert_eq!(insert_idx, split_idx + 1);
        assert!(!_is_equal);

        let (mut new_leaf, _ptr_v) =
            leaf.insert_with_split(insert_idx, new_key as i32, new_value as i32);

        // Verify the split
        let left_count = leaf.key_count();
        let right_count = new_leaf.key_count();
        assert_eq!(left_count, split_idx, "Left node should have keys");
        assert!(right_count > 0, "Right node should have keys");
        assert_eq!(left_count + right_count, cap + 1, "Total keys should be cap + 1");
        for i in 0..split_idx {
            assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32 * 2);
            assert_eq!((*leaf.value_ptr(i)).assume_init_read(), i as i32 * 10);
        }
        assert_eq!((*new_leaf.key_ptr(0)).assume_init_read(), split_idx as i32 * 2);
        assert_eq!((*new_leaf.value_ptr(0)).assume_init_read(), split_idx as i32 * 10);

        let found_key = (*new_leaf.key_ptr(1)).assume_init_ref();
        let found_value = (*new_leaf.value_ptr(1)).assume_init_ref();
        assert_eq!(*found_key, new_key as i32, "New key should be at position 1 in right node");
        assert_eq!(
            *found_value, new_value as i32,
            "New value should be at position 1 in right node"
        );
        for i in 0..(cap - split_idx - 1) {
            // println!("checkout {i} {}", i+2);
            assert_eq!(
                (*new_leaf.key_ptr(i + 2)).assume_init_read(),
                (i + split_idx + 1) as i32 * 2
            );
            assert_eq!(
                (*new_leaf.value_ptr(i + 2)).assume_init_read(),
                (i + split_idx + 1) as i32 * 10
            );
        }
        // Cleanup
        leaf.dealloc();
        new_leaf.dealloc();
    }
}

/// Test leaf node split when inserting key at the end (index = cap)
#[test]
fn test_leaf_node_split_insert_at_end() {
    unsafe {
        let mut leaf = LeafNode::<i32, i32>::alloc();
        let cap = LeafNode::<i32, i32>::cap();
        // Fill the leaf with keys 0..cap
        for i in 0..cap {
            leaf.insert_no_split(i as i32, i as i32 * 10);
        }
        let new_key = cap as i32;
        let new_value = new_key * 10;

        let (mut new_leaf, _ptr_v) = leaf.insert_with_split(cap, new_key, new_value);
        assert_eq!(*_ptr_v, new_value);

        // Verify the split
        let left_count = leaf.key_count();
        let right_count = new_leaf.key_count();

        assert_eq!(left_count, cap, "Left node keys unchanged");
        assert_eq!(right_count, 1, "Right node should have keys");

        // New key should be at position 0 in right node
        let found_key = (*new_leaf.key_ptr(0)).assume_init_ref();
        let found_value = (*new_leaf.value_ptr(0)).assume_init_ref();
        assert_eq!(*found_key, new_key, "New key should be at position 0 in right node");
        assert_eq!(*found_value, new_value, "New value should be at position 0 in right node");
        for i in 0..cap {
            assert_eq!((*leaf.key_ptr(i)).assume_init_read(), i as i32);
            assert_eq!((*leaf.value_ptr(i)).assume_init_read(), (i as i32) * 10);
        }
        // Cleanup
        leaf.dealloc();
        new_leaf.dealloc();
    }
}

#[test]
fn test_btree_split_leaf_simple() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // First, fill exactly to capacity
    for i in 0..cap {
        assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        map.validate();
    }
    assert_eq!(map.len(), cap);

    // Verify all values
    for i in 0..cap {
        assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
    }

    // Now insert one more to trigger split - insert at the end
    assert_eq!(map.insert(cap as i32, cap as i32 * 10), None);
    map.validate();
    assert_eq!(map.len(), cap + 1);

    println!("verify after split");
    map.dump(); // Debug: dump tree structure

    // Verify all values including the new one
    for i in 0..=cap {
        assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)), "Failed to get key {}", i);
    }
}

#[test]
fn test_btree_split_leaf_insert_at_beginning() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // Fill to capacity
    for i in 0..cap {
        assert_eq!(map.insert(i as i32, i as i32 * 10), None);
        map.validate();
    }

    // Insert at the beginning (should trigger split and move to left)
    assert_eq!(map.insert(-1, -10), None);
    map.validate();
    assert_eq!(map.len(), cap + 1);

    // Verify the new key
    assert_eq!(map.get(&-1), Some(&-10));

    // Verify some original keys
    assert_eq!(map.get(&0), Some(&0));
    assert_eq!(map.get(&(cap as i32 - 1)), Some(&((cap - 1) as i32 * 10)));
}

#[test]
fn test_btree_split_leaf_insert_in_middle() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // Fill with even numbers: 0, 2, 4, 6, ...
    for i in 0..cap {
        assert_eq!(map.insert((i * 2) as i32, (i * 20) as i32), None);
        map.validate();
    }

    // Insert an odd number in the middle (cap - 1 is odd and not in the sequence)
    let insert_key = (cap - 1) as i32;
    assert_eq!(map.insert(insert_key, insert_key * 10), None);
    map.validate();
    assert_eq!(map.len(), cap + 1);

    // Verify the new key
    assert_eq!(map.get(&insert_key), Some(&(insert_key * 10)));

    // Verify some original keys
    assert_eq!(map.get(&0), Some(&0));
    assert_eq!(map.get(&2), Some(&20));
}

#[test]
fn test_btree_split_leaf_seq() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // Insert just enough to trigger one split
    for i in 0..(cap + 1) {
        map.insert(i as i32, i as i32 * 10);
        map.validate();
    }
    assert_eq!(map.len(), cap + 1);
}

#[test]
fn test_btree_split_leaf_verify_structure() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // Insert just enough to trigger one split
    let total = cap + 5;
    for i in 0..total {
        map.insert(i as i32, i as i32 * 10);
        map.validate();
    }

    assert_eq!(map.len(), total);

    // Now manually traverse the tree to verify structure
    if let Some(Node::Inter(root)) = &map.root {
        println!("Root has {} children", root.key_count() + 1);

        unsafe {
            // Check first child
            let child0_ptr = *root.child_ptr(0);
            assert!(!child0_ptr.is_null(), "Child 0 is null");

            // Try to access it as leaf
            let leaf0 = LeafNode::<i32, i32>::from_header(NonNull::new_unchecked(child0_ptr));
            println!("Leaf 0 has {} items", leaf0.key_count());

            // Check second child
            let child1_ptr = *root.child_ptr(1);
            if !child1_ptr.is_null() {
                let leaf1 = LeafNode::<i32, i32>::from_header(NonNull::new_unchecked(child1_ptr));
                println!("Leaf 1 has {} items", leaf1.key_count());
            }
        }
    }
}
