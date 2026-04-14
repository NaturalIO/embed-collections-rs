use super::super::{leaf::*, *};
use super::{CounterI32, alive_count, reset_alive_count};

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
        leaf.dealloc::<true>();
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
        leaf.dealloc::<true>();
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

        leaf.dealloc::<true>();
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

        let (new_leaf, _ptr_v) =
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
        leaf.dealloc::<true>();
        new_leaf.dealloc::<true>();
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

        let (new_leaf, _ptr_v) =
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
        leaf.dealloc::<true>();
        new_leaf.dealloc::<true>();
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

        let (new_leaf, _ptr_v) = leaf.insert_with_split(cap, new_key, new_value);
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
        leaf.dealloc::<true>();
        new_leaf.dealloc::<true>();
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
            let leaf0 = LeafNode::<i32, i32>::from_header(child0_ptr);
            println!("Leaf 0 has {} items", leaf0.key_count());

            // Check second child
            let child1_ptr = *root.child_ptr(1);
            if !child1_ptr.is_null() {
                let leaf1 = LeafNode::<i32, i32>::from_header(child1_ptr);
                println!("Leaf 1 has {} items", leaf1.key_count());
            }
        }
    }
}

#[test]
fn test_remove_pair_no_borrow_basic() {
    reset_alive_count();
    unsafe {
        let mut leaf = LeafNode::<CounterI32, CounterI32>::alloc();

        // Insert 5 pairs: (0,0), (10,100), (20,200), (30,300), (40,400)
        for i in 0..5 {
            leaf.insert_no_split((i * 10).into(), (i * 100).into());
        }
        assert_eq!(leaf.key_count(), 5);
        assert_eq!(alive_count(), 10);

        // Remove middle pair at index 2: removes (20, 200)
        let (k1, v1) = leaf.remove_pair_no_borrow(2);
        assert_eq!(k1, 20);
        assert_eq!(v1, 200);
        assert_eq!(leaf.key_count(), 4);
        assert_eq!(alive_count(), 10);
        // Verify remaining keys and values: [0, 10, 30, 40] and [0, 100, 300, 400]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 0);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 0);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(2)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(2)).assume_init_ref(), 300);
        assert_eq!(*(*leaf.key_ptr(3)).assume_init_ref(), 40);
        assert_eq!(*(*leaf.value_ptr(3)).assume_init_ref(), 400);

        // Remove first pair: removes (0, 0)
        let (k2, v2) = leaf.remove_pair_no_borrow(0);
        assert_eq!(k2, 0);
        assert_eq!(v2, 0);
        assert_eq!(leaf.key_count(), 3);
        assert_eq!(alive_count(), 10);
        // Verify remaining: [10, 30, 40] and [100, 300, 400]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 300);
        assert_eq!(*(*leaf.key_ptr(2)).assume_init_ref(), 40);
        assert_eq!(*(*leaf.value_ptr(2)).assume_init_ref(), 400);

        // Remove last pair at index 2: removes (40, 400)
        let (k3, v3) = leaf.remove_pair_no_borrow(2);
        assert_eq!(k3, 40);
        assert_eq!(v3, 400);
        assert_eq!(leaf.key_count(), 2);
        assert_eq!(alive_count(), 10);
        // Verify remaining: [10, 30] and [100, 300]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 300);

        // Drop removed pairs (alive = 4)
        drop(k1);
        drop(v1);
        drop(k2);
        drop(v2);
        drop(k3);
        drop(v3);
        assert_eq!(alive_count(), 4);

        // Dealloc leaf drops remaining 2 pairs (alive = 0)
        leaf.dealloc::<true>();
        assert_eq!(alive_count(), 0);
    }
}

#[test]
fn test_remove_pair_no_borrow_single_element() {
    reset_alive_count();
    unsafe {
        let mut leaf = LeafNode::<CounterI32, CounterI32>::alloc();

        leaf.insert_no_split(42.into(), 420.into());
        assert_eq!(leaf.key_count(), 1);
        assert_eq!(alive_count(), 2);

        let (k, v) = leaf.remove_pair_no_borrow(0);
        assert_eq!(k, 42);
        assert_eq!(v, 420);
        assert_eq!(leaf.key_count(), 0);
        assert_eq!(alive_count(), 2); // Moved out

        drop(k);
        drop(v);
        assert_eq!(alive_count(), 0);

        leaf.dealloc::<true>();
        assert_eq!(alive_count(), 0);
    }
}

#[test]
fn test_remove_value_no_borrow_basic() {
    reset_alive_count();
    unsafe {
        let mut leaf = LeafNode::<CounterI32, CounterI32>::alloc();

        // Insert 5 pairs: (0,0), (10,100), (20,200), (30,300), (40,400)
        for i in 0..5 {
            leaf.insert_no_split((i * 10).into(), (i * 100).into());
        }
        assert_eq!(leaf.key_count(), 5);
        assert_eq!(alive_count(), 10);

        // Remove value at index 2 - key 20 dropped, value 200 returned (alive = 9)
        let v1 = leaf.remove_value_no_borrow(2);
        assert_eq!(v1, 200);
        assert_eq!(leaf.key_count(), 4);
        assert_eq!(alive_count(), 9);
        // Verify remaining keys and values: [0, 10, 30, 40] and [0, 100, 300, 400]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 0);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 0);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(2)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(2)).assume_init_ref(), 300);
        assert_eq!(*(*leaf.key_ptr(3)).assume_init_ref(), 40);
        assert_eq!(*(*leaf.value_ptr(3)).assume_init_ref(), 400);

        // Remove value at index 0 - key 0 dropped (alive = 8)
        let v2 = leaf.remove_value_no_borrow(0);
        assert_eq!(v2, 0);
        assert_eq!(leaf.key_count(), 3);
        assert_eq!(alive_count(), 8);
        // Verify remaining: [10, 30, 40] and [100, 300, 400]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 300);
        assert_eq!(*(*leaf.key_ptr(2)).assume_init_ref(), 40);
        assert_eq!(*(*leaf.value_ptr(2)).assume_init_ref(), 400);

        // Remove value at index 2 - key 40 dropped (alive = 7)
        let v3 = leaf.remove_value_no_borrow(2);
        assert_eq!(v3, 400);
        assert_eq!(leaf.key_count(), 2);
        assert_eq!(alive_count(), 7);
        // Verify remaining: [10, 30] and [100, 300]
        assert_eq!(*(*leaf.key_ptr(0)).assume_init_ref(), 10);
        assert_eq!(*(*leaf.value_ptr(0)).assume_init_ref(), 100);
        assert_eq!(*(*leaf.key_ptr(1)).assume_init_ref(), 30);
        assert_eq!(*(*leaf.value_ptr(1)).assume_init_ref(), 300);

        // Drop returned values (alive = 4)
        drop(v1);
        drop(v2);
        drop(v3);
        assert_eq!(alive_count(), 4);

        // Dealloc remaining 2 pairs (alive = 0)
        leaf.dealloc::<true>();
        assert_eq!(alive_count(), 0);
    }
}

#[test]
fn test_remove_value_no_borrow_single_element() {
    reset_alive_count();
    unsafe {
        let mut leaf = LeafNode::<CounterI32, CounterI32>::alloc();

        leaf.insert_no_split(42.into(), 420.into());
        assert_eq!(leaf.key_count(), 1);
        assert_eq!(alive_count(), 2);

        // Remove value - key dropped, value returned (alive = 1)
        let v = leaf.remove_value_no_borrow(0);
        assert_eq!(v, 420);
        assert_eq!(leaf.key_count(), 0);
        assert_eq!(alive_count(), 1);

        // Drop value (alive = 0)
        drop(v);
        assert_eq!(alive_count(), 0);

        leaf.dealloc::<true>();
        assert_eq!(alive_count(), 0);
    }
}

/// Test insert_borrow_left - insert at index 1 (minimum valid idx)
/// Setup: left_node has [0, 1, 2], right_node (self) has [10, 20, 30, 40]
/// Operation: insert_borrow_left with idx=1, key=15, value=150
/// Expected: left_node becomes [0, 1, 2, 10], right_node becomes [15, 20, 30, 40]
#[test]
fn test_insert_borrow_left_at_idx_one() {
    unsafe {
        let mut left_node = LeafNode::<i32, i32>::alloc();
        let mut right_node = LeafNode::<i32, i32>::alloc();

        // Setup left_node with [0, 1, 2]
        for i in 0..3 {
            left_node.insert_no_split(i, i * 10);
        }

        // Setup right_node with [10, 20, 30, 40]
        for i in 1..5 {
            right_node.insert_no_split(i * 10, i * 100);
        }

        // Verify search returns correct idx for key=15
        let (idx, found) = right_node.search(&15);
        assert!(!found);
        assert_eq!(idx, 1, "key=15 should be inserted at idx=1");

        // Insert at idx=1, key=15, value=150
        let ptr_v = right_node.insert_borrow_left(&mut left_node, 1, 15, 150);
        assert_eq!(*ptr_v, 150);

        // Verify left_node: [0, 1, 2, 10]
        assert_eq!(left_node.key_count(), 4);
        assert_eq!((*left_node.key_ptr(0)).assume_init_read(), 0);
        assert_eq!((*left_node.key_ptr(1)).assume_init_read(), 1);
        assert_eq!((*left_node.key_ptr(2)).assume_init_read(), 2);
        assert_eq!((*left_node.key_ptr(3)).assume_init_read(), 10);

        // Verify right_node: [15, 20, 30, 40]
        assert_eq!(right_node.key_count(), 4);
        assert_eq!((*right_node.key_ptr(0)).assume_init_read(), 15);
        assert_eq!((*right_node.key_ptr(1)).assume_init_read(), 20);
        assert_eq!((*right_node.key_ptr(2)).assume_init_read(), 30);
        assert_eq!((*right_node.key_ptr(3)).assume_init_read(), 40);

        left_node.dealloc::<true>();
        right_node.dealloc::<true>();
    }
}

/// Test insert_borrow_left - insert at last index
/// Setup: left_node has [0], right_node (self) has [10, 20, 30]
/// Operation: insert_borrow_left with idx=2, key=25, value=250
/// Expected: left_node becomes [0, 10], right_node becomes [20, 25, 30]
#[test]
fn test_insert_borrow_left_at_last_idx() {
    unsafe {
        let mut left_node = LeafNode::<i32, i32>::alloc();
        let mut right_node = LeafNode::<i32, i32>::alloc();

        // Setup left_node with [0]
        left_node.insert_no_split(0, 0);

        // Setup right_node with [10, 20, 30]
        for i in 1..4 {
            right_node.insert_no_split(i * 10, i * 100);
        }

        // Verify search returns correct idx for key=25
        let (idx, found) = right_node.search(&25);
        assert!(!found);
        assert_eq!(idx, 2, "key=25 should be inserted at idx=2");

        // Insert at idx=2 (last valid index), key=25, value=250
        let ptr_v = right_node.insert_borrow_left(&mut left_node, 2, 25, 250);
        assert_eq!(*ptr_v, 250);

        // Verify left_node: [0, 10]
        assert_eq!(left_node.key_count(), 2);
        assert_eq!((*left_node.key_ptr(0)).assume_init_read(), 0);
        assert_eq!((*left_node.key_ptr(1)).assume_init_read(), 10);

        // Verify right_node: [20, 25, 30]
        assert_eq!(right_node.key_count(), 3);
        assert_eq!((*right_node.key_ptr(0)).assume_init_read(), 20);
        assert_eq!((*right_node.key_ptr(1)).assume_init_read(), 25);
        assert_eq!((*right_node.key_ptr(2)).assume_init_read(), 30);

        left_node.dealloc::<true>();
        right_node.dealloc::<true>();
    }
}

/// Test borrow_right - move last element from left to right
/// Setup: left_node has [10, 20, 30], right_node has [40, 50]
/// Operation: left_node.borrow_right(&mut right_node)
/// Expected: left_node becomes [10, 20], right_node becomes [30, 40, 50]
#[test]
fn test_borrow_right_basic() {
    unsafe {
        let mut left_node = LeafNode::<i32, i32>::alloc();
        let mut right_node = LeafNode::<i32, i32>::alloc();

        // Setup left_node with [10, 20, 30]
        for i in 1..4 {
            left_node.insert_no_split(i * 10, i * 100);
        }

        // Setup right_node with [40, 50]
        right_node.insert_no_split(40, 400);
        right_node.insert_no_split(50, 500);

        // Borrow from left to right
        left_node.borrow_right(&mut right_node);

        // Verify left_node: [10, 20]
        assert_eq!(left_node.key_count(), 2);
        assert_eq!((*left_node.key_ptr(0)).assume_init_read(), 10);
        assert_eq!((*left_node.key_ptr(1)).assume_init_read(), 20);

        // Verify right_node: [30, 40, 50]
        assert_eq!(right_node.key_count(), 3);
        assert_eq!((*right_node.key_ptr(0)).assume_init_read(), 30);
        assert_eq!((*right_node.key_ptr(1)).assume_init_read(), 40);
        assert_eq!((*right_node.key_ptr(2)).assume_init_read(), 50);

        left_node.dealloc::<true>();
        right_node.dealloc::<true>();
    }
}

/// Test borrow_right - when left_node has only one element
/// Setup: left_node has [10], right_node has [20, 30]
/// Operation: left_node.borrow_right(&mut right_node)
/// Expected: left_node becomes empty, right_node becomes [10, 20, 30]
#[test]
fn test_borrow_right_single_element() {
    unsafe {
        let mut left_node = LeafNode::<i32, i32>::alloc();
        let mut right_node = LeafNode::<i32, i32>::alloc();

        // Setup left_node with [10]
        left_node.insert_no_split(10, 100);

        // Setup right_node with [20, 30]
        right_node.insert_no_split(20, 200);
        right_node.insert_no_split(30, 300);

        // Borrow from left to right
        left_node.borrow_right(&mut right_node);

        // Verify left_node: empty
        assert_eq!(left_node.key_count(), 0);

        // Verify right_node: [10, 20, 30]
        assert_eq!(right_node.key_count(), 3);
        assert_eq!((*right_node.key_ptr(0)).assume_init_read(), 10);
        assert_eq!((*right_node.key_ptr(1)).assume_init_read(), 20);
        assert_eq!((*right_node.key_ptr(2)).assume_init_read(), 30);

        left_node.dealloc::<true>();
        right_node.dealloc::<true>();
    }
}
