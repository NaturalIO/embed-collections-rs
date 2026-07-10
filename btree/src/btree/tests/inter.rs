use super::super::{inter::*, node::*};
use super::*;
use core::mem::align_of;
use rstest::rstest;
use std::println;

#[test]
fn test_inter_align() {
    let cap = InterNode::<u8, usize>::cap();
    println!("align u8 {}, cap {}", align_of::<u8>(), cap);
    let mut inter = unsafe { InterNode::<u8, usize>::alloc(1) };
    inter.set_left_ptr(0 as *mut NodeHeader);
    for i in 1..(cap + 1) {
        inter.insert_no_split(i as u8, i as *mut NodeHeader);
    }
    for i in 1..(cap + 1) {
        let idx = inter.search_child(&(i as u8));
        assert_eq!(idx, i as u32);
    }
    inter.dealloc::<true>();
}

#[rstest]
#[case::empty_node(0)]
#[case::node_1_key(1)]
#[case::node_3_keys(3)]
#[case::node_5_keys(5)]
fn test_inter_search_child_smart(#[case] key_count: u32) {
    let is_seqs = [false, true];
    unsafe {
        let mut node = InterNode::<i32, i32>::alloc(1);
        node.set_left_ptr(0x1000 as *mut NodeHeader);

        // Insert odd keys: 1, 3, 5... (if key_count=3 -> keys are 1, 3, 5)
        for i in 1..=key_count {
            let key = (i * 2 - 1) as i32;
            node.insert_no_split(key, (0x1000 + i * 0x100) as *mut NodeHeader);
        }

        let upper_bound = if key_count == 0 { 2 } else { (key_count * 2) as i32 + 1 };

        for initial_is_seq in is_seqs {
            for search_key in 0..=upper_bound {
                let expected_idx = node.search_child(&search_key);
                let programmatic_idx = ((search_key + 1) / 2).min(key_count as i32) as u32;
                assert_eq!(
                    expected_idx, programmatic_idx,
                    "search_child idx ({}) does not match mathematical expectation ({}) for key_count={} search_key={}",
                    expected_idx, programmatic_idx, key_count, search_key
                );

                let mut is_seq = initial_is_seq;
                let smart_idx = node.search_child_smart(&search_key, &mut is_seq);
                assert_eq!(
                    smart_idx, programmatic_idx,
                    "search_child_smart index ({}) != programmatic expectation ({}) for key={}, initial_is_seq={}",
                    smart_idx, programmatic_idx, search_key, initial_is_seq
                );
            }
        }
        node.dealloc::<true>();
    }
}

#[test]
fn test_inter_insert_and_search() {
    unsafe {
        let mut inter = InterNode::<usize, usize>::alloc(1);
        let cap = InterNode::<usize, usize>::cap();
        println!("InterNode<usize> cap {}", cap);

        inter.set_left_ptr(0 as *mut NodeHeader);
        for i in 1..(cap + 1) {
            inter.insert_no_split(i as usize, i as *mut NodeHeader);
        }
        assert_eq!(*inter.child_ptr(0), 0 as *mut NodeHeader);

        assert_eq!(inter.key_count(), cap);
        // Test search - existing key
        for i in 1..(cap + 1) {
            let idx = inter.search_child(&(i as usize));
            assert_eq!(idx, i as u32);
            assert_eq!(*inter.child_ptr(i), i as *mut NodeHeader);
        }
        // search left ptr
        let idx = inter.search_child(&0);
        assert_eq!(idx, 0);

        // Test search - key larger than all
        let idx = inter.search_child(&50);
        assert_eq!(idx, cap as u32);

        inter.dealloc::<true>();
    }
}

#[test]
fn test_inter_split_insert_left() {
    reset_alive_count();
    let cap = InterNode::<CounterI32, CounterI32>::cap();
    println!("InterNode<CounterI32> cap {}", cap);
    // TODO should test split_idx == count ?  cap = 2
    unsafe {
        // Test Case 2: Insert key before split_idx (should go to left node)
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        // Fill the node to capacity with dummy pointers
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..cap {
            //println!("idx={i} {}", i*10);
            node.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        assert_eq!(*node.child_ptr(0), 0x1000 as *mut NodeHeader);
        for i in 0..cap {
            let idx = node.search_child(&((i * 10) as i32));
            assert_eq!(*node.child_ptr(idx), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }

        let split_idx = cap >> 1;
        let insert_key: CounterI32 = ((split_idx * 10 - 15) as i32).into(); // Key before split_idx
        let insert_key_value = insert_key.value;
        let insert_child = 0x5000 as *mut NodeHeader;
        let insert_idx = node.search_key(&insert_key);
        assert!(insert_idx < split_idx);
        println!("cap {cap} split_idx {split_idx}, insert_idx {insert_idx}");
        let (new_node, _promote_key) = node.insert_split(insert_key, insert_child);

        // Verify counts
        let left_count = node.key_count();
        let right_count = new_node.key_count();
        println!("left {left_count} right {right_count}");
        // although the keys will promote, the values are the same

        assert_eq!(left_count, split_idx + 1, "Left node should have split_idx keys");
        assert_eq!(left_count, insert_idx + 2, "Left node should have split_idx keys");
        assert_eq!(right_count, cap - split_idx - 1, "Right node should have cap - split_idx keys");
        assert_eq!(left_count + right_count, cap); // one more node, one more left ptr,

        assert_eq!(*node.child_ptr(0), 0x1000 as *mut NodeHeader);
        // total value is unchanged
        for i in 0..insert_idx {
            println!("check idx {i}={}", i * 10);
            let idx = node.search_child(&((i * 10) as i32));
            assert_eq!(idx, i + 1);
            assert_eq!((*node.key_ptr(i)).assume_init_ref(), (i * 10) as i32);
            assert_eq!(*node.child_ptr(i + 1), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }
        let idx = node.search_child(&insert_key_value);
        println!("insert_idx {insert_idx} ={}", (*node.key_ptr(insert_idx)).assume_init_ref());
        assert_eq!(idx, insert_idx + 1);
        assert_eq!(*node.child_ptr(idx), insert_child);
        // the last one in the left
        assert_eq!((*node.key_ptr(insert_idx + 1)).assume_init_ref(), ((insert_idx) * 10) as i32);
        assert_eq!(
            *node.child_ptr(insert_idx + 2),
            (0x1000 + (insert_idx + 1) * 0x100) as *mut NodeHeader
        );

        // the split_idx key is promoted and (split_idx+1) child is left child in new_node
        assert_eq!(*new_node.child_ptr(0), (0x1000 + (split_idx + 1) * 0x100) as *mut NodeHeader);
        for i in 0..cap - split_idx - 1 {
            assert_eq!((*new_node.key_ptr(i)).assume_init_ref(), ((split_idx + 1 + i) * 10) as i32);
            assert_eq!(
                *new_node.child_ptr(i + 1),
                (0x1000 + (split_idx + i + 2) * 0x100) as *mut NodeHeader
            );
        }
        new_node.dealloc::<true>();
        node.dealloc::<true>();
        println!("Test Case 2 completed successfully");
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_inter_split_insert_at_promote() {
    reset_alive_count();
    // Insert key at split_idx position (will be promoted, not inserted)
    unsafe {
        let cap = InterNode::<CounterI32, CounterI32>::cap();

        println!("=== Test Internal Node Split Basic ===");
        println!("cap = {}", cap);

        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        // Fill the node to capacity with dummy pointers
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..cap {
            node.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }

        let split_idx = cap >> 1;
        let insert_key: CounterI32 = ((split_idx * 10 - 5) as i32).into(); // Key between split_idx-1 and split_idx
        let insert_key_value = insert_key.value;
        let insert_child = 0x5000 as *mut NodeHeader;
        let insert_idx = node.search_key(&insert_key);
        assert!(insert_idx == split_idx);

        println!(
            "split_idx = {}, insert_key = {}, insert_child = {:?}",
            split_idx, insert_key_value, insert_child
        );

        let (mut new_node, promote_key) = node.insert_split(insert_key, insert_child);

        println!(
            "After split: left count = {}, right count = {}, promote_key = {}",
            node.key_count(),
            new_node.key_count(),
            promote_key,
        );
        println!("left ptr = {:?}, right ptr = {:?}", node.get_ptr_mut(), new_node.get_ptr_mut());

        // Verify counts
        let left_count = node.key_count() as u32;
        let right_count = new_node.key_count() as u32;

        println!("Asserting: left_count({}) == split_idx({})", left_count, split_idx);
        assert_eq!(left_count, split_idx, "Left node should have split_idx keys");
        assert_eq!(right_count, cap - split_idx, "Right node should have cap - split_idx keys");
        assert_eq!(
            left_count + right_count,
            cap,
            "Total keys should be cap when insert_key == promote_key"
        );
        assert_eq!(promote_key, insert_key_value, "Promoted key should be the inserted key");

        for i in 0..split_idx {
            assert_eq!((*node.key_ptr(i)).assume_init_ref(), ((i) * 10) as i32);
            assert_eq!(*node.child_ptr(i + 1), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }
        assert_eq!(*new_node.child_ptr(0), insert_child);

        for i in 0..cap - split_idx {
            assert_eq!((*new_node.key_ptr(i)).assume_init_ref(), ((split_idx + i) * 10) as i32);
            assert_eq!(
                *new_node.child_ptr(i + 1),
                (0x1000 + (split_idx + i + 1) * 0x100) as *mut NodeHeader
            );
        }
        new_node.dealloc::<true>();
        node.dealloc::<true>();
        println!("Test Case 1 completed successfully");
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_inter_split_insert_right_begin() {
    reset_alive_count();
    let cap = InterNode::<CounterI32, CounterI32>::cap() as u32;
    // Test Case 3: Insert key after split_idx (should go to right node)
    unsafe {
        println!("\n--- Test Case 3: Insert after split_idx (key goes to right node) ---");
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        // Fill the node to capacity with dummy pointers
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..cap {
            node.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        node.get_header_mut().count = cap;

        let split_idx = cap >> 1;
        let insert_key: CounterI32 = ((split_idx * 10 + 5) as i32).into(); // Key after split_idx
        let insert_key_value = insert_key.value;
        let insert_child = 0x5000 as *mut NodeHeader;
        let insert_idx = node.search_key(&insert_key);
        assert_eq!(insert_idx, split_idx + 1);
        println!("cap {cap} split_idx {split_idx} insert_idx {insert_idx}");

        let (new_node, promote_key) = node.insert_split(insert_key, insert_child);
        assert_eq!(promote_key, (split_idx * 10) as i32);

        // Verify counts
        let left_count = node.key_count() as u32;
        let right_count = new_node.key_count() as u32;

        assert_eq!(left_count, split_idx, "Left node should have split_idx keys");
        assert_eq!(right_count, cap - split_idx, "Right node should have cap - split_idx keys");
        assert_eq!(
            left_count + right_count,
            cap,
            "Total keys should be cap when insert_key != promote_key"
        );

        for i in 0..split_idx {
            assert_eq!((*node.key_ptr(i)).assume_init_ref(), ((i) * 10) as i32);
            assert_eq!(*node.child_ptr(i + 1), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }
        assert_eq!(*new_node.child_ptr(0), (0x1000 + (split_idx + 1) * 0x100) as *mut NodeHeader);

        assert_eq!((*new_node.key_ptr(0)).assume_init_ref(), insert_key_value);
        assert_eq!((*new_node.child_ptr(1)), insert_child);

        for i in 1..cap - split_idx {
            assert_eq!((*new_node.key_ptr(i)).assume_init_ref(), ((split_idx + i) * 10) as i32);
            assert_eq!(
                *new_node.child_ptr(i + 1),
                (0x1000 + (split_idx + i + 1) * 0x100) as *mut NodeHeader
            );
        }
        new_node.dealloc::<true>();
        node.dealloc::<true>();
        println!("Test Case 3 completed successfully");
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_inter_split_insert_right_mid() {
    reset_alive_count();
    let cap = InterNode::<CounterI32, CounterI32>::cap() as u32;
    // Test Case 3: Insert key after split_idx (should go to right node)
    unsafe {
        println!("\n--- Test Case 3: Insert after split_idx (key goes to right node) ---");
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        // Fill the node to capacity with dummy pointers
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..cap {
            node.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        node.get_header_mut().count = cap;

        let split_idx = cap >> 1;
        let insert_key: CounterI32 = ((split_idx * 11 + 5) as i32).into(); // Key after split_idx + 1
        let insert_key_value = insert_key.value;
        let insert_child = 0x5000 as *mut NodeHeader;
        let insert_idx = node.search_key(&insert_key);
        assert_eq!(insert_idx, split_idx + 2);
        println!("cap {cap} split_idx {split_idx} insert_idx {insert_idx}");

        let (new_node, promote_key) = node.insert_split(insert_key, insert_child);
        assert_eq!(promote_key.value, (split_idx * 10) as i32);

        // Verify counts
        let left_count = node.key_count() as u32;
        let right_count = new_node.key_count() as u32;

        assert_eq!(left_count, split_idx, "Left node should have split_idx keys");
        assert_eq!(right_count, cap - split_idx, "Right node should have cap - split_idx keys");
        assert_eq!(
            left_count + right_count,
            cap,
            "Total keys should be cap when insert_key != promote_key"
        );

        for i in 0..split_idx {
            assert_eq!((*node.key_ptr(i)).assume_init_ref(), ((i) * 10) as i32);
            assert_eq!(*node.child_ptr(i + 1), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }
        assert_eq!(*new_node.child_ptr(0), (0x1000 + (split_idx + 1) * 0x100) as *mut NodeHeader);

        assert_eq!((*new_node.key_ptr(0)).assume_init_ref(), ((split_idx + 1) * 10) as i32);
        assert_eq!(
            *new_node.child_ptr(1),
            (0x1000 + (split_idx + 1 + 1) * 0x100) as *mut NodeHeader
        );
        assert_eq!((*new_node.key_ptr(1)).assume_init_ref(), insert_key_value);
        assert_eq!((*new_node.child_ptr(2)), insert_child);
        for i in 2..cap - split_idx {
            assert_eq!((*new_node.key_ptr(i)).assume_init_ref(), ((split_idx + i) * 10) as i32);
            assert_eq!(
                *new_node.child_ptr(i + 1),
                (0x1000 + (split_idx + i + 1) * 0x100) as *mut NodeHeader
            );
        }
        new_node.dealloc::<true>();
        node.dealloc::<true>();
        println!("Test Case 3 completed successfully");
    }
    assert_eq!(alive_count(), 0);
}

#[test]
fn test_inter_split_insert_at_end() {
    reset_alive_count();
    let cap = InterNode::<CounterI32, CounterI32>::cap() as u32;
    // Test Case 3: Insert key after split_idx (should go to right node)
    unsafe {
        println!("\n--- Test Case 3: Insert after split_idx (key goes to right node) ---");
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        // Fill the node to capacity with dummy pointers
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..cap {
            node.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        node.get_header_mut().count = cap;

        let insert_key: CounterI32 = (((cap + 1) as i32) * 10).into(); // Key after split_idx + 1
        let insert_key_value = insert_key.value;
        let insert_child = 0x5000 as *mut NodeHeader;
        let insert_idx = node.search_key(&insert_key);
        assert_eq!(insert_idx, cap);
        println!("cap {cap} insert_idx {insert_idx}");

        let (new_node, promote_key) = node.insert_split(insert_key, insert_child);
        assert_eq!(promote_key.value, insert_key_value);

        // Verify counts
        let left_count = node.key_count() as u32;
        let right_count = new_node.key_count() as u32;

        assert_eq!(left_count, cap, "Left node should have split_idx keys");
        assert_eq!(right_count, 0, "Right node should have cap - split_idx keys");

        for i in 0..cap {
            assert_eq!((*node.key_ptr(i)).assume_init_ref(), ((i) * 10) as i32);
            assert_eq!(*node.child_ptr(i + 1), (0x1000 + (i + 1) * 0x100) as *mut NodeHeader);
        }
        assert_eq!(*new_node.child_ptr(0), insert_child);
        new_node.dealloc::<true>();
        node.dealloc::<true>();
        println!("Test Case 3 completed successfully");
    }
    assert_eq!(alive_count(), 0);
}

/// Test: Merge two internal nodes with separator key from grandparent
///
/// Tree structure before:
///   grand(h=2) -> [left | sep_key | right]
///   left(h=1) -> [child_0 | key_1 | child_1 | ...]
///   right(h=1) -> [child_n | key_n+1 | child_n+1 | ...]
///
/// After merge(left, right, grand, right_idx=1):
///   grand(h=2) -> [merged]
///   merged(h=1) contains all keys from left + sep_key + all keys from right
///
/// Key test: Verifies merge operation correctly:
/// 1. Pulls separator key from grandparent
/// 2. Combines all keys and children from both nodes
/// 3. Properly manages CounterI32 memory (alive_count == 0 at end)
#[test]
fn test_inter_merge_basic() {
    reset_alive_count();
    unsafe {
        let cap = InterNode::<CounterI32, CounterI32>::cap();
        println!("InterNode<CounterI32> cap {}", cap);

        // Create left node with some keys
        let mut left = InterNode::<CounterI32, CounterI32>::alloc(1);
        left.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..3 {
            left.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        assert_eq!(left.key_count(), 3);

        // Create right node with some keys
        let mut right = InterNode::<CounterI32, CounterI32>::alloc(1);
        right.set_left_ptr(0x2000 as *mut NodeHeader);
        for i in 0..3 {
            right.insert_no_split(
                ((30 + i * 10) as i32).into(),
                (0x2000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        assert_eq!(right.key_count(), 3);

        // Create grandparent node with separator key
        let mut grand = InterNode::<CounterI32, CounterI32>::alloc(2);
        grand.set_left_ptr(left.get_ptr_mut());
        grand.insert_no_split(25_i32.into(), right.get_ptr_mut()); // separator key = 25
        assert_eq!(grand.key_count(), 1);

        // Record alive count before merge
        let alive_before = alive_count();
        println!("Alive count before merge: {}", alive_before);

        // Perform merge: left merges right, separator key (25) pulled from grand
        left.merge(right, &mut grand, 1);

        // Verify merge results
        assert_eq!(left.key_count(), 7, "Merged node should have 3 + 1 + 3 = 7 keys");
        assert_eq!(grand.key_count(), 0, "Grandparent should have 0 keys after removing separator");

        // Verify keys are in correct order: [0, 10, 20, 25, 30, 40, 50]
        let expected_keys = [0, 10, 20, 25, 30, 40, 50];
        for (i, &expected) in expected_keys.iter().enumerate() {
            let actual = (*left.key_ptr(i as u32)).assume_init_ref().value;
            assert_eq!(actual, expected, "Key at index {} should be {}", i, expected);
        }

        // Verify children pointers
        assert_eq!(
            *left.child_ptr(0),
            0x1000 as *mut NodeHeader,
            "First child should be left's left_ptr"
        );
        assert_eq!(
            *left.child_ptr(4),
            0x2000 as *mut NodeHeader,
            "Child at index 4 should be right's left_ptr"
        );

        // Verify alive count - all CounterI32 should still be alive
        let alive_after = alive_count();
        println!("Alive count after merge: {}", alive_after);
        assert_eq!(alive_after, alive_before, "No CounterI32 should be dropped during merge");

        // Clean up
        grand.dealloc::<false>(); // grand has no keys
        left.dealloc::<true>(); // left has all the keys

        println!("test_inter_merge_basic completed successfully");
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped after cleanup");
}

/// Test: Merge when right node has 0 keys (only left child)
///
/// This tests the edge case where right node has no keys,
/// only a leftmost child pointer.
#[test]
fn test_inter_merge_right_empty() {
    reset_alive_count();
    unsafe {
        // Create left node with keys
        let mut left = InterNode::<CounterI32, CounterI32>::alloc(1);
        left.set_left_ptr(0x1000 as *mut NodeHeader);
        for i in 0..3 {
            left.insert_no_split(
                ((i * 10) as i32).into(),
                (0x1000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        assert_eq!(left.key_count(), 3);

        // Create right node with NO keys (only left child)
        let mut right = InterNode::<CounterI32, CounterI32>::alloc(1);
        (*right.child_ptr_mut(0)) = 0x2000 as *mut NodeHeader;
        assert_eq!(right.key_count(), 0);

        // Create grandparent with separator key
        let mut grand = InterNode::<CounterI32, CounterI32>::alloc(2);
        grand.set_left_ptr(left.get_ptr_mut());
        grand.insert_no_split(25_i32.into(), right.get_ptr_mut());
        assert_eq!(grand.key_count(), 1);

        // Perform merge
        left.merge(right, &mut grand, 1);

        // Verify results
        assert_eq!(left.key_count(), 4, "Merged node should have 3 + 1 + 0 = 4 keys");

        // Verify keys: [0, 10, 20, 25]
        let expected_keys = [0, 10, 20, 25];
        for (i, &expected) in expected_keys.iter().enumerate() {
            let actual = (*left.key_ptr(i as u32)).assume_init_ref().value;
            assert_eq!(actual, expected, "Key at index {} should be {}", i, expected);
        }

        // Verify children: left has 5 children (original 4 + right's left child)
        assert_eq!(*left.child_ptr(0), 0x1000 as *mut NodeHeader);
        assert_eq!(*left.child_ptr(4), 0x2000 as *mut NodeHeader);

        // Clean up
        grand.dealloc::<false>();
        left.dealloc::<true>();
    }
    assert_eq!(alive_count(), 0);
}

/// Test: Merge when left node has 0 keys
///
/// This tests the edge case where left node has no keys before merge.
#[test]
fn test_inter_merge_left_empty() {
    reset_alive_count();
    unsafe {
        // Create left node with NO keys
        let mut left = InterNode::<CounterI32, CounterI32>::alloc(1);
        (*left.child_ptr_mut(0)) = 0x1000 as *mut NodeHeader;
        assert_eq!(left.key_count(), 0);

        // Create right node with keys
        let mut right = InterNode::<CounterI32, CounterI32>::alloc(1);
        right.set_left_ptr(0x2000 as *mut NodeHeader);
        for i in 0..3 {
            right.insert_no_split(
                ((30 + i * 10) as i32).into(),
                (0x2000 + (i + 1) * 0x100) as *mut NodeHeader,
            );
        }
        assert_eq!(right.key_count(), 3);

        // Create grandparent with separator key
        let mut grand = InterNode::<CounterI32, CounterI32>::alloc(2);
        grand.set_left_ptr(left.get_ptr_mut());
        grand.insert_no_split(25_i32.into(), right.get_ptr_mut());
        assert_eq!(grand.key_count(), 1);

        // Perform merge
        left.merge(right, &mut grand, 1);

        // Verify results
        assert_eq!(left.key_count(), 4, "Merged node should have 0 + 1 + 3 = 4 keys");

        // Verify keys: [25, 30, 40, 50]
        let expected_keys = [25, 30, 40, 50];
        for (i, &expected) in expected_keys.iter().enumerate() {
            let actual = (*left.key_ptr(i as u32)).assume_init_ref().value;
            assert_eq!(actual, expected, "Key at index {} should be {}", i, expected);
        }

        // Verify children: left has 5 children (original 1 + separator + right's 4)
        assert_eq!(*left.child_ptr(0), 0x1000 as *mut NodeHeader);
        assert_eq!(*left.child_ptr(1), 0x2000 as *mut NodeHeader);

        // Clean up
        grand.dealloc::<false>();
        left.dealloc::<true>();
    }
    assert_eq!(alive_count(), 0);
}

/// Test: InterNode insert_at_front
///
/// Verifies inserting key and child at the front of an internal node,
/// shifting existing content to the right.
#[test]
fn test_inter_insert_at_front() {
    reset_alive_count();
    unsafe {
        let cap = InterNode::<CounterI32, CounterI32>::cap() as usize;
        assert!(cap > 6);

        // Create an internal node with some keys
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        node.set_left_ptr(0x1000 as *mut NodeHeader);

        // Insert some keys
        for i in 0..5 {
            node.insert_no_split(
                CounterI32::new((i * 10) as i32),
                ((0x2000 + i * 0x100) as usize) as *mut NodeHeader,
            );
        }
        assert_eq!(node.key_count() as usize, 5);

        let original_first_key = node.get_keys()[0].value;
        let original_first_child = node.get_child_ptr(0);

        // Insert at front (child_ptr, key)
        node.insert_at_front(0x9999 as *mut NodeHeader, CounterI32::new(999));
        // Verify count increased
        assert_eq!(node.key_count() as usize, 6);
        // Verify new key is at front
        assert_eq!(node.get_keys()[0].value, 999);
        assert_eq!(node.get_child_ptr(0), 0x9999 as *mut NodeHeader);
        // Verify original content shifted right
        assert_eq!(node.get_keys()[1].value, original_first_key);
        assert_eq!(node.get_child_ptr(1), original_first_child);

        // Verify remaining keys are correct
        for i in 1..5 {
            assert_eq!(node.get_keys()[i + 1].value, (i * 10) as i32);
        }
        // Clean up
        node.dealloc::<true>();
    }
    assert_eq!(alive_count(), 0);
}

/// Test: InterNode insert_at_front on empty node
#[test]
fn test_inter_insert_at_front_empty() {
    reset_alive_count();
    unsafe {
        // Create an empty internal node
        let mut node = InterNode::<CounterI32, CounterI32>::alloc(1);
        node.set_left_ptr(0x1000 as *mut NodeHeader);
        assert_eq!(node.key_count(), 0);
        // Insert at front on empty node (child_ptr, key)
        node.insert_at_front(0x2000 as *mut NodeHeader, CounterI32::new(100));

        // Verify
        assert_eq!(node.key_count(), 1);
        assert_eq!(node.get_keys()[0].value, 100);
        assert_eq!(node.get_child_ptr(0), 0x2000 as *mut NodeHeader);
        // Original left_ptr should be shifted to child[1]
        assert_eq!(node.get_child_ptr(1), 0x1000 as *mut NodeHeader);
        // Clean up
        node.dealloc::<true>();
    }
    assert_eq!(alive_count(), 0);
}

/// Test insert_rotate_left - basic case
///
/// Setup:
///   parent (h=2) -> [left | 100 | right]
///   left (h=1) -> [0x1000 | 10 | 0x1001 | 20 | 0x1002]
///   right (h=1) -> [0x2000 | 110 | 0x2001 | 120 | 0x2002 | 130 | 0x2003]
///
/// Insert key=115 (search returns idx=1, meaning between 110 and 120)
/// After rotate:
///   parent: key 100 -> 110
///   left: [10, 20, 100] with children [0x1000, 0x1001, 0x1002, 0x2000]
///   right: [115, 120, 130] with children [0x2001, 0x2001A, 0x2002, 0x2003]
#[test]
fn test_insert_rotate_left_basic() {
    unsafe {
        // Create left node with keys [10, 20]
        let mut left = InterNode::<i32, i32>::alloc(1);
        left.set_left_ptr(0x1000 as *mut NodeHeader);
        left.insert_no_split(10_i32, 0x1001 as *mut NodeHeader);
        left.insert_no_split(20_i32, 0x1002 as *mut NodeHeader);

        // Create right node with keys [110, 120, 130]
        let mut right = InterNode::<i32, i32>::alloc(1);
        right.set_left_ptr(0x2000 as *mut NodeHeader);
        right.insert_no_split(110_i32, 0x2001 as *mut NodeHeader);
        right.insert_no_split(120_i32, 0x2002 as *mut NodeHeader);
        right.insert_no_split(130_i32, 0x2003 as *mut NodeHeader);

        // Create parent node with separator key 100
        let mut parent = InterNode::<i32, i32>::alloc(2);
        parent.set_left_ptr(left.get_ptr_mut());
        parent.insert_no_split(100_i32, right.get_ptr_mut());

        // Search for key=115, should return idx=1
        let key: i32 = 115_i32;
        let insert_idx = right.search_key(&key);
        assert_eq!(insert_idx, 1, "key=115 should be inserted at idx=1");

        // Perform insert_rotate_left
        right.insert_rotate_left(
            &mut parent,
            1,
            &mut left,
            insert_idx,
            key,
            0x2001A as *mut NodeHeader,
        );

        // Verify parent: key 100 replaced with 110
        assert_eq!((*parent.key_ptr(0)).assume_init_read(), 110);

        // Verify left node: [10, 20, 100]
        assert_eq!(left.key_count(), 3);
        assert_eq!((*left.key_ptr(0)).assume_init_read(), 10);
        assert_eq!((*left.key_ptr(1)).assume_init_read(), 20);
        assert_eq!((*left.key_ptr(2)).assume_init_read(), 100);

        // Verify right node: [115, 120, 130]
        assert_eq!(right.key_count(), 3);
        assert_eq!((*right.key_ptr(0)).assume_init_read(), 115);
        assert_eq!((*right.key_ptr(1)).assume_init_read(), 120);
        assert_eq!((*right.key_ptr(2)).assume_init_read(), 130);

        parent.dealloc::<false>();
        left.dealloc::<true>();
        right.dealloc::<true>();
    }
}

/// Test insert_rotate_left - insert at middle position (idx=2)
///
/// Setup:
///   parent (h=2) -> [left | 200 | right]
///   left (h=1) -> [0x3000 | 30 | 0x3001]
///   right (h=1) -> [0x4000 | 210 | 0x4001 | 220 | 0x4002 | 230 | 0x4003]
///
/// Insert key=225 (search returns idx=2, meaning between 220 and 230)
#[test]
fn test_insert_rotate_left_middle() {
    unsafe {
        // Create left node with key [30]
        let mut left = InterNode::<i32, i32>::alloc(1);
        left.set_left_ptr(0x3000 as *mut NodeHeader);
        left.insert_no_split(30_i32, 0x3001 as *mut NodeHeader);

        // Create right node with keys [210, 220, 230]
        let mut right = InterNode::<i32, i32>::alloc(1);
        right.set_left_ptr(0x4000 as *mut NodeHeader);
        right.insert_no_split(210_i32, 0x4001 as *mut NodeHeader);
        right.insert_no_split(220_i32, 0x4002 as *mut NodeHeader);
        right.insert_no_split(230_i32, 0x4003 as *mut NodeHeader);

        // Create parent node with separator key 200
        let mut parent = InterNode::<i32, i32>::alloc(2);
        parent.set_left_ptr(left.get_ptr_mut());
        parent.insert_no_split(200_i32, right.get_ptr_mut());

        // Search for key=225, should return idx=2
        let key: i32 = 225_i32;
        let insert_idx = right.search_key(&key);
        assert_eq!(insert_idx, 2, "key=225 should be inserted at idx=2");

        // Perform insert_rotate_left
        right.insert_rotate_left(
            &mut parent,
            1,
            &mut left,
            insert_idx,
            key,
            0x4002A as *mut NodeHeader,
        );

        // Verify parent: key 200 replaced with 210
        assert_eq!((*parent.key_ptr(0)).assume_init_read(), 210);

        // Verify left node: [30, 200]
        assert_eq!(left.key_count(), 2);
        assert_eq!((*left.key_ptr(0)).assume_init_read(), 30);
        assert_eq!((*left.key_ptr(1)).assume_init_read(), 200);

        // Verify right node: [220, 225, 230]
        assert_eq!(right.key_count(), 3);
        assert_eq!((*right.key_ptr(0)).assume_init_read(), 220);
        assert_eq!((*right.key_ptr(1)).assume_init_read(), 225);
        assert_eq!((*right.key_ptr(2)).assume_init_read(), 230);

        parent.dealloc::<false>();
        left.dealloc::<true>();
        right.dealloc::<true>();
    }
}

/// Test insert_rotate_left - insert at last position (idx=key_count)
///
/// Setup:
///   parent (h=2) -> [left | 300 | right]
///   left (h=1) -> [0x5000 | 40 | 0x5001]
///   right (h=1) -> [0x6000 | 310 | 0x6001 | 320 | 0x6002]
///
/// Insert key=330 (search returns idx=2, meaning after 320)
#[test]
fn test_insert_rotate_left_last() {
    unsafe {
        // Create left node with key [40]
        let mut left = InterNode::<i32, i32>::alloc(1);
        left.set_left_ptr(0x5000 as *mut NodeHeader);
        left.insert_no_split(40_i32, 0x5001 as *mut NodeHeader);

        // Create right node with keys [310, 320]
        let mut right = InterNode::<i32, i32>::alloc(1);
        right.set_left_ptr(0x6000 as *mut NodeHeader);
        right.insert_no_split(310_i32, 0x6001 as *mut NodeHeader);
        right.insert_no_split(320_i32, 0x6002 as *mut NodeHeader);

        // Create parent node with separator key 300
        let mut parent = InterNode::<i32, i32>::alloc(2);
        parent.set_left_ptr(left.get_ptr_mut());
        parent.insert_no_split(300_i32, right.get_ptr_mut());

        // Search for key=330, should return idx=2 (key_count)
        let key: i32 = 330_i32;
        let insert_idx = right.search_key(&key);
        assert_eq!(insert_idx, 2, "key=330 should be inserted at idx=2 (key_count)");

        // Perform insert_rotate_left
        right.insert_rotate_left(
            &mut parent,
            1,
            &mut left,
            insert_idx,
            key,
            0x6003 as *mut NodeHeader,
        );

        // Verify parent: key 300 replaced with 310
        assert_eq!((*parent.key_ptr(0)).assume_init_read(), 310);

        // Verify left node: [40, 300]
        assert_eq!(left.key_count(), 2);
        assert_eq!((*left.key_ptr(0)).assume_init_read(), 40);
        assert_eq!((*left.key_ptr(1)).assume_init_read(), 300);

        // Verify right node: [320, 330]
        assert_eq!(right.key_count(), 2);
        assert_eq!((*right.key_ptr(0)).assume_init_read(), 320);
        assert_eq!((*right.key_ptr(1)).assume_init_read(), 330);

        parent.dealloc::<false>();
        left.dealloc::<true>();
        right.dealloc::<true>();
    }
}
