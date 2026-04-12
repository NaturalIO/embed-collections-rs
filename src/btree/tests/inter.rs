use super::super::{inter::*, node::*};
use super::{CounterI32, alive_count, reset_alive_count};
use core::mem::align_of;

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

        let (new_node, promote_key) = node.insert_split(insert_key, insert_child);

        println!(
            "After split: left count = {}, right count = {}, promote_key = {}",
            node.key_count(),
            new_node.key_count(),
            promote_key,
        );
        println!("left ptr = {:?}, right ptr = {:?}", node.get_ptr(), new_node.get_ptr());

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
