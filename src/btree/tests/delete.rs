use super::super::*;
use super::{CounterI32, alive_count, reset_alive_count};
use rstest::rstest;

/// sequenctial delete all elements
///
/// Note: Since we don't implement borrowing data from brothers, it's possible to produce single child
/// tree structure
#[rstest]
#[case(100, 2)]
#[case(1000, 3)]
#[case(10000, 4)]
fn test_delete_all_seq(#[case] count: u32, #[case] height: u32) {
    // Reset counter at test start
    reset_alive_count();
    assert_eq!(alive_count(), 0);

    let mut map: BTreeMap<CounterI32, CounterI32> = BTreeMap::new();
    // Fill node to capacity
    for i in 0..count {
        map.insert((i as i32).into(), (i as i32 * 10).into());
        map.validate();
    }
    println!("height: {}", map.height());
    assert_eq!(height, map.height());

    let alive_after_insert = alive_count();
    println!("alive_after_insert: {}", alive_after_insert);

    // Delete most elements to trigger merge, use Borrow<i32> to query
    for i in 0..count {
        let v = map.remove(&(i as i32));
        assert!(v.is_some(), "failed to remove {}", i);
        assert_eq!(*v.unwrap(), i as i32 * 10); // Deref to i32
        map.validate();
    }
    assert_eq!(map.height(), 1);

    let alive_after_remove = alive_count();
    println!("alive_after_remove: {}", alive_after_remove);
    assert_eq!(alive_after_remove, 0); // All dropped

    drop(map);
    assert_eq!(alive_count(), 0);
}

/// Mixed random insert and delete test
///
/// Test workflow:
/// 1. Insert first batch of random elements (batch_size), store in prev_batch Vec
/// 2. For each subsequent iteration:
///    - Insert new batch of random elements (batch_size), store in current_batch Vec
///    - Delete all elements from prev_batch
///    - Move current_batch to prev_batch
/// 3. After all iterations, delete remaining elements
/// 4. Verify all CounterI32 are properly dropped
///
/// This test verifies that the BTreeMap correctly handles mixed operations
/// and properly manages memory during tree restructuring.
#[rstest]
#[case(100, 10)] // Small batch, more iterations
#[case(1000, 10)] // Standard test: 1000 elements per batch, 10 iterations
#[case(500, 5)] // Medium batch, fewer iterations
fn test_mixed_random_batch_insert_delete(#[case] batch_size: usize, #[case] iterations: usize) {
    reset_alive_count();
    assert_eq!(alive_count(), 0);

    let mut map: BTreeMap<CounterI32, CounterI32> = BTreeMap::new();
    let mut rng = fastrand::Rng::new();

    // Helper to compute value from key (use wrapping to avoid overflow)
    let value_from_key = |k: i32| k.wrapping_mul(10);

    // Generate first batch
    let mut prev_batch: Vec<i32> = Vec::with_capacity(batch_size);
    for _ in 0..batch_size {
        let key: i32 = rng.i32(..);
        prev_batch.push(key);
        map.insert(key.into(), value_from_key(key).into());
    }
    map.validate();
    println!("After first batch: height={}, len={}", map.height(), map.len());

    // For subsequent iterations: insert new batch, then delete previous batch
    for iter in 1..iterations {
        // Insert new batch
        let mut current_batch: Vec<i32> = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let key: i32 = rng.i32(..);
            current_batch.push(key);
            map.insert(key.into(), value_from_key(key).into());
        }
        map.validate();
        println!("After iteration {} insert: height={}, len={}", iter, map.height(), map.len());

        // Delete previous batch
        for key in &prev_batch {
            let v = map.remove(key);
            assert!(
                v.is_some() || current_batch.contains(key),
                "Key {} from prev_batch should exist (unless duplicated in current)",
                key
            );
            if let Some(val) = v {
                assert_eq!(*val, value_from_key(*key));
            }
        }
        map.validate();
        println!("After iteration {} delete: height={}, len={}", iter, map.height(), map.len());

        prev_batch = current_batch;
    }

    // Verify all remaining elements are accessible
    for key in &prev_batch {
        assert!(map.contains_key(key), "Remaining key {} should be accessible", key);
    }

    // Delete remaining elements
    for key in &prev_batch {
        let v = map.remove(key);
        assert!(v.is_some(), "Remaining key {} should be removable", key);
        assert_eq!(*v.unwrap(), value_from_key(*key));
    }
    map.validate();

    assert_eq!(map.len(), 0, "Map should be empty after deleting all elements");
    assert_eq!(map.height(), 1, "Height should be 1 for empty tree");

    drop(map);
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}
