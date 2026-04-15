use super::super::*;
use crate::test::{CounterI32, alive_count, reset_alive_count, setup_log};
use captains_log::logfn;
use rstest::rstest;

/// sequenctial delete all elements
///
/// Note: Since we don't implement borrowing data from brothers, it's possible to produce single child
/// tree structure
#[logfn]
#[rstest]
#[case(100, 2)]
#[case(1000, 3)]
#[case(10000, 4)]
fn test_delete_all_seq(setup_log: (), #[case] count: u32, #[case] height: u32) {
    #[cfg(miri)]
    {
        if count > 100 {
            println!("skip big test for miri");
            return;
        }
    }
    // Reset counter at test start
    reset_alive_count();
    assert_eq!(alive_count(), 0);

    let mut map: BTreeMap<CounterI32, CounterI32> = BTreeMap::new();
    // Fill node to capacity
    for i in 0..count {
        map.insert((i as i32).into(), (i as i32 * 10).into());
        map.validate();
    }
    println!("leaf_count: {}", map.leaf_count());
    println!("fill_ratio: {:.2}", map.get_fill_ratio());
    println!("height: {}", map.height());
    assert_eq!(height, map.height());

    let alive_after_insert = alive_count();
    println!("alive_after_insert: {}", alive_after_insert);
    map.print_trigger_flags();

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
    map.print_trigger_flags();

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
///
/// Environment variable:
/// - `TEST_SEED`: Set a specific seed for reproducibility. If not set, a random seed is generated.
#[logfn]
#[cfg(not(miri))]
#[rstest]
#[case(100, 10)] // Small batch, more iterations
#[case(1000, 10)] // Standard test: 1000 elements per batch, 10 iterations
#[case(500, 5)] // Medium batch, fewer iterations
#[case(10000, 3)] // Standard test: 1000 elements per batch, 10 iterations
fn test_mixed_random_batch_insert_delete(
    setup_log: (), #[case] batch_size: usize, #[case] iterations: usize,
) {
    reset_alive_count();
    assert_eq!(alive_count(), 0);

    // Get seed from environment variable or generate a random one
    let seed: u64 = match std::env::var("TEST_SEED") {
        Ok(val) => val.parse().expect("TEST_SEED must be a valid u64"),
        Err(_) => fastrand::u64(..),
    };

    println!(
        "=== Test Parameters === seed: {}, batch_size: {}, iterations: {} ===",
        seed, batch_size, iterations
    );

    let mut map: BTreeMap<CounterI32, CounterI32> = BTreeMap::new();
    let mut rng = fastrand::Rng::with_seed(seed);

    // Helper to compute value from key (use wrapping to avoid overflow)
    let value_from_key = |k: i32| k.wrapping_mul(10);

    // Generate first batch
    let mut prev_batch: Vec<i32> = Vec::with_capacity(batch_size);
    while prev_batch.len() < batch_size {
        let key: i32 = rng.i32(..);
        crate::trace_log!("check contain {key:?}");
        if map.contains_key(&key) {
            // filter duplicated keys
            continue;
        }
        prev_batch.push(key);
        crate::trace_log!("insert {key:?} {}th", map.len());
        map.insert(key.into(), value_from_key(key).into());
    }
    println!("---");
    println!("len: {}", map.len());
    println!("leaf_count: {}", map.leaf_count());
    println!("fill_ratio: {:.2}", map.get_fill_ratio());
    println!("height: {}", map.height());
    map.validate();
    println!("After first batch: height={}, len={}", map.height(), map.len());

    // For subsequent iterations: insert new batch, then delete previous batch
    for iter in 1..iterations {
        // Insert new batch
        let mut current_batch: Vec<i32> = Vec::with_capacity(batch_size);
        while current_batch.len() < batch_size {
            let key: i32 = rng.i32(..);
            crate::trace_log!("check contain {key:?}");
            if map.contains_key(&key) {
                // filter duplicated keys
                continue;
            }
            current_batch.push(key);
            crate::trace_log!("insert {key:?}");
            map.insert(key.into(), value_from_key(key).into());
        }
        map.validate();
        println!("---iteration {iter}: insert ---");
        println!("len: {}", map.len());
        println!("leaf_count: {}", map.leaf_count());
        println!("fill_ratio: {:.2}", map.get_fill_ratio());
        println!("height: {}", map.height());

        // Delete previous batch
        for (_i, key) in prev_batch.iter().enumerate() {
            crate::trace_log!("remove {key} {_i}th");
            let v = map.remove(key);
            map.validate();
            assert!(v.is_some(), "Key {} from prev_batch should exist", key);
            if let Some(val) = v {
                assert_eq!(*val, value_from_key(*key));
            }
        }
        map.validate();
        println!("---iteration {iter}: removed ---");
        println!("len: {}", map.len());
        println!("leaf_count: {}", map.leaf_count());
        println!("fill_ratio: {:.2}", map.get_fill_ratio());
        println!("height: {}", map.height());
        map.print_trigger_flags();

        prev_batch = current_batch;
    }

    let mut height = map.height();

    // Verify all remaining elements are accessible
    for key in &prev_batch {
        if !map.contains_key(key) {
            map.dump();
            map.validate();
            panic!("error: Remaining key {} should be accessible", key);
        }
    }

    // Delete remaining elements
    for key in &prev_batch {
        let v = map.remove(key);
        assert!(v.is_some(), "Remaining key {} should be removable", key);
        assert_eq!(*v.unwrap(), value_from_key(*key));
        if height != map.height() {
            height = map.height();
            map.print_trigger_flags();
            println!("tree height dec to {}, len {}", height, map.len());
        }
    }
    map.validate();

    assert_eq!(map.len(), 0, "Map should be empty after deleting all elements");
    assert_eq!(map.height(), 1, "Height should be 1 for empty tree");
    assert_eq!(map.leaf_count(), 1);

    drop(map);
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}
