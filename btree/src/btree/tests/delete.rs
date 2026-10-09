use super::super::*;
use super::*;
use captains_log::{log_println, logfn};
use rstest::rstest;
use std::fmt::Debug;
use std::println;
use std::vec::Vec;

fn _test_delete_all_seq<S: Stats<CounterI32>, F>(
    mut map: BTree<CounterI32, CounterI32, S>, count: u32, height: u8, print_f: F,
) where
    F: Fn(&BTree<CounterI32, CounterI32, S>),
{
    // Reset counter at test start
    reset_alive_count();
    assert_eq!(alive_count(), 0);

    // Fill node to capacity
    for i in 0..count {
        map.insert((i as i32).into(), (i as i32 * 10).into());
        map.validate();
    }
    print_f(&map);
    assert_eq!(height, map.height());

    let alive_after_insert = alive_count();
    println!("alive_after_insert: {}", alive_after_insert);
    #[cfg(feature = "trace_log")]
    map.inner.print_trigger_flags();

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
    #[cfg(feature = "trace_log")]
    map.inner.print_trigger_flags();

    drop(map);
    assert_eq!(alive_count(), 0);
}

/// sequenctial delete all elements
///
/// note: since we don't implement borrowing data from brothers, it's possible to produce single child
/// tree structure
#[logfn]
#[rstest]
#[case(100, 2)]
#[case(1000, 3)]
#[case(10000, 3)]
fn test_large_delete_all_seq(setup_log: (), #[case] count: u32, #[case] height: u8) {
    #[cfg(miri)]
    {
        if count > 100 {
            println!("skip big test for miri");
            return;
        }
    }
    let map = crate::large::BTreeMap::<CounterI32, CounterI32>::new();
    _test_delete_all_seq(map, count, height, |_map| {
        println!("leaf_count: {}", _map.leaf_count());
        println!("fill_ratio: {:.2}", _map.get_fill_ratio());
        println!("height: {}", _map.height());
    });
}

/// sequenctial delete all elements
///
/// note: since we don't implement borrowing data from brothers, it's possible to produce single child
/// tree structure
#[logfn]
#[rstest]
#[case(100, 2)]
#[case(1000, 3)]
#[case(10000, 3)]
fn test_compact_delete_all_seq(setup_log: (), #[case] count: u32, #[case] height: u8) {
    #[cfg(miri)]
    {
        if count > 100 {
            println!("skip big test for miri");
            return;
        }
    }
    let map = crate::compact::BTreeMap::<CounterI32, CounterI32>::new();
    _test_delete_all_seq(map, count, height, |_map| {
        println!("height: {}", _map.height());
    });
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
#[case(100, 10, true)]
#[case(100, 10, false)]
#[case(500, 5, true)]
#[case(500, 5, false)]
#[case(1000, 10, true)]
#[case(1000, 10, false)]
#[case(10000, 3, true)]
#[case(10000, 3, false)]
fn test_large_mixed_random_batch_insert_delete(
    setup_log: (), #[case] batch_size: usize, #[case] iterations: usize, #[case] use_entry: bool,
) {
    reset_alive_count();
    assert_eq!(alive_count(), 0);
    let gen_data = |_rng: &mut fastrand::Rng| {
        let k = _rng.i32(..);
        let v = k.wrapping_mul(10);
        (CounterI32::from(k), CounterI32::from(v))
    };
    {
        println!("test large");
        let mut map = crate::large::BTreeMap::<CounterI32, CounterI32>::new();
        _test_large_mixed_random_batch_insert_delete(
            batch_size,
            iterations,
            &mut map,
            |_map: &crate::large::BTreeMap<CounterI32, CounterI32>| {
                println!("len: {}", _map.len());
                println!("leaf_count: {}", _map.leaf_count());
                println!("fill_ratio: {:.2}", _map.get_fill_ratio());
                println!("height: {}", _map.height());
            },
            &gen_data,
            use_entry,
        );
        assert_eq!(map.len(), 0, "Map should be empty after deleting all elements");
        assert_eq!(map.height(), 1, "Height should be 1 for empty tree");
        assert_eq!(map.leaf_count(), 1);
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
    {
        println!("test compact");

        let mut map = crate::compact::BTreeMap::<CounterI32, CounterI32>::new();
        _test_large_mixed_random_batch_insert_delete(
            batch_size,
            iterations,
            &mut map,
            |_map: &crate::compact::BTreeMap<CounterI32, CounterI32>| {
                println!("len: {}", _map.len());
                println!("height: {}", _map.height());
            },
            &gen_data,
            use_entry,
        );
        assert_eq!(map.len(), 0, "Map should be empty after deleting all elements");
        assert_eq!(map.height(), 1, "Height should be 1 for empty tree");
    }
    assert_eq!(alive_count(), 0, "All CounterI32 should be dropped");
}

fn _test_large_mixed_random_batch_insert_delete<
    K: Key + Debug,
    V: Key + Debug,
    S: Stats<K>,
    F,
    FR,
>(
    batch_size: usize, iterations: usize, map: &mut BTree<K, V, S>, print_func: F, randf: FR,
    use_entry: bool,
) where
    F: Fn(&BTree<K, V, S>),
    FR: Fn(&mut fastrand::Rng) -> (K, V),
{
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

    macro_rules! insert {
        ($archive: expr, $k: expr, $v: expr) => {
            crate::trace_log!("check contain {:?}", $k);
            if map.contains_key(&$k) {
                // filter duplicated keys
                continue;
            } else {
                crate::trace_log!("insert {:?} {}th", $k, map.len());
                $archive.push(($k.clone(), $v.clone()));
                if use_entry {
                    map.entry($k).or_insert($v);
                } else {
                    map.insert($k, $v);
                }
            }
        };
    }

    macro_rules! remove {
        ($k: expr, $v: expr) => {
            // We try to mix entry ops with non entry ops, see if switching PathBuffer size OK
            let v = if !use_entry {
                if let Entry::Occupied(ent) = map.entry($k.clone()) {
                    Some(ent.remove())
                } else {
                    None
                }
            } else {
                map.remove($k)
            };
            map.validate();
            assert!(v.is_some(), "Key {:?} from prev_batch should exist", $k);
            assert_eq!(&v.unwrap(), $v);
        };
    }

    let mut rng = fastrand::Rng::with_seed(seed);

    // Generate first batch
    let mut prev_batch: Vec<(K, V)> = Vec::with_capacity(batch_size);
    while prev_batch.len() < batch_size {
        let (key, value) = randf(&mut rng);
        insert!(prev_batch, key, value);
    }
    println!("---");
    print_func(map);
    map.validate();
    println!("After first batch: height={}, len={}", map.height(), map.len());

    // For subsequent iterations: insert new batch, then delete previous batch
    for iter in 1..iterations {
        // Insert new batch
        let mut current_batch: Vec<(K, V)> = Vec::with_capacity(batch_size);
        while current_batch.len() < batch_size {
            let (key, value) = randf(&mut rng);
            insert!(current_batch, key, value);
        }
        map.validate();
        println!("---iteration {iter}: insert ---");
        print_func(map);

        // Delete previous batch
        for (_i, (key, _val)) in prev_batch.iter().enumerate() {
            crate::trace_log!("remove {key:?} {_i}th");
            remove!(key, _val);
        }
        map.validate();
        println!("---iteration {iter}: removed ---");
        print_func(map);
        #[cfg(feature = "trace_log")]
        map.inner.print_trigger_flags();

        prev_batch = current_batch;
    }

    let mut height = map.height();

    // Verify all remaining elements are accessible
    for (key, _) in &prev_batch {
        if !map.contains_key(key) {
            map.dump();
            map.validate();
            panic!("error: Remaining key {key:?} should be accessible");
        }
    }

    // Delete remaining elements
    for (key, val) in &prev_batch {
        remove!(key, val);
        if height != map.height() {
            height = map.height();
            #[cfg(feature = "trace_log")]
            map.inner.print_trigger_flags();
            println!("tree height dec to {}, len {}", height, map.len());
        }
    }
    map.validate();

    assert_eq!(map.len(), 0, "Map should be empty after deleting all elements");
    assert_eq!(map.height(), 1, "Height should be 1 for empty tree");
}

#[cfg(not(miri))]
#[logfn]
#[rstest]
#[case(500, 20)]
#[case(1000, 20)]
#[case(10000, 5)]
fn test_large_mix_remove_range_random(
    setup_log: (), #[case] count: usize, #[case] iterations: usize,
) {
    let seed: u64 = match std::env::var("TEST_SEED") {
        Ok(val) => val.parse().expect("TEST_SEED must be a valid u64"),
        Err(_) => fastrand::u64(..),
    };

    fn run_test<S: Stats<CounterI32>>(
        mut map: BTree<CounterI32, CounterI32, S>, count: usize, iterations: usize, seed: u64,
    ) {
        reset_alive_count();
        println!("=== test_mix_remove_range_random seed: {} ===", seed);
        let mut rng = fastrand::Rng::with_seed(seed);

        for i in 0..iterations {
            // 1. Insert random elements
            let mut inserted = 0;
            for _ in 0..count {
                let k = rng.i32(0..20000);
                if !map.contains_key(&k) {
                    trace_log!("insert {k:?}");
                    map.insert(k.into(), (k * 10).into());
                    inserted += 1;
                }
            }
            map.validate();
            log_println!(
                "Iter {}: Inserted {} elements, len: {}, height: {}",
                i,
                inserted,
                map.len(),
                map.height()
            );

            // 2. Select a random range and remove it
            if map.len() > 0 {
                let mut k1 = rng.i32(0..20000);
                let mut k2 = rng.i32(0..20000);
                if k1 > k2 {
                    std::mem::swap(&mut k1, &mut k2);
                }

                let range = CounterI32::from(k1)..=CounterI32::from(k2);
                log_println!("Removing range [{}..={}]", k1, k2);
                map.remove_range(range);
                map.validate();

                // Verify all keys in [k1, k2] are gone
                // Note: iterating 20000 might be slow, but it's acceptable for a few iterations
                for k in k1..=k2 {
                    assert!(!map.contains_key(&k), "Key {} should be removed", k);
                }
            }
        }

        // 3. Clear all remaining
        println!("Final clear all, current len: {}", map.len());
        map.remove_range(..);
        map.validate();
        assert_eq!(map.len(), 0);
        assert_eq!(map.height(), 1);

        assert_eq!(alive_count(), 0, "Memory leak detected after remove_range");
    }

    println!("-- test large ---");
    let map = crate::large::BTreeMap::<CounterI32, CounterI32>::new();
    run_test(map, count, iterations, seed);

    println!("-- test compact ---");
    let map = crate::compact::BTreeMap::<CounterI32, CounterI32>::new();
    run_test(map, count, iterations, seed);
}
