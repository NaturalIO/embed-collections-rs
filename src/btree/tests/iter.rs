use super::super::*;
use core::ops::Bound;

#[test]
fn test_iter_empty() {
    let map: BTreeMap<i32, i32> = BTreeMap::new();
    let mut iter = map.iter();
    assert_eq!(iter.next(), None);
}

#[test]
fn test_iter_single() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    let mut iter = map.iter();
    assert_eq!(iter.next(), Some((&1, &"a")));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_iter_multiple() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    let collected: Vec<_> = map.iter().collect();
    assert_eq!(collected, vec![(&1, &"a"), (&2, &"b"), (&3, &"c")]);
}

#[test]
fn test_iter_large() {
    let mut map = BTreeMap::new();
    // Use at least 3x leaf capacity to ensure multiple leaf nodes
    let leaf_cap = LeafNode::<i32, i32>::cap() as usize;
    let n = leaf_cap * 3 + 10;

    for i in 0..n {
        map.insert(i as i32, i as i32 * 2);
    }

    let collected: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
    let expected: Vec<_> = (0..n).map(|i| (i as i32, i as i32 * 2)).collect();
    assert_eq!(collected, expected);
}

#[test]
fn test_iter_mut() {
    let mut map = BTreeMap::new();
    map.insert(1, 10);
    map.insert(2, 20);
    map.insert(3, 30);

    for (_, v) in map.iter_mut() {
        *v *= 2;
    }

    assert_eq!(map.get(&1), Some(&20));
    assert_eq!(map.get(&2), Some(&40));
    assert_eq!(map.get(&3), Some(&60));
}

#[test]
fn test_keys() {
    let mut map = BTreeMap::new();
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");

    let keys: Vec<_> = map.keys().collect();
    assert_eq!(keys, vec![&1, &2, &3]);
}

#[test]
fn test_values() {
    let mut map = BTreeMap::new();
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");

    let values: Vec<_> = map.values().collect();
    assert_eq!(values, vec![&"a", &"b", &"c"]);
}

#[test]
fn test_values_mut() {
    let mut map = BTreeMap::new();
    map.insert(1, 10);
    map.insert(2, 20);
    map.insert(3, 30);

    for v in map.values_mut() {
        *v += 1;
    }

    assert_eq!(map.get(&1), Some(&11));
    assert_eq!(map.get(&2), Some(&21));
    assert_eq!(map.get(&3), Some(&31));
}

#[test]
fn test_for_loop() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    let mut collected = Vec::new();
    for (k, v) in &map {
        collected.push((*k, *v));
    }
    assert_eq!(collected, vec![(1, "a"), (2, "b"), (3, "c")]);
}

#[test]
fn test_for_loop_mut() {
    let mut map = BTreeMap::new();
    map.insert(1, 10);
    map.insert(2, 20);
    map.insert(3, 30);

    for (_, v) in &mut map {
        *v *= 2;
    }

    assert_eq!(map.get(&1), Some(&20));
    assert_eq!(map.get(&2), Some(&40));
    assert_eq!(map.get(&3), Some(&60));
}

#[test]
fn test_iter_after_split() {
    let mut map = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;

    // Insert enough to trigger splits
    for i in 0..(cap + 10) {
        map.insert(i as i32, i as i32 * 10);
    }

    let collected: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
    let expected: Vec<_> = (0..(cap + 10)).map(|i| (i as i32, i as i32 * 10)).collect();
    assert_eq!(collected, expected);
}

#[test]
fn test_iter_with_deletes() {
    let mut map = BTreeMap::new();

    for i in 0..20 {
        map.insert(i, i * 10);
    }

    // Remove some elements
    map.remove(&5);
    map.remove(&10);
    map.remove(&15);

    let collected: Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();

    assert_eq!(collected.len(), 17);
    assert!(!collected.iter().any(|(k, _)| *k == 5 || *k == 10 || *k == 15));
}

#[test]
fn test_iter_exact_size() {
    let mut map = BTreeMap::new();
    for i in 0..10 {
        map.insert(i, i * 10);
    }

    let iter = map.iter();
    assert_eq!(iter.len(), 10);

    // After consuming some elements, len should decrease
    let mut iter = map.iter();
    iter.next();
    assert_eq!(iter.len(), 9);
    iter.next();
    assert_eq!(iter.len(), 8);
}

#[test]
fn test_iter_double_ended_single_leaf() {
    let mut map = BTreeMap::new();
    for i in 0..5 {
        map.insert(i, i * 10);
    }

    let collected: Vec<_> = map.iter().rev().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(4, 40), (3, 30), (2, 20), (1, 10), (0, 0)]);
}

#[test]
fn test_iter_double_ended_multi_leaf() {
    // Test with at least 3 leaf nodes to ensure proper multi-leaf navigation
    let leaf_cap = LeafNode::<i32, i32>::cap() as usize;
    let n = leaf_cap * 3 + 10;

    let mut map = BTreeMap::new();
    for i in 0..n {
        map.insert(i as i32, i as i32 * 10);
    }
    map.dump();

    // Test full reverse iteration
    let collected: Vec<_> = map.iter().rev().map(|(k, v)| (*k, *v)).collect();
    let expected: Vec<_> = (0..n).rev().map(|i| (i as i32, i as i32 * 10)).collect();
    assert_eq!(collected, expected);

    // Test mixed forward/backward
    let mut iter = map.iter();
    let first = iter.next().map(|(k, v)| (*k, *v));
    let last = iter.next_back().map(|(k, v)| (*k, *v));
    assert_eq!(first, Some((0, 0)));
    assert_eq!(last, Some(((n - 1) as i32, (n - 1) as i32 * 10)));
}

#[test]
fn test_iter_mixed_forward_backward_multi_leaf() {
    // Test mixed iteration with at least 3 leaf nodes
    let leaf_cap = LeafNode::<i32, i32>::cap() as usize;
    let n = leaf_cap * 3 + 10;

    let mut map = BTreeMap::new();
    for i in 0..n {
        map.insert(i as i32, i as i32 * 10);
    }

    let mut iter = map.iter();
    let mut collected = Vec::new();

    // Alternate between next() and next_back()
    for _ in 0..n / 2 {
        if let Some((k, v)) = iter.next() {
            collected.push((*k, *v));
        }
        if let Some((k, v)) = iter.next_back() {
            collected.push((*k, *v));
        }
    }

    // Collect any remaining middle element
    if let Some((k, v)) = iter.next() {
        collected.push((*k, *v));
    }

    // Verify we collected all elements
    assert_eq!(collected.len(), n);

    // Verify no duplicates
    let unique_count =
        collected.iter().map(|(k, _)| *k).collect::<std::collections::HashSet<_>>().len();
    assert_eq!(unique_count, n);

    // Verify all values are correct
    for (k, v) in &collected {
        assert_eq!(*v, *k * 10);
    }
}

#[test]
fn test_iter_mixed_forward_backward() {
    let mut map = BTreeMap::new();
    for i in 0..6 {
        map.insert(i, i * 10);
    }

    let mut iter = map.iter();
    assert_eq!(iter.next(), Some((&0, &0)));
    assert_eq!(iter.next_back(), Some((&5, &50)));
    assert_eq!(iter.next(), Some((&1, &10)));
    assert_eq!(iter.next_back(), Some((&4, &40)));
    assert_eq!(iter.next(), Some((&2, &20)));
    assert_eq!(iter.next_back(), Some((&3, &30)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
}

#[test]
fn test_iter_mut_double_ended() {
    let mut map = BTreeMap::new();
    for i in 0..5 {
        map.insert(i, i * 10);
    }

    // Test that we can iterate in reverse
    let collected: Vec<_> = map.iter_mut().rev().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(4, 40), (3, 30), (2, 20), (1, 10), (0, 0)]);
}

#[test]
fn test_iter_mut_exact_size() {
    let mut map = BTreeMap::new();
    for i in 0..10 {
        map.insert(i, i * 10);
    }

    let iter = map.iter_mut();
    assert_eq!(iter.len(), 10);
}

#[test]
fn test_keys_double_ended() {
    let mut map = BTreeMap::new();
    for i in 0..5 {
        map.insert(i, i * 10);
    }

    let collected: Vec<_> = map.keys().rev().copied().collect();
    assert_eq!(collected, vec![4, 3, 2, 1, 0]);
}

#[test]
fn test_values_double_ended() {
    let mut map = BTreeMap::new();
    for i in 0..5 {
        map.insert(i, i * 10);
    }

    let collected: Vec<_> = map.values().rev().copied().collect();
    assert_eq!(collected, vec![40, 30, 20, 10, 0]);
}

#[test]
fn test_values_mut_double_ended() {
    let mut map = BTreeMap::new();
    for i in 0..5 {
        map.insert(i, i * 10);
    }

    let collected: Vec<_> = map.values_mut().rev().map(|v| *v).collect();
    assert_eq!(collected, vec![40, 30, 20, 10, 0]);
}

#[test]
fn test_iter_empty_double_ended() {
    let map: BTreeMap<i32, i32> = BTreeMap::new();
    let mut iter = map.iter();
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.len(), 0);
}

#[test]
fn test_iter_single_double_ended() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");

    let mut iter = map.iter();
    assert_eq!(iter.next(), Some((&1, &"a")));
    assert_eq!(iter.next_back(), None);
}

#[test]
fn test_range_basic() {
    let mut map = BTreeMap::<u32, u32>::new();

    for i in 0..10 {
        map.insert(i, i * 10);
    }
    // Test inclusive range
    let collected: Vec<_> = map.range(3..=6).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(3, 30), (4, 40), (5, 50), (6, 60)]);
    // Test exclusive range
    let collected: Vec<_> = map.range(3..7).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(3, 30), (4, 40), (5, 50), (6, 60)]);
    // Test unbounded start
    let collected: Vec<_> = map.range(..=3).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(0, 0), (1, 10), (2, 20), (3, 30)]);
    // Test unbounded end
    let collected: Vec<_> = map.range(7..).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(7, 70), (8, 80), (9, 90)]);
    // Test full range
    let collected: Vec<_> = map.range(..).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected.len(), 10);
}

#[test]
fn test_range_mut() {
    let mut map = BTreeMap::<u32, u32>::new();

    for i in 0..10 {
        map.insert(i, i * 10);
    }
    // Modify values in range
    for (_, v) in map.range_mut(3..=6) {
        *v *= 2;
    }
    assert_eq!(map.get(&2), Some(&20)); // Unchanged
    assert_eq!(map.get(&3), Some(&60)); // Changed
    assert_eq!(map.get(&6), Some(&120)); // Changed
    assert_eq!(map.get(&7), Some(&70)); // Unchanged
}

#[test]
fn test_range_empty() {
    let map: BTreeMap<i32, i32> = BTreeMap::new();
    let collected: Vec<_> = map.range(0..10).collect();
    assert!(collected.is_empty());
}

#[test]
fn test_range_boundaries() {
    let mut map = BTreeMap::new();

    // Insert even numbers only: 0, 2, 4, 6, 8
    for i in [0, 2, 4, 6, 8] {
        map.insert(i, i * 10);
    }

    // Test: Included(key) where key exists
    let collected: Vec<_> = map.range(2..=6).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(2, 20), (4, 40), (6, 60)]);

    // Test: Included(key) where key does NOT exist (should start from next greater)
    let collected: Vec<_> = map.range(1..=5).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(2, 20), (4, 40)]);

    let r = (Bound::Excluded(2), Bound::Excluded(6));
    println!("range {r:?}");
    // Test: Excluded(key) where key exists (should start from next greater)
    let collected: Vec<_> = map.range(r).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(4, 40)]);

    // Test: Excluded(key) where key does NOT exist
    let collected: Vec<_> =
        map.range((Bound::Excluded(1), Bound::Excluded(5))).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(2, 20), (4, 40)]);

    // Test: Excluded end where key exists
    let collected: Vec<_> = map.range(0..6).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(0, 0), (2, 20), (4, 40)]);

    // Test: Excluded end where key does NOT exist
    let collected: Vec<_> = map.range(0..5).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(0, 0), (2, 20), (4, 40)]);

    // Test: Included end where key exists
    let collected: Vec<_> = map.range(0..=6).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(0, 0), (2, 20), (4, 40), (6, 60)]);

    // Test: Included end where key does NOT exist
    let collected: Vec<_> = map.range(0..=5).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(0, 0), (2, 20), (4, 40)]);

    // Test: Single element with Included/Included
    let collected: Vec<_> = map.range(4..=4).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(4, 40)]);

    // Test: Empty range (Excluded/Excluded on same key)
    let collected: Vec<_> = map.range(4..4).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![]);

    // Test: Range before first element
    let collected: Vec<_> = map.range(..0).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![]);

    // Test: Range after last element
    let collected: Vec<_> = map.range(10..).map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![]);
}

#[test]
fn test_range_double_ended_single_leaf() {
    let mut map = BTreeMap::new();
    for i in 0..10 {
        map.insert(i, i * 10);
    }

    // Test full reverse iteration of a range
    let collected: Vec<_> = map.range(3..=7).rev().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(collected, vec![(7, 70), (6, 60), (5, 50), (4, 40), (3, 30)]);

    // Test mixed forward/backward
    let mut iter = map.range(2..=8);
    let first = iter.next().map(|(k, v)| (*k, *v));
    let last = iter.next_back().map(|(k, v)| (*k, *v));
    let second = iter.next().map(|(k, v)| (*k, *v));
    let second_last = iter.next_back().map(|(k, v)| (*k, *v));

    assert_eq!(first, Some((2, 20)));
    assert_eq!(last, Some((8, 80)));
    assert_eq!(second, Some((3, 30)));
    assert_eq!(second_last, Some((7, 70)));

    // Continue until exhausted
    assert_eq!(iter.next().map(|(k, v)| (*k, *v)), Some((4, 40)));
    assert_eq!(iter.next_back().map(|(k, v)| (*k, *v)), Some((6, 60)));
    assert_eq!(iter.next().map(|(k, v)| (*k, *v)), Some((5, 50)));
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next(), None);
}

#[test]
fn test_range_double_ended_multi_leaf() {
    // Test with at least 3 leaf nodes
    let leaf_cap = LeafNode::<i32, i32>::cap() as usize;
    let n = leaf_cap * 3 + 10;

    let mut map = BTreeMap::new();
    for i in 0..n {
        map.insert(i as i32, i as i32 * 10);
    }
    map.dump();

    // Test range spanning multiple leaves
    let range_start = leaf_cap as i32;
    let range_end = (leaf_cap * 2 + 5) as i32;

    let r = range_start..=range_end;
    println!("range {r:?}");

    // Test full reverse iteration
    let collected: Vec<_> = map.range(r).rev().map(|(k, v)| (*k, *v)).collect();
    let expected: Vec<_> = (range_start..=range_end).rev().map(|i| (i, i * 10)).collect();
    assert_eq!(collected, expected);

    let r = range_start..range_end;
    println!("range {r:?}");
    // Test mixed forward/backward with specific assertions
    let mut iter = map.range(r);

    // First round: next() then next_back()
    assert_eq!(iter.next(), Some((&range_start, &(range_start * 10))));
    println!("next {}", range_start);
    assert_eq!(iter.next_back(), Some((&(range_end - 1), &((range_end - 1) * 10))));
    println!("back {}", range_end - 1);

    // Second round
    assert_eq!(iter.next(), Some((&(range_start + 1), &((range_start + 1) * 10))));

    println!("next {}", range_start + 1);
    assert_eq!(iter.next_back(), Some((&(range_end - 2), &((range_end - 2) * 10))));
    println!("back {}", range_end - 2);

    // Third round
    assert_eq!(iter.next(), Some((&(range_start + 2), &((range_start + 2) * 10))));

    println!("next key {}", range_start + 2);
    assert_eq!(
        iter.next_back().map(|(k, v)| (*k, *v)),
        Some((range_end - 3, (range_end - 3) * 10))
    );
    println!("back key {}", range_end - 3);

    // Continue until exhausted - collect remaining elements
    let mut remaining_forward: Vec<(i32, i32)> = Vec::new();

    while let Some((k, v)) = iter.next() {
        remaining_forward.push((*k, *v));
    }

    // Iterator should be exhausted
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next(), None);

    // Verify remaining elements are in correct order
    // After taking 3 from front and 3 from back, remaining should be:
    // range_start+3 .. range_end-3
    let expected_remaining: Vec<(i32, i32)> =
        ((range_start + 3)..(range_end - 3)).map(|i| (i, i * 10)).collect();
    assert_eq!(remaining_forward, expected_remaining);
}

#[test]
fn test_into_iter() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    let collected: Vec<_> = map.into_iter().collect();
    assert_eq!(collected, vec![(1, "a"), (2, "b"), (3, "c")]);
}

#[test]
fn test_into_iter_empty() {
    let map: BTreeMap<i32, i32> = BTreeMap::new();
    let mut iter = map.into_iter();
    assert_eq!(iter.next(), None);
}

#[test]
fn test_into_iter_large() {
    let mut map = BTreeMap::new();
    let n = 1000;

    for i in 0..n {
        map.insert(i, i * 2);
    }

    let collected: Vec<_> = map.into_iter().collect();
    let expected: Vec<_> = (0..n).map(|i| (i, i * 2)).collect();
    assert_eq!(collected, expected);
}
