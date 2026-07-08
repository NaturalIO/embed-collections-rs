use super::super::{inter::*, leaf::*, *};
use captains_log::logfn;
use rstest::*;
use std::println;
use std::vec;
use test_common::setup_log;

#[test]
fn test_btree_large_tree_split_seq() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let (inter_cap, leaf_cap) = BTreeMap::<i32, i32>::cap();
    assert!(100 > inter_cap);
    assert!(100 > leaf_cap);
    // Insert many values to create multi-level tree
    for i in 0..100 {
        assert_eq!(map.insert(i, i * 2), None);
        map.validate();
    }
    assert_eq!(map.len(), 100);
    println!("tree height {}", map.height());
    // Verify all values
    for i in 0..100 {
        assert_eq!(map.get(&i), Some(&(i * 2)));
    }
}

#[test]
fn test_btree_random_inserts() {
    let mut map: BTreeMap<i32, &str> = BTreeMap::new();
    let values = vec![
        (5, "e"),
        (3, "c"),
        (7, "g"),
        (1, "a"),
        (9, "i"),
        (2, "b"),
        (4, "d"),
        (6, "f"),
        (8, "h"),
    ];
    for (k, v) in &values {
        map.insert(*k, *v);
        map.validate();
    }
    for (k, v) in &values {
        assert_eq!(map.get(k), Some(v));
    }
    //map.dump();
}

#[test]
fn test_node_capacity() {
    // On x86_64 with 64-byte cache line:
    // Leaf: (128 - 16) / 8 = 14 keys/values, but limited by smaller of key/value space
    // Actually should be (128-16)/8 = 14 for both keys and values
    let leaf_cap = LeafNode::<i64, i64>::cap();
    let inter_cap = InterNode::<i64, i64>::cap();

    // Leaf can hold more because keys and values share the same space
    assert!(leaf_cap >= 2, "Leaf should hold at least 2 items");
    // Internal: n keys, n+1 children
    assert!(inter_cap >= 2, "Internal node should hold at least 2 keys");
}

#[logfn]
#[rstest]
fn test_btree_split_leaf_root_with_treeinfo(setup_log: ()) {
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
    let leaf_cap = LeafNode::<u32, u32>::cap();
    for k in 0..(leaf_cap + 1) {
        map.insert(k, k * 10);
    }
    assert_eq!(map.leaf_count(), 2);
    map.validate();
    for k in 0..(leaf_cap + 1) {
        map.remove(&k);
    }
    map.validate();
    assert_eq!(map.leaf_count(), 1);
    assert_eq!(map.len(), 0);
    // re-insert
    for k in 0..(leaf_cap + 1) {
        map.insert(k, k * 10);
    }
    assert_eq!(map.leaf_count(), 2);
    map.validate();
}
