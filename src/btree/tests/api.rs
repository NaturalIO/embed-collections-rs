use super::{TestBTreeMap, TestStats};
use crate::btree::*;

#[test]
fn test_simple() {
    let (inter_cap, leaf_cap) = TestBTreeMap::<i32, &'static str>::cap();
    println!("cap: inter {inter_cap} leaf {leaf_cap}");
    let mut map: TestBTreeMap<i32, &'static str> = BTreeMap::new_with_state(TestStats::new());
    assert!(map.is_empty());
    assert_eq!(map.len(), 0);
    assert_eq!(map.get(&1), None);
    assert!(!map.contains_key(&1));
    assert_eq!(map.insert(1, "a"), None);
    map.validate();
    assert_eq!(map.get(&1), Some(&"a"));
    assert_eq!(map.len(), 1);
    // insert duplicate
    assert_eq!(map.insert(1, "b"), Some("a"));
    map.validate();
    assert_eq!(map.get(&1), Some(&"b"));
    assert_eq!(map.len(), 1);
    // get_mut
    if let Some(v) = map.get_mut(&1) {
        *v = "c";
    }
    map.validate();
    assert_eq!(map.get(&1), Some(&"c"));
    assert!(map.contains_key(&1));
    assert!(!map.contains_key(&2));
}

#[test]
fn test_multiple_inserts() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    map.insert(3, "c");
    map.validate();
    map.insert(1, "a");
    map.validate();
    map.insert(2, "b");
    map.validate();
    assert_eq!(map.get(&1), Some(&"a"));
    assert_eq!(map.get(&2), Some(&"b"));
    assert_eq!(map.get(&3), Some(&"c"));
    assert_eq!(map.len(), 3);
}

#[test]
fn test_entry_occupied() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    map.insert(1, "a");
    map.validate();
    match map.entry(1) {
        Entry::Occupied(entry) => {
            assert_eq!(entry.get(), &"a");
        }
        Entry::Vacant(_) => panic!("Expected occupied entry"),
    }
}

#[test]
fn test_occupied_entry_remove() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    map.insert(1, "a");
    map.validate();
    match map.entry(1) {
        Entry::Occupied(entry) => {
            assert_eq!(entry.remove(), "a");
        }
        _ => panic!("Expected occupied entry"),
    }
    map.validate();
    assert!(map.is_empty());
}

#[test]
fn test_entry_vacant() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    match map.entry(1) {
        Entry::Vacant(entry) => {
            assert_eq!(entry.key(), &1);
        }
        Entry::Occupied(_) => panic!("Expected vacant entry"),
    }
}

#[test]
fn test_entry_or_insert() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    let val = map.entry(1).or_insert("a");
    assert_eq!(*val, "a");
    map.validate();
    let val = map.entry(1).or_insert("b");
    assert_eq!(*val, "a");
    map.validate();
}

#[test]
fn test_entry_and_modify() {
    let mut map: TestBTreeMap<i32, i32> = BTreeMap::new_with_state(TestStats::new());
    map.insert(1, 10);
    map.validate();
    map.entry(1).and_modify(|v| *v = 20);
    map.validate();
    assert_eq!(map.get(&1), Some(&20));
}

#[test]
fn test_remove() {
    let mut map: TestBTreeMap<i32, &str> = BTreeMap::new_with_state(TestStats::new());
    map.insert(1, "a");
    map.validate();
    map.insert(2, "b");
    map.validate();
    assert_eq!(map.remove(&1), Some("a"));
    map.validate();
    assert_eq!(map.get(&1), None);
    assert_eq!(map.len(), 1);
    assert_eq!(map.remove(&3), None);
    map.validate();
    assert_eq!(map.len(), 1);
}
