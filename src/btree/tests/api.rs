use super::super::*;

#[test]
fn test_simple() {
    let (inter_cap, leaf_cap) = BTreeMap::<i32, &'static str>::cap();
    println!("cap: inter {inter_cap} leaf {leaf_cap}");
    let mut map: BTreeMap<i32, &'static str> = BTreeMap::new();
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
    let mut map = BTreeMap::new();
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
    let mut map = BTreeMap::new();
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
    let mut map = BTreeMap::new();
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
    let mut map: BTreeMap<i32, &str> = BTreeMap::new();
    match map.entry(1) {
        Entry::Vacant(entry) => {
            assert_eq!(entry.key(), &1);
        }
        Entry::Occupied(_) => panic!("Expected vacant entry"),
    }
}

#[test]
fn test_entry_or_insert() {
    let mut map = BTreeMap::new();
    let val = map.entry(1).or_insert("a");
    assert_eq!(*val, "a");
    map.validate();
    let val = map.entry(1).or_insert("b");
    assert_eq!(*val, "a");
    map.validate();
}

#[test]
fn test_entry_and_modify() {
    let mut map = BTreeMap::new();
    map.insert(1, 10);
    map.validate();
    map.entry(1).and_modify(|v| *v = 20);
    map.validate();
    assert_eq!(map.get(&1), Some(&20));
}

#[test]
fn test_remove() {
    let mut map = BTreeMap::new();
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

#[test]
fn test_first_last_key_value_multiple() {
    let mut map = BTreeMap::new();
    assert_eq!(map.first_key_value(), None);
    assert_eq!(map.last_key_value(), None);
    map.insert(3, "c");
    assert_eq!(map.first_key_value(), Some((&3, &"c")));
    assert_eq!(map.last_key_value(), Some((&3, &"c")));
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    assert_eq!(map.first_key_value(), Some((&1, &"a")));
    assert_eq!(map.last_key_value(), Some((&3, &"c")));
    map.remove(&3);
    map.validate();
    assert_eq!(map.first_key_value(), Some((&1, &"a")));
    assert_eq!(map.last_key_value(), Some((&2, &"b")));
}

#[test]
fn test_first_last_entry_single() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.validate();
    match map.first_entry() {
        Some(Entry::Occupied(entry)) => {
            assert_eq!(entry.get(), &"a");
        }
        _ => panic!("Expected occupied entry"),
    }
    match map.last_entry() {
        Some(Entry::Occupied(entry)) => {
            assert_eq!(entry.get(), &"a");
        }
        _ => panic!("Expected occupied entry"),
    }
}

#[test]
fn test_first_last_entry_multiple() {
    let mut map = BTreeMap::new();
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    match map.first_entry() {
        Some(Entry::Occupied(entry)) => {
            assert_eq!(entry.get(), &"a");
            assert_eq!(entry.key(), &1);
        }
        _ => panic!("Expected occupied entry"),
    }
    match map.last_entry() {
        Some(Entry::Occupied(entry)) => {
            assert_eq!(entry.get(), &"c");
            assert_eq!(entry.key(), &3);
        }
        _ => panic!("Expected occupied entry"),
    }
}

#[test]
fn test_first_entry_modify() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    if let Some(Entry::Occupied(mut entry)) = map.first_entry() {
        entry.insert("aa");
    }
    map.validate();
    assert_eq!(map.get(&1), Some(&"aa"));
    assert_eq!(map.get(&2), Some(&"b"));
}

#[test]
fn test_last_entry_modify() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    if let Some(Entry::Occupied(mut entry)) = map.last_entry() {
        entry.insert("bb");
    }
    map.validate();
    assert_eq!(map.get(&1), Some(&"a"));
    assert_eq!(map.get(&2), Some(&"bb"));
}

#[test]
fn test_first_entry_remove() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    if let Some(Entry::Occupied(entry)) = map.first_entry() {
        assert_eq!(entry.remove(), "a");
    }
    map.validate();
    assert_eq!(map.get(&1), None);
    assert_eq!(map.len(), 2);
    assert_eq!(map.first_key_value(), Some((&2, &"b")));
}

#[test]
fn test_last_entry_remove() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    if let Some(Entry::Occupied(entry)) = map.last_entry() {
        assert_eq!(entry.remove(), "c");
    }
    map.validate();
    assert_eq!(map.get(&3), None);
    assert_eq!(map.len(), 2);
    assert_eq!(map.last_key_value(), Some((&2, &"b")));
}

#[test]
fn test_large_tree_operations() {
    let mut map = BTreeMap::new();
    // Insert enough elements to trigger splits (leaf capacity is typically small)
    for i in 0..1000 {
        map.insert(i, i * 2);
    }
    map.validate();

    // Test first_key_value and last_key_value
    assert_eq!(map.first_key_value(), Some((&0, &0)));
    assert_eq!(map.last_key_value(), Some((&999, &1998)));

    // Test entry API on large tree
    if let Some(Entry::Occupied(entry)) = map.first_entry() {
        assert_eq!(entry.key(), &0);
        assert_eq!(entry.get(), &0);
    } else {
        panic!("Expected first entry");
    }

    if let Some(Entry::Occupied(entry)) = map.last_entry() {
        assert_eq!(entry.key(), &999);
        assert_eq!(entry.get(), &1998);
    } else {
        panic!("Expected last entry");
    }

    // Test pop_first on large tree - pop first 10 elements
    for i in 0..10 {
        assert_eq!(map.pop_first(), Some((i, i * 2)));
        map.validate();
    }
    assert_eq!(map.len(), 990);
    assert_eq!(map.first_key_value(), Some((&10, &20)));

    // Test pop_last on large tree - pop last 10 elements
    for i in 0..10 {
        assert_eq!(map.pop_last(), Some((999 - i, (999 - i) * 2)));
        map.validate();
    }
    assert_eq!(map.len(), 980);
    assert_eq!(map.last_key_value(), Some((&989, &1978)));

    // Verify remaining elements
    assert_eq!(map.first_key_value(), Some((&10, &20)));
    assert_eq!(map.last_key_value(), Some((&989, &1978)));
}

#[test]
fn test_pop_first_multiple() {
    let mut map = BTreeMap::new();
    assert_eq!(map.pop_last(), None);
    assert_eq!(map.pop_first(), None);
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    assert_eq!(map.pop_first(), Some((1, "a")));
    map.validate();
    assert_eq!(map.len(), 2);
    assert_eq!(map.first_key_value(), Some((&2, &"b")));
    assert_eq!(map.last_key_value(), Some((&3, &"c")));
}

#[test]
fn test_pop_last_multiple() {
    let mut map = BTreeMap::new();
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");
    map.validate();
    assert_eq!(map.pop_last(), Some((3, "c")));
    map.validate();
    assert_eq!(map.len(), 2);
    assert_eq!(map.first_key_value(), Some((&1, &"a")));
    assert_eq!(map.last_key_value(), Some((&2, &"b")));
}

#[test]
fn test_pop_first_all() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    assert_eq!(map.pop_first(), Some((1, "a")));
    map.validate();
    assert_eq!(map.pop_first(), Some((2, "b")));
    map.validate();
    assert_eq!(map.pop_first(), Some((3, "c")));
    map.validate();
    assert!(map.is_empty());
    assert_eq!(map.pop_first(), None);
}

#[test]
fn test_pop_last_all() {
    let mut map = BTreeMap::new();
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    assert_eq!(map.pop_last(), Some((3, "c")));
    map.validate();
    assert_eq!(map.pop_last(), Some((2, "b")));
    map.validate();
    assert_eq!(map.pop_last(), Some((1, "a")));
    map.validate();
    assert!(map.is_empty());
    assert_eq!(map.pop_last(), None);
}

#[test]
fn test_borrow_string_str() {
    let mut map: BTreeMap<String, i32> = BTreeMap::new();
    map.insert("hello".to_string(), 1);
    map.insert("world".to_string(), 2);
    map.insert("foo".to_string(), 3);
    map.validate();

    // Test get with &str
    assert_eq!(map.get("hello"), Some(&1));
    assert_eq!(map.get("world"), Some(&2));
    assert_eq!(map.get("foo"), Some(&3));
    assert_eq!(map.get("not_exist"), None);

    // Test contains_key with &str
    assert!(map.contains_key("hello"));
    assert!(map.contains_key("world"));
    assert!(!map.contains_key("not_exist"));

    // Test get_mut with &str
    if let Some(v) = map.get_mut("hello") {
        *v = 100;
    }
    map.validate();
    assert_eq!(map.get("hello"), Some(&100));

    // Test remove with &str
    assert_eq!(map.remove("foo"), Some(3));
    map.validate();
    assert_eq!(map.get("foo"), None);
    assert_eq!(map.len(), 2);
}

#[test]
fn test_borrow_vec_slice() {
    let mut map: BTreeMap<Vec<u8>, i32> = BTreeMap::new();
    map.insert(vec![1, 2, 3], 1);
    map.insert(vec![4, 5, 6], 2);
    map.validate();

    // Test get with &[u8]
    assert_eq!(map.get(&[1, 2, 3][..]), Some(&1));
    assert_eq!(map.get(&[4, 5, 6][..]), Some(&2));
    assert_eq!(map.get(&[7, 8, 9][..]), None);

    // Test contains_key with &[u8]
    assert!(map.contains_key(&[1, 2, 3][..]));
    assert!(!map.contains_key(&[7, 8, 9][..]));

    // Test remove with &[u8]
    assert_eq!(map.remove(&[1, 2, 3][..]), Some(1));
    map.validate();
    assert_eq!(map.len(), 1);
}
