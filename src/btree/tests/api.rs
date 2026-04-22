use super::super::helper::*;
use super::super::*;
use core::mem::size_of;

#[test]
fn test_size() {
    let root = size_of::<Option<Node<u32, u32>>>();
    println!("size: root {}", root);
    let path_cache = size_of::<TreeInfo<u32, u32>>();
    println!("size: path_cache {}", path_cache);
    let tree = size_of::<BTreeMap<u32, u32>>();
    println!("size: BTreeMap {}", tree);
    let s_tree = size_of::<alloc::collections::BTreeMap<u32, u32>>();
    println!("size: std BTreeMap {}", s_tree);
}

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
fn test_zero_size() {
    let (inter_cap, leaf_cap) = BTreeMap::<u8, ()>::cap();
    println!("cap: inter {inter_cap} leaf {leaf_cap}");
    let mut map: BTreeMap<u8, ()> = BTreeMap::new();
    for i in 0u8..=u8::MAX {
        map.insert(i, ());
    }
    for i in 0u8..=u8::MAX {
        assert_eq!(map.get(&i), Some(&()));
    }
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
        Some(entry) => {
            assert_eq!(entry.get(), &"a");
        }
        _ => panic!("Expected occupied entry"),
    }
    match map.last_entry() {
        Some(entry) => {
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
        Some(entry) => {
            assert_eq!(entry.get(), &"a");
            assert_eq!(entry.key(), &1);
        }
        _ => panic!("Expected occupied entry"),
    }
    match map.last_entry() {
        Some(entry) => {
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
    if let Some(mut entry) = map.first_entry() {
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
    if let Some(mut entry) = map.last_entry() {
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
    if let Some(entry) = map.first_entry() {
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
    if let Some(entry) = map.last_entry() {
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
    if let Some(entry) = map.first_entry() {
        assert_eq!(entry.key(), &0);
        assert_eq!(entry.get(), &0);
    } else {
        panic!("Expected first entry");
    }

    if let Some(entry) = map.last_entry() {
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
    assert_eq!(map.leaf_count(), 0);
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    assert_eq!(map.leaf_count(), 1);
    assert_eq!(map.pop_first(), Some((1, "a")));
    map.validate();
    assert_eq!(map.pop_first(), Some((2, "b")));
    map.validate();
    assert_eq!(map.pop_first(), Some((3, "c")));
    map.validate();
    assert!(map.is_empty());
    assert_eq!(map.pop_first(), None);
    assert_eq!(map.leaf_count(), 1);
}

#[test]
fn test_pop_last_all() {
    let mut map = BTreeMap::new();
    assert_eq!(map.leaf_count(), 0);
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.validate();
    assert_eq!(map.leaf_count(), 1);
    assert_eq!(map.pop_last(), Some((3, "c")));
    map.validate();
    assert_eq!(map.pop_last(), Some((2, "b")));
    map.validate();
    assert_eq!(map.pop_last(), Some((1, "a")));
    map.validate();
    assert!(map.is_empty());
    assert_eq!(map.pop_last(), None);
    assert_eq!(map.leaf_count(), 1);
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

#[test]
fn test_remove_range_api() {
    use core::ops::Bound;
    let mut map = BTreeMap::new();
    for i in 1..=10 {
        map.insert(i, i * 10);
    }
    map.validate();

    // 1. [2, 4] -> should remove 2, 3, 4
    let mut removed = Vec::new();
    let last = map.remove_range_with(2..=4, |k, v| removed.push((*k, *v)));
    assert_eq!(last, Some((4, 40)));
    assert_eq!(removed, vec![(2, 20), (3, 30), (4, 40)]);
    map.validate();
    assert_eq!(map.len(), 7);
    assert!(!map.contains_key(&2));
    assert!(!map.contains_key(&3));
    assert!(!map.contains_key(&4));
    assert!(map.contains_key(&1));
    assert!(map.contains_key(&5));

    // 2. (5, 7) -> should remove 6
    let mut removed = Vec::new();
    let last = map
        .remove_range_with((Bound::Excluded(5), Bound::Excluded(7)), |k, v| removed.push((*k, *v)));
    assert_eq!(last, Some((6, 60)));
    assert_eq!(removed, vec![(6, 60)]);
    map.validate();
    assert_eq!(map.len(), 6);
    assert!(!map.contains_key(&6));
    assert!(map.contains_key(&5));
    assert!(map.contains_key(&7));

    // 3. ..3 -> should remove 1 (only 1 is in range, since 2,3,4 are gone)
    // Wait, remaining are 1, 5, 7, 8, 9, 10
    // ..3 means keys < 3. Only 1 is < 3.
    let mut removed = Vec::new();
    let last = map.remove_range_with(..3, |k, v| removed.push((*k, *v)));
    assert_eq!(last, Some((1, 10)));
    assert_eq!(removed, vec![(1, 10)]);
    map.validate();
    assert_eq!(map.len(), 5);
    assert!(!map.contains_key(&1));

    // 4. 9.. -> should remove 9, 10
    let mut removed = Vec::new();
    let last = map.remove_range_with(9.., |k, v| removed.push((*k, *v)));
    assert_eq!(last, Some((10, 100)));
    assert_eq!(removed, vec![(9, 90), (10, 100)]);
    map.validate();
    assert_eq!(map.len(), 3); // remaining: 5, 7, 8
    assert!(!map.contains_key(&9));
    assert!(!map.contains_key(&10));

    // 5. .. -> remove all
    let mut removed = Vec::new();
    let last = map.remove_range_with(.., |k, v| removed.push((*k, *v)));
    assert_eq!(last, Some((8, 80)));
    assert_eq!(removed, vec![(5, 50), (7, 70), (8, 80)]);
    map.validate();
    assert!(map.is_empty());
}

#[test]
fn test_remove_range_large() {
    let mut map = BTreeMap::new();
    let (_, leaf_cap) = BTreeMap::<i32, i32>::cap();
    let count = leaf_cap * 5; // multiple leaves
    for i in 0..count {
        map.insert(i as i32, i as i32);
    }
    map.validate();
    assert!(map.height() > 1);

    // remove a range that spans multiple leaves
    let start = leaf_cap / 2;
    let end = count - leaf_cap / 2;
    let mut count_removed = 0;
    let last = map.remove_range_with(start as i32..end as i32, |_, _| {
        count_removed += 1;
    });
    assert_eq!(last, Some(((end - 1) as i32, (end - 1) as i32)));
    assert_eq!(count_removed, end - start);
    map.validate();

    // verify remaining
    for i in 0..count {
        let i = i as i32;
        if i >= start as i32 && i < end as i32 {
            assert!(!map.contains_key(&i), "Key {} should be removed", i);
        } else {
            assert!(map.contains_key(&i), "Key {} should remain", i);
        }
    }
    assert_eq!(map.len(), (start + leaf_cap / 2) as usize);
}
