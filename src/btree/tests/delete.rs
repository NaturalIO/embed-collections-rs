use super::super::{inter::*, leaf::*, node::*, *};

/// Test: Basic delete and merge scenario
///
/// Simple test filling a node to capacity then deleting most elements
/// to trigger merge operations. Tests the basic merge path without
/// manual tree construction.
#[test]
fn test_delete_and_merge() {
    let mut map: BTreeMap<i32, i32> = BTreeMap::new();
    let cap = LeafNode::<i32, i32>::cap() as usize;
    // Fill node to capacity
    for i in 0..cap {
        map.insert(i as i32, i as i32 * 10);
        map.validate();
    }
    // Delete most elements to trigger merge
    for i in 0..cap - 2 {
        assert!(map.remove(&(i as i32)).is_some());
        map.validate();
    }
    // Verify remaining elements
    for i in cap - 2..cap {
        assert_eq!(map.get(&(i as i32)), Some(&(i as i32 * 10)));
    }
}

/// Test: Delete all and reinsert
///
/// Tests that the tree remains valid after deleting all elements
/// and then reinserting new ones. Verifies cleanup and reinitialization.
#[test]
fn test_delete_all_and_reinsert() {
    let mut map = BTreeMap::new();
    // Insert some values
    for i in 0..20 {
        map.insert(i, i * 10);
        map.validate();
    }
    // Delete all
    for i in 0..20 {
        assert!(map.remove(&i).is_some());
        map.validate();
    }
    assert!(map.is_empty());
    // Reinsert
    for i in 0..20 {
        map.insert(i, i * 100);
        map.validate();
    }
    // Verify
    for i in 0..20 {
        assert_eq!(map.get(&i), Some(&(i * 100)));
    }
}
