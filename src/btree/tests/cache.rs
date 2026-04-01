use super::super::{inter::*, leaf::*, node::*, *};
use core::cell::UnsafeCell;

/// Test PathCache with actual tree operations
#[test]
fn test_path_cache_with_tree_operations() {
    unsafe {
        let leaf_cap = LeafNode::<i32, i32>::cap();

        // Create a simple tree structure
        let mut leaf1 = LeafNode::<i32, i32>::alloc();
        let mut leaf2 = LeafNode::<i32, i32>::alloc();

        for i in 0..leaf_cap {
            leaf1.insert_no_split(i as i32, i as i32 * 10);
            leaf2.insert_no_split((leaf_cap + i) as i32, (leaf_cap + i) as i32 * 10);
        }

        (*leaf1.brothers()).next = leaf2.get_ptr();
        (*leaf2.brothers()).prev = leaf1.get_ptr();

        let mut root = InterNode::<i32, i32>::alloc(1);
        root.set_left_ptr(leaf1.get_ptr());
        let leaf2_first_key = leaf2.get_keys()[0];
        root.insert_no_split(leaf2_first_key, leaf2.get_ptr());

        let mut map = BTreeMap::<i32, i32> {
            root: Some(Node::Inter(root)),
            len: (2 * leaf_cap) as usize,
            cache: UnsafeCell::new(PathCache::new()),
        };

        // Perform operations that should use cache
        let _ = map.get(&(leaf_cap as i32 / 2));

        // Test entry which populates cache
        let _entry = map.entry(leaf_cap as i32 + 5);
        // TODO test entry moving

        // Cleanup
        drop(map);
    }
}
