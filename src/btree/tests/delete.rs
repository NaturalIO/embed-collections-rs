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
