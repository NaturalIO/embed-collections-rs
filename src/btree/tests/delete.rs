use super::super::{inter::*, leaf::*, node::*, *};
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
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
    // Fill node to capacity
    for i in 0..count {
        map.insert(i, i * 10);
        map.validate();
    }
    println!("height: {}", map.height(),);
    assert_eq!(height, map.height());
    // Delete most elements to trigger merge
    for i in 0..count {
        assert_eq!(map.remove(&i), Some(i * 10));
        map.validate();
    }
    assert_eq!(map.height(), 1);
}
