use super::*;

#[test]
fn test_avl_drain() {
    let mut tree = new_inttree();
    for i in 0..100 {
        tree.add_int_node(new_intnode(i));
    }
    assert_eq!(tree.len(), 100);

    let mut count = 0;
    for node in tree.drain() {
        assert!(node.value >= 0 && node.value < 100);
        count += 1;
    }
    assert_eq!(count, 100);
    assert_eq!(tree.len(), 0);
    assert!(tree.first().is_none());
}

#[test]
fn test_avl_iter() {
    let mut tree = new_inttree();
    for i in 0..100 {
        tree.add_int_node(new_intnode(i));
    }
    assert_eq!(tree.len(), 100);

    let mut count = 0;
    for (i, node) in tree.iter().enumerate() {
        assert_eq!(node.value as usize, i);
        count += 1;
    }
    assert_eq!(count, 100);

    let mut count = 0;
    for (i, node) in tree.iter_rev().enumerate() {
        assert_eq!(node.value as usize, 100 - i - 1);
        count += 1;
    }
    assert_eq!(count, 100);
}
