use super::*;

#[test]
fn test_avl_drain() {
    let mut tree = new_inttree();
    for i in 0..100 {
        tree.add_int_node(new_intnode(i));
    }
    assert_eq!(tree.get_count(), 100);

    let mut count = 0;
    for node in tree.drain() {
        assert!(node.value >= 0 && node.value < 100);
        count += 1;
    }
    assert_eq!(count, 100);
    assert_eq!(tree.get_count(), 0);
    assert!(tree.first().is_none());
}
