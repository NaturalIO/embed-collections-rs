use super::*;
use rstest::*;

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_arc_drain<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    for i in 0..100 {
        tree.add_int_node(tree.new_node(i));
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

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_arc_iter<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    for i in 0..100 {
        tree.add_int_node(tree.new_node(i));
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

/*
#[test]
fn test_avl_prev_and_next() {
    let mut tree = new_inttree();
    for i in 0..100 {
        tree.add_int_node(tree.new_node(i));
    }
}
*/
