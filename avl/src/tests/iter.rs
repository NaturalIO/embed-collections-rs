use super::*;
use rstest::*;
use std::boxed::Box;
use std::sync::Arc;

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_drain<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
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
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_iter<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
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
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

/// Test AvlIter::next_ref() with Arc by cloning each node during iteration.
/// Verifies that reference counting works correctly and all references are properly cleaned up.
#[rstest]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_next_ref_clone_arc<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Clone,
{
    reset_alive_count();
    {
        let n = 50;
        for i in 0..n {
            tree.add_int_node(tree.new_node(i as i64));
        }
        assert_eq!(tree.len(), n);
        // Each node created once
        assert_eq!(alive_count(), n);

        // Iterate using next_ref() and clone each Arc during iteration
        let mut cloned_nodes: Vec<P> = Vec::with_capacity(n);
        let mut iter = tree.iter();
        while let Some(arc) = iter.next_ref() {
            cloned_nodes.push(arc.clone());
        }
        for (i, node) in cloned_nodes.iter().enumerate() {
            assert_eq!(node.value as usize, i);
        }

        // After cloning, we have tree refs + cloned refs
        assert_eq!(alive_count(), n);

        // Verify all cloned values are correct
        for (i, arc) in cloned_nodes.iter().enumerate() {
            assert_eq!(arc.value as usize, i);
        }
        // Drop all cloned references
        drop(cloned_nodes);
        // Only tree refs remain
        assert_eq!(alive_count(), n);

        // Validate tree structure is intact
        tree.validate_tree();

        // Drop the tree
        drop(tree);
    }
    // All nodes dropped, alive count should be 0
    assert_eq!(alive_count(), 0);
}

/// Test AvlIter::next_ref() reverse iteration with Arc cloning.
#[rstest]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn test_next_ref_clone_rev<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Clone,
{
    reset_alive_count();
    {
        let n = 30;
        for i in 0..n {
            tree.add_int_node(tree.new_node(i as i64));
        }
        assert_eq!(tree.len(), n);
        assert_eq!(alive_count(), n);

        let mut cloned_nodes: Vec<P> = Vec::with_capacity(n);
        let mut iter = tree.iter_rev();
        while let Some(arc) = iter.next_ref() {
            cloned_nodes.push(arc.clone());
        }

        // Reverse order: last element first
        for (i, arc) in cloned_nodes.iter().enumerate() {
            assert_eq!(arc.value as usize, n - 1 - i);
        }

        drop(cloned_nodes);
        assert_eq!(alive_count(), n);

        drop(tree);
    }
    assert_eq!(alive_count(), 0);
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
