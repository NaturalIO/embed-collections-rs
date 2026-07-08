use super::super::*;
use super::*;
use fastrand::Rng;
use pointers::SmartPointer;
use rstest::*;
use std::boxed::Box;
use std::println;
use std::sync::Arc;
use std::time::Instant;

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_node<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        assert_eq!(tree.len(), 0);
        assert!(tree.first().is_none());
        assert!(tree.last().is_none());

        let node1 = tree.new_node(1);
        let node2 = tree.new_node(2);
        let node3 = tree.new_node(3);

        let p1 = &*node1 as *const IntAvlNode;
        let p2 = &*node2 as *const IntAvlNode;
        let p3 = &*node3 as *const IntAvlNode;

        tree.set_child2(node1.get_node(), AvlDirection::Left, p2, p1);
        tree.set_child2(node2.get_node(), AvlDirection::Right, p3, p2);

        assert_eq!(tree.parent_direction2(p2), AvlDirection::Left);
        // This is tricky as node1 is not in a tree, its parent is not set.
        // assert_eq!(tree.parent_direction2(p1), AvlDirection::Left);
        assert_eq!(tree.parent_direction2(p3), AvlDirection::Right);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_basic<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        let temp_node = tree.new_node(0);
        assert!(tree.find(&0).get_node_ref().is_none());
        drop(temp_node);

        tree.add_int_node(tree.new_node(0));
        let result = tree.find_int(0);
        assert!(result.get_node_ref().is_some());
        assert_eq!(tree.nearest(&result, AvlDirection::Left).is_exact(), false);
        assert_eq!(tree.nearest(&result, AvlDirection::Right).is_exact(), false);

        let rs = tree.find_larger_eq(&0).get_node_ref();
        assert!(rs.is_some());
        let found_value = rs.unwrap().value;
        assert_eq!(found_value, 0);

        let rs = tree.find_larger_eq(&2).get_node_ref();
        assert!(rs.is_none());

        let result = tree.find_int(1);
        let left = tree.nearest(&result, AvlDirection::Left);
        assert_eq!(left.is_exact(), true);
        assert_eq!(left.get_nearest().unwrap().value, 0);
        assert_eq!(tree.nearest(&result, AvlDirection::Right).is_exact(), false);

        tree.add_int_node(tree.new_node(2));
        let rs = tree.find_larger_eq(&1).get_node_ref();
        assert!(rs.is_some());
        let found_value = rs.unwrap().value;
        assert_eq!(found_value, 2);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_order<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    let max;
    #[cfg(miri)]
    {
        max = 2000;
    }
    #[cfg(not(miri))]
    {
        max = 200000;
    }

    reset_alive_count();
    {
        assert!(tree.first().is_none());
        let start_ts = Instant::now();
        for i in 0..max {
            tree.add_int_node(tree.new_node(i));
        }
        tree.validate_tree();
        assert_eq!(tree.len(), max as usize);

        let mut count = 0;
        let mut current = tree.first();
        let last = tree.last();
        while let Some(c) = current {
            assert_eq!(c.value, count);
            count += 1;
            if c as *const _ == last.map(|n| n as *const _).unwrap_or(null()) {
                current = None;
            } else {
                current = tree.next(c);
            }
        }
        assert_eq!(count, max);

        {
            let rs = tree.find_larger_eq(&5).get_node_ref();
            assert!(rs.is_some());
            let found_value = rs.unwrap().value;
            println!("found larger_eq {}", found_value);
            assert!(found_value >= 5);
            tree.remove_int(5);
            let rs = tree.find_larger_eq(&5).get_node_ref();
            assert!(rs.is_some());
            assert!(rs.unwrap().value >= 6);
            tree.add_int_node(tree.new_node(5));
        }

        for i in 0..max {
            assert!(tree.remove_int(i));
        }
        assert_eq!(tree.len(), 0);

        let end_ts = Instant::now();
        println!("duration {}", end_ts.duration_since(start_ts).as_secs_f64());
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_fixed1<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        let arr = [4719789032060327248, 7936680652950253153, 5197008094511783121];
        for i in arr.iter() {
            let node = tree.new_node(*i);
            tree.add_int_node(node);
            let rs = tree.find_int(*i);
            assert!(rs.get_node_ref().is_some(), "add error {}", i);
        }
        assert_eq!(tree.len(), arr.len());
        for i in arr.iter() {
            assert!(tree.remove_int(*i));
        }
        assert_eq!(tree.len(), 0);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_fixed2<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        tree.validate_tree();
        let node1 = tree.new_node(536872960);
        {
            tree.add_int_node(node1);
            tree.validate_tree();
            tree.remove_int(536872960);
            tree.validate_tree();
            tree.add_int_node(tree.new_node(536872960));
            tree.validate_tree();
        }

        assert!(tree.find_int(536872960).get_node_ref().is_some());
        let node2 = tree.new_node(12288);
        tree.add_int_node(node2);
        tree.validate_tree();
        tree.remove_int(536872960);
        tree.validate_tree();
        tree.add_int_node(tree.new_node(536872960));
        tree.validate_tree();
        let node3 = tree.new_node(22528);
        tree.add_int_node(node3);
        tree.validate_tree();
        tree.remove_int(12288);
        assert!(tree.find_int(12288).get_node_ref().is_none());
        tree.validate_tree();
        tree.remove_int(22528);
        assert!(tree.find_int(22528).get_node_ref().is_none());
        tree.validate_tree();
        tree.add_int_node(tree.new_node(22528));
        tree.validate_tree();
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_random<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        let count = 1000;
        let mut test_list: Vec<i64> = Vec::with_capacity(count);
        let mut rng = Rng::new();
        tree.validate_tree();
        for _ in 0..count {
            let node_value: i64 = rng.i64(..);
            if !test_list.contains(&node_value) {
                test_list.push(node_value);
                assert!(tree.add_int_node(tree.new_node(node_value)))
            }
        }
        tree.validate_tree();
        test_list.sort();
        for index in 0..test_list.len() {
            let node_ptr = tree.find_int(test_list[index]).get_node_ref().unwrap();
            let prev = tree.prev(node_ptr);
            let next = tree.next(node_ptr);
            if index == 0 {
                // first node
                assert!(prev.is_none());
                assert!(next.is_some());
                assert_eq!(next.unwrap().value, test_list[index + 1]);
            } else if index == test_list.len() - 1 {
                // last node
                assert!(prev.is_some());
                assert_eq!(prev.unwrap().value, test_list[index - 1]);
                assert!(next.is_none());
            } else {
                // middle node
                assert!(prev.is_some());
                assert_eq!(prev.unwrap().value, test_list[index - 1]);
                assert!(next.is_some());
                assert_eq!(next.unwrap().value, test_list[index + 1]);
            }
        }
        for index in 0..test_list.len() {
            assert!(tree.remove_int(test_list[index]));
        }
        tree.validate_tree();
        assert_eq!(0, tree.len());
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_insert_here<P>(#[case] mut tree: IntAvlTree<P>)
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode>,
{
    reset_alive_count();
    {
        let node1 = tree.new_node(10);
        tree.add_int_node(node1);
        // Insert 5 before 10
        let rs = tree.find_int(10);
        let here = unsafe { rs.detach() };
        let node = tree.new_node(5);
        unsafe { tree.insert_here(node, here, AvlDirection::Left) };
        tree.validate_tree();
        assert_eq!(tree.len(), 2);
        assert_eq!(tree.find_int(5).get_node_ref().unwrap().value, 5);

        // Insert 15 after 10
        let rs = tree.find_int(10);
        let here = unsafe { rs.detach() };
        let node = tree.new_node(15);
        unsafe { tree.insert_here(node, here, AvlDirection::Right) };
        tree.validate_tree();
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.find_int(15).get_node_ref().unwrap().value, 15);

        // Insert 3 before 5 (which is left child of 10)
        let rs = tree.find_int(5);
        let here = unsafe { rs.detach() };
        let node = tree.new_node(3);
        unsafe { tree.insert_here(node, here, AvlDirection::Left) };
        tree.validate_tree();
        assert_eq!(tree.len(), 4);

        // Insert 7 after 5
        let rs = tree.find_int(5);
        let here = unsafe { rs.detach() };
        let node = tree.new_node(7);
        unsafe { tree.insert_here(node, here, AvlDirection::Right) };
        tree.validate_tree();
        assert_eq!(tree.len(), 5);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
fn int_arc_avl_tree_get_exact() {
    reset_alive_count();
    {
        let mut tree = IntAvlTree::<Arc<IntAvlNode>>::new();
        let node = tree.new_node(100);
        // Manually constructing Arc node
        tree.add(node.clone());

        // find returns AvlSearchResult<'a, Arc<IntAvlNode>>
        let result_search = tree.find(&100);

        // This should invoke the specialized get_exact for Arc<T>
        let exact = result_search.get_exact();
        assert!(exact.is_some());
        let exact_arc = exact.unwrap();
        assert_eq!(exact_arc.value, 100);
        assert!(Arc::ptr_eq(&node, &exact_arc));
        // Check ref count: 1 (original) + 1 (in tree) + 1 (exact_arc) = 3
        assert_eq!(Arc::strong_count(&node), 3);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
fn test_arc_avl_tree_remove_ref() {
    reset_alive_count();
    {
        let mut tree = IntAvlTree::<Arc<IntAvlNode>>::new();
        let node = tree.new_node(200);
        tree.add(node.clone());
        assert_eq!(tree.len(), 1);
        assert_eq!(Arc::strong_count(&node), 2);

        tree.remove_ref(&node);
        assert_eq!(tree.len(), 0);
        assert_eq!(Arc::strong_count(&node), 1);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[rstest]
fn test_arc_avl_tree_remove_by_key() {
    reset_alive_count();
    {
        let mut tree = IntAvlTree::<Arc<IntAvlNode>>::new();
        let node = tree.new_node(300);
        tree.add(node.clone());

        let removed = tree.remove_by_key(&300);
        assert!(removed.is_some());
        let removed_arc = removed.unwrap();
        assert_eq!(removed_arc.value, 300);
        assert_eq!(tree.len(), 0);
        // count: 1 (node) + 1 (removed_arc) = 2. Tree dropped its count.
        assert_eq!(Arc::strong_count(&node), 2);

        drop(removed_arc);
        assert_eq!(Arc::strong_count(&node), 1);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}
