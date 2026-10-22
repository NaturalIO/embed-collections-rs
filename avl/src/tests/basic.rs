use super::super::*;
use super::*;
use captains_log::logfn;
use fastrand::Rng;
use pointers::SmartPointer;
use rstest::*;
use std::boxed::Box;
use std::fmt::Debug;
use std::println;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;
use std::vec;

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_node<P>(#[case] tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    {
        assert_eq!(tree.len(), 0);
        assert!(tree.first().is_none());
        assert!(tree.last().is_none());
        let _new_node = IntAvlTree::<P>::new_node;

        let node1 = _new_node(1);
        let node2 = _new_node(2);
        let node3 = _new_node(3);

        let p1 = &*node1 as *const IntAvlNode as *mut IntAvlNode;
        let p2 = &*node2 as *const IntAvlNode as *mut IntAvlNode;
        let p3 = &*node3 as *const IntAvlNode as *mut IntAvlNode;

        node1.get_node().set_child2::<P>(DIR_LEFT, p2, p1);
        node2.get_node().set_child2::<P>(DIR_RIGHT, p3, p2);

        assert_eq!(AvlNode::<IntAvlNode, ()>::parent_direction(p2), DIR_LEFT);
        // This is tricky as node1 is not in a tree, its parent is not set.
        // assert_eq!(tree.parent_direction2(p1), DIR_LEFT);
        assert_eq!(AvlNode::<IntAvlNode, ()>::parent_direction(p3), DIR_RIGHT);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_basic<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    {
        let _new_node = IntAvlTree::<P>::new_node;
        assert!(tree.get(&0).is_none());

        tree.add_int_node(_new_node(0));
        tree.validate_tree();
        assert_eq!(tree.entry(0).unwrap_occupied().value, 0);
        let res = tree.get(&0);
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, 0);

        assert!(tree.get(&2).is_none());

        let ent = tree.entry(1).unwrap_vacant();
        assert_eq!(ent.nearest().unwrap().value, 0);
        assert_eq!(ent.peek_prev().unwrap().value, 0);
        assert!(ent.peek_next().is_none());

        tree.add_int_node(_new_node(2));
        tree.validate_tree();
        let ent = tree.entry(1).unwrap_vacant();
        assert_eq!(ent.peek_prev().unwrap().value, 0);
        assert_eq!(ent.peek_next().unwrap().value, 2);
        assert_eq!(ent.nearest().unwrap().value, 2);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_order<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
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
    let _new_node = IntAvlTree::<P>::new_node;

    reset_alive_count();
    {
        assert!(tree.first().is_none());
        let start_ts = Instant::now();
        for i in 0..max {
            tree.add_int_node(_new_node(i));
        }
        tree.validate_tree();
        assert_eq!(tree.len(), max as usize);
        assert_eq!(tree.first().unwrap().value, 0);
        assert_eq!(tree.last().unwrap().value, max - 1);

        let mut count = 0;
        let mut iter = tree.iter();
        while let Some(c) = iter.next() {
            assert_eq!(c.value, count);
            count += 1;
        }
        assert_eq!(count, max);

        {
            assert_eq!(tree.get(&5).unwrap().value, 5);
            tree.remove_int(5);
            let ent = tree.entry(5).unwrap_vacant();
            assert_eq!(ent.peek_next().unwrap().value, 6);
            tree.validate_tree();
            tree.add_int_node(_new_node(5));
        }

        let mut count = max;
        let mut iter = tree.iter_rev();
        while let Some(c) = iter.next() {
            assert_eq!(c.value, count - 1);
            count -= 1;
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

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_fixed1<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    let _new_node = IntAvlTree::<P>::new_node;
    {
        let arr = [4719789032060327248, 7936680652950253153, 5197008094511783121];
        for i in arr.iter() {
            tree.add_int_node(_new_node(*i));
            tree.validate_tree();
            assert_eq!(tree.get(i).unwrap().value, *i);
        }
        assert_eq!(tree.len(), arr.len());
        for i in arr.iter() {
            assert!(tree.remove_int(*i));
            tree.validate_tree();
        }
        assert_eq!(tree.len(), 0);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_fixed2<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    let _new_node = IntAvlTree::<P>::new_node;
    {
        tree.validate_tree();
        {
            tree.add_int_node(_new_node(536872960));
            tree.validate_tree();
            tree.remove_int(536872960);
            tree.validate_tree();
            tree.add_int_node(_new_node(536872960));
            tree.validate_tree();
        }

        assert!(tree.get(&536872960).is_some());
        tree.add_int_node(_new_node(12288));
        tree.validate_tree();
        tree.remove_int(536872960);
        tree.validate_tree();
        tree.add_int_node(_new_node(536872960));
        tree.validate_tree();
        tree.add_int_node(_new_node(22528));
        tree.validate_tree();
        tree.remove_int(12288);
        assert!(tree.get(&12288).is_none());
        tree.validate_tree();
        tree.remove_int(22528);
        assert!(tree.get(&22528).is_none());
        tree.validate_tree();
        tree.add_int_node(_new_node(22528));
        tree.validate_tree();
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
fn int_avl_tree_fixed3<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    // test will cover all branch of remove
    let test_data: Vec<i64> = vec![
        6701132600390042969,
        16037547747698279,
        6968470155198969672,
        3994714700825908325,
        -3562517043415005434,
        -3045537343578687951,
        2524319250247492254,
        1978356101225525588,
        5421964435552326859,
        8357131494956206805,
    ];
    let _new_node = IntAvlTree::<P>::new_node;
    {
        tree.validate_tree();
        for i in &test_data {
            crate::trace_log!("insert {i}");
            tree.add_int_node(_new_node(*i));
            tree.validate_tree();
        }
        for i in &test_data {
            crate::trace_log!("remove {i}");
            tree.remove_int(*i);
            tree.validate_tree();
        }
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_random<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    let _new_node = IntAvlTree::<P>::new_node;
    {
        let count = {
            #[cfg(miri)]
            {
                1000
            }
            #[cfg(not(miri))]
            {
                10000
            }
        };
        let mut test_data: Vec<i64> = Vec::with_capacity(count);
        let mut rng = Rng::new();
        tree.validate_tree();
        // random add
        for _ in 0..count {
            let node_value: i64 = rng.i64(..);
            if !test_data.contains(&node_value) {
                test_data.push(node_value);
                crate::trace_log!("insert {node_value}");
                tree.add_int_node(_new_node(node_value));
            }
        }
        tree.validate_tree();
        let mut ordered = test_data.clone();
        ordered.sort();
        // test order
        for index in 0..ordered.len() {
            let node_ref = tree.get(&ordered[index]).unwrap();
            let prev = tree.prev(&node_ref);
            let next = tree.next(&node_ref);
            if index == 0 {
                // first node
                assert!(prev.is_none());
                assert!(next.is_some());
                assert_eq!(next.unwrap().value, ordered[index + 1]);
            } else if index == ordered.len() - 1 {
                // last node
                assert!(prev.is_some());
                assert_eq!(prev.unwrap().value, ordered[index - 1]);
                assert!(next.is_none());
            } else {
                // middle node
                assert!(prev.is_some());
                assert_eq!(prev.unwrap().value, ordered[index - 1]);
                assert!(next.is_some());
                assert_eq!(next.unwrap().value, ordered[index + 1]);
            }
        }
        // random remove
        for index in 0..test_data.len() {
            let key = &test_data[index];
            crate::trace_log!("remove {key:?}");
            assert!(tree.remove_int(*key));
            tree.validate_tree();
        }
        tree.validate_tree();
        assert_eq!(0, tree.len());
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_entry_insert_adjacent<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    {
        let _new_node = IntAvlTree::<P>::new_node;
        let node1 = _new_node(10);
        tree.add_int_node(node1);

        // Insert 5 before 10
        let mut ent = tree.entry(10).unwrap_occupied();
        let node = _new_node(5);
        // left is null
        unsafe { ent.insert_prev_unchecked(node) };
        // ent is not moved
        assert_eq!(ent.value, 10);
        tree.validate_tree();

        assert_eq!(tree.len(), 2);
        assert_eq!(tree.get(&5).unwrap().value, 5);

        // Insert 15 after 10
        let ent = tree.entry(10).unwrap_occupied();
        let node = _new_node(15);
        assert_eq!(unsafe { ent.insert_move_next_unchecked(node) }.get().value, 15);
        tree.validate_tree();
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.get(&15).unwrap().value, 15);

        // Insert 3 before 5 (which is left child of 10)
        let ent = tree.entry(5).unwrap_occupied();
        let node = _new_node(3);
        assert_eq!(unsafe { ent.insert_move_prev_unchecked(node) }.value, 3);
        tree.validate_tree();
        assert_eq!(tree.len(), 4);

        // Insert 7 after 5
        let ent = tree.entry(5).unwrap_occupied();
        let node = _new_node(7);
        assert_eq!(unsafe { ent.insert_move_next_unchecked(node) }.value, 7);
        tree.validate_tree();
        assert_eq!(tree.len(), 5);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_entry_cursor_mut_forward<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    let _new_node = IntAvlTree::<P>::new_node;
    {
        let n: usize = 1000;
        let mut ent = tree.last_entry();
        for i in 0..n {
            ent = unsafe { ent.append_unchecked(_new_node((i as i64) * 2)) };
        }
        assert_eq!(tree.len(), n);
        assert_eq!(alive_count(), n);
        let mut ent = tree.first_entry().unwrap_occupied();
        let mut i: usize = 0;
        loop {
            ent = unsafe { ent.insert_move_next_unchecked(_new_node(i as i64 + 1)) };
            i += 2;
            if let Some(_ent) = ent.move_next() {
                ent = _ent;
            } else {
                break;
            }
        }
        assert_eq!(i, n * 2);
        assert_eq!(tree.len(), n * 2);
        tree.validate_tree();

        for i in 0..n {
            let m = (i as i64) * 2;
            assert_eq!(tree.get(&m).unwrap().value, m);
            assert_eq!(tree.get(&(m + 1)).unwrap().value, m + 1);
        }

        let mut i: usize = 0;
        let mut ent = tree.first_entry().unwrap_occupied();
        loop {
            ent.remove_next();
            i += 1;
            if let Some(_ent) = ent.move_next() {
                ent = _ent;
            } else {
                break;
            }
        }
        for i in 0..n {
            let m = (i as i64) * 2;
            assert_eq!(tree.get(&(m)).unwrap().value, m);
        }

        assert_eq!(tree.len(), n);
        assert_eq!(i, n);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}

#[logfn]
#[rstest]
#[case(IntAvlTree::<Box<IntAvlNode>>::new())]
#[case(IntAvlTree::<Arc<IntAvlNode>>::new())]
#[case(IntAvlTree::<Rc<IntAvlNode>>::new())]
fn int_avl_tree_entry_cursor_mut_backward<P>(#[case] mut tree: IntAvlTree<P>, setup_log: ())
where
    P: SmartPointer<Target = IntAvlNode> + Deref<Target = IntAvlNode> + Debug,
{
    reset_alive_count();
    let _new_node = IntAvlTree::<P>::new_node;
    {
        let n: usize = 1000;
        let mut ent = tree.first_entry();
        for i in 1..=n {
            ent = unsafe { ent.prepend_unchecked(_new_node(((n - i) as i64) * 2)) };
        }
        assert_eq!(tree.len(), n);
        assert_eq!(alive_count(), n);
        let mut ent = tree.last_entry().unwrap_occupied();
        let mut i: usize = n - 1;
        loop {
            unsafe { ent.insert_next_unchecked(_new_node((i * 2) as i64 + 1)) };
            if let Some(_ent) = ent.move_prev() {
                ent = _ent;
                i -= 1;
            } else {
                break;
            }
        }
        assert_eq!(i, 0);
        assert_eq!(tree.len(), n * 2);
        tree.validate_tree();

        for i in 0..n {
            let m = (i as i64) * 2;
            assert_eq!(tree.get(&m).unwrap().value, m);
            assert_eq!(tree.get(&(m + 1)).unwrap().value, m + 1);
        }

        let mut i: usize = 0;
        let mut ent = tree.last_entry().unwrap_occupied();
        loop {
            ent.remove_prev();
            i += 1;
            if let Some(_ent) = ent.move_prev() {
                ent = _ent;
            } else {
                break;
            }
        }
        tree.validate_tree();

        for i in 0..n {
            let m = (i as i64) * 2;
            assert_eq!(tree.get(&(m + 1)).unwrap().value, m + 1);
        }
        assert_eq!(tree.first().unwrap().value, 1i64);
        assert_eq!(tree.last().unwrap().value, ((n - 1) * 2 + 1) as i64);
        assert_eq!(tree.len(), n);
        assert_eq!(i, n);
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}
