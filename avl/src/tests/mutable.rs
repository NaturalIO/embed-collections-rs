use super::super::*;
use super::*;
use captains_log::logfn;
use core::cell::UnsafeCell;
use rstest::*;
use std::println;

use std::cmp::Ordering as CmpOrdering;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

#[derive(format_attr::DebugAttr)]
#[fmt("MutNode {id} {} {:?}", self.value.load(Relaxed), self.get_node())]
#[repr(C)]
pub struct MutNode {
    pub node: UnsafeCell<AvlNode<()>>,
    pub id: usize,
    pub value: AtomicUsize,
}

impl MutNode {
    pub fn new(id: usize, value: usize) -> Arc<Self> {
        inc_alive_count();
        Arc::new(Self {
            id,
            value: AtomicUsize::new(value),
            node: UnsafeCell::new(AvlNode::default()),
        })
    }
}

impl Drop for MutNode {
    fn drop(&mut self) {
        dec_alive_count();
    }
}

unsafe impl AvlItem<()> for MutNode {
    fn get_node(&self) -> &mut AvlNode<()> {
        unsafe { &mut *self.node.get() }
    }
}

impl PartialOrd for MutNode {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(Ord::cmp(self, other))
    }
}

impl PartialEq for MutNode {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for MutNode {}

impl Ord for MutNode {
    #[inline]
    fn cmp(&self, other: &Self) -> CmpOrdering {
        let s_id = self.id;
        let o_id = other.id;
        // start means they are the same
        if s_id != o_id {
            let r = self.value.load(Relaxed).cmp(&other.value.load(Relaxed));
            if r != CmpOrdering::Equal {
                return r;
            }
            s_id.cmp(&o_id)
        } else {
            return CmpOrdering::Equal;
        }
    }
}

#[logfn]
#[rstest]
fn int_avl_tree_remove_add_fixed5() {
    reset_alive_count();
    let _new_node = MutNode::new;
    {
        let mut tree = AvlTree::<Arc<MutNode>, ()>::new();
        let node1 = _new_node(1, 262142);
        tree.add(node1.clone()).expect("add");
        let node0 = _new_node(0, 262137);
        tree.add(node0.clone()).expect("add");
        let node2 = _new_node(2, 262142);
        tree.add(node2.clone()).expect("add");
        let node3 = _new_node(3, 262136);
        tree.add(node3.clone()).expect("add");
        tree.validate();
        println!("---");
        tree.dump(|_node: &MutNode, _level: usize| {
            println!("[l{_level}] {:?}", _node);
        });
        node2.value.store(262136, Relaxed);
        node3.value.store(262134, Relaxed);
        println!("removing");
        tree.remove(&node2);
        tree.remove(&node3);
        println!("---");
        tree.dump(|_node: &MutNode, _level: usize| {
            println!("[l{_level}] {:?}", _node);
        });
        tree.validate();
        assert_eq!(tree.len(), 2);
        tree.add(node2).expect("add");
        tree.add(node3).expect("add");
        tree.validate();
        println!("---");
        tree.dump(|_node: &MutNode, _level: usize| {
            println!("[l{_level}] {:?}", _node);
        });
        drop(tree);
    }
    assert_eq!(alive_count(), 0);
}
