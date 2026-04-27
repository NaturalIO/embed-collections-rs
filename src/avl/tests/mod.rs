mod basic;
mod iter;

use super::*;
use core::cell::UnsafeCell;
use fastrand::Rng;
use std::time::Instant;

pub struct IntAvlNode {
    pub value: i64,
    pub node: UnsafeCell<AvlNode<Self, ()>>,
}

impl fmt::Debug for IntAvlNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {:#?}", self.value, self.node)
    }
}

impl fmt::Display for IntAvlNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

unsafe impl AvlItem<()> for IntAvlNode {
    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }
}

pub type IntAvlTree = AvlTree<Box<IntAvlNode>, ()>;

pub fn new_intnode(i: i64) -> Box<IntAvlNode> {
    Box::new(IntAvlNode { node: UnsafeCell::new(AvlNode::default()), value: i })
}

pub fn new_inttree() -> IntAvlTree {
    AvlTree::<Box<IntAvlNode>, ()>::new()
}

pub fn cmp_int_node(a: &IntAvlNode, b: &IntAvlNode) -> Ordering {
    a.value.cmp(&b.value)
}

pub fn cmp_int(a: &i64, b: &IntAvlNode) -> Ordering {
    a.cmp(&b.value)
}

impl AvlTree<Box<IntAvlNode>, ()> {
    pub fn remove_int(&mut self, i: i64) -> bool {
        if let Some(_node) = self.remove_by_key(&i, cmp_int) {
            // node is Box<IntAvlNode>, dropped automatically
            return true;
        }
        // else
        println!("not found {}", i);
        false
    }

    pub fn add_int_node(&mut self, node: Box<IntAvlNode>) -> bool {
        self.add(node, cmp_int_node)
    }

    pub fn validate_tree(&self) {
        self.validate(cmp_int_node);
    }

    pub fn find_int<'a>(&'a self, i: i64) -> AvlSearchResult<'a, Box<IntAvlNode>> {
        self.find(&i, cmp_int)
    }

    pub fn find_node<'a>(&'a self, node: &'a IntAvlNode) -> AvlSearchResult<'a, Box<IntAvlNode>> {
        self.find(node, cmp_int_node)
    }
}
