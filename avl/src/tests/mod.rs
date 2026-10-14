mod basic;
mod iter;
//mod range_tree;
pub use embed_collections_test::*;

use super::*;
use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use pointers::{Pointer, SmartPointer};
use std::println;

#[derive(format_attr::DebugAttr)]
#[fmt("IntAvlNode {value} {node:#?}")]
pub struct IntAvlNode {
    pub value: i64,
    pub node: UnsafeCell<AvlNode<Self, ()>>,
}

impl IntAvlNode {
    pub fn new(value: i64) -> Self {
        inc_alive_count();
        Self { value, node: UnsafeCell::new(AvlNode::default()) }
    }
}

impl Drop for IntAvlNode {
    fn drop(&mut self) {
        dec_alive_count();
    }
}

impl Borrow<i64> for IntAvlNode {
    fn borrow(&self) -> &i64 {
        &self.value
    }
}

unsafe impl AvlItem<()> for IntAvlNode {
    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }
}

impl_ord_with_borrow!(IntAvlNode, i64);

#[derive(Debug)]
pub struct IntAvlTree<P: Pointer<Target = IntAvlNode>>(AvlTree<P, ()>);

impl<P> IntAvlTree<P>
where
    P: Pointer<Target = IntAvlNode>,
{
    pub fn new() -> Self {
        Self(AvlTree::<P, ()>::new())
    }

    pub fn remove_int(&mut self, i: i64) -> bool {
        if let Some(_node) = self.0.remove_by_key(&i) {
            // node is Box<IntAvlNode>, dropped automatically
            return true;
        }
        // else
        println!("not found {}", i);
        false
    }

    pub fn add_int_node(&mut self, node: P)
    where
        P: core::fmt::Debug,
    {
        self.0.add(node).expect("added");
    }

    pub fn validate_tree(&self) {
        self.0.validate();
    }
}

impl<P> Deref for IntAvlTree<P>
where
    P: Pointer<Target = IntAvlNode>,
{
    type Target = AvlTree<P, ()>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<P> DerefMut for IntAvlTree<P>
where
    P: Pointer<Target = IntAvlNode>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<P> IntAvlTree<P>
where
    P: SmartPointer<Target = IntAvlNode>,
{
    pub fn new_node(i: i64) -> P {
        P::new(IntAvlNode::new(i))
    }
}
