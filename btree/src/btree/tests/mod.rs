extern crate std;

mod api;
mod delete;
mod entry_move;
mod inter;
mod inter_borrow;
mod inter_underflow;
mod iter;
mod leaf;
mod leaf_borrow;
mod leaf_delete;
mod split;

use super::{helper::*, inter::*, leaf::*, node::*, *};
use test_common::*;

pub struct TreeBuilder<K: Ord + Clone + Sized, V: Sized> {
    leaf_count: usize,
    inter_count: u32,
    len: usize,
    prev: Option<LeafNode<K, V>>,
}

impl<K: Ord + Sized + Clone, V: Sized> Default for TreeBuilder<K, V> {
    fn default() -> Self {
        Self { leaf_count: 0, inter_count: 0, len: 0, prev: None }
    }
}

impl<K: Ord + Sized + Clone, V: Sized> TreeBuilder<K, V> {
    pub fn leaf_cap(&self) -> u32 {
        LeafNode::<K, V>::cap()
    }

    pub fn inter_cap(&self) -> u32 {
        InterNode::<K, V>::cap()
    }

    pub fn new_inter(&mut self, height: u32) -> InterNode<K, V> {
        self.inter_count += 1;
        unsafe { InterNode::alloc(height) }
    }

    pub fn new_root(
        &mut self, height: u32, promote_key: K, left_ptr: *mut NodeHeader,
        right_ptr: *mut NodeHeader,
    ) -> InterNode<K, V> {
        let mut root = self.new_inter(height);
        root.set_left_ptr(left_ptr);
        root.insert_no_split_with_idx(0, promote_key, right_ptr);
        root
    }

    pub fn new_leaf(&mut self) -> LeafNode<K, V> {
        self.leaf_count += 1;
        unsafe {
            let new_leaf = LeafNode::alloc();
            if let Some(prev) = self.prev.as_ref() {
                (*prev.brothers()).next = new_leaf.get_ptr();
                (*new_leaf.brothers()).prev = prev.get_ptr();
            }
            self.prev.replace(new_leaf.clone());
            new_leaf
        }
    }

    pub fn insert_leaf(&mut self, leaf: &mut LeafNode<K, V>, key: K, value: V) {
        self.len += 1;
        leaf.insert_no_split(key, value);
    }

    pub fn build(self, root: Node<K, V>) -> BTreeMap<K, V> {
        let cache = if self.inter_count > 0 {
            Some(TreeInfo::new(self.leaf_count, self.inter_count))
        } else {
            None
        };
        BTreeMap {
            len: self.len,
            root: Some(root.to_root_ptr()),
            _info: UnsafeCell::new(cache),
            #[cfg(feature = "trace_log")]
            triggers: 0,
        }
    }
}
