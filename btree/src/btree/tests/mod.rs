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
pub(super) use crate::compact::Compact;
pub(super) use crate::large::TreeInfo;
pub(super) use embed_collections_test::*;

pub struct TreeBuilder<K: Key, V: Value, S: Stats> {
    leaf_count: usize,
    inter_count: u32,
    stats: S,
    len: usize,
    prev: Option<LeafNode<K, V>>,
}

impl<K: Key, V: Value, S: Stats> Default for TreeBuilder<K, V, S> {
    fn default() -> Self {
        Self { leaf_count: 0, inter_count: 0, len: 0, prev: None, stats: S::default() }
    }
}

impl<K: Key, V: Value, S: Stats> TreeBuilder<K, V, S> {
    pub fn leaf_cap(&self) -> u8 {
        LeafNode::<K, V>::cap()
    }

    pub fn inter_cap(&self) -> u8 {
        InterNode::<K>::cap()
    }

    pub fn new_inter(&mut self, height: u8) -> InterNode<K> {
        self.inter_count += 1;
        unsafe { InterNode::alloc(height) }
    }

    // XXX this helper only support building height > 1 tree
    pub fn new_root(
        &mut self, height: u8, promote_key: K, left_ptr: *mut NodeHeader,
        right_ptr: *mut NodeHeader,
    ) -> InterNode<K> {
        let mut root = self.new_inter(height);
        root.set_left_ptr(left_ptr);
        root.insert_no_split_with_idx(0, promote_key, right_ptr);
        root
    }

    pub fn new_leaf(&mut self) -> LeafNode<K, V> {
        self.leaf_count += 1;
        unsafe {
            let mut new_leaf = LeafNode::alloc();
            if let Some(prev) = self.prev.as_mut() {
                (*prev.brothers()).next = new_leaf.get_ptr_mut();
                (*new_leaf.brothers()).prev = prev.get_ptr_mut();
            }
            self.prev.replace(new_leaf.clone());
            new_leaf
        }
    }

    pub fn insert_leaf(&mut self, leaf: &mut LeafNode<K, V>, key: K, value: V) {
        self.len += 1;
        leaf.insert_no_split(key, value);
    }

    pub fn build(mut self, root: Node<K, V>) -> BTree<K, V, S> {
        self.stats.init_count(self.leaf_count, self.inter_count);
        BTree {
            inner: BTreeInner {
                len: self.len,
                root: Some(root.to_root_ptr()),
                _phan: Default::default(),
                #[cfg(feature = "trace_log")]
                triggers: 0,
            },
            stats: self.stats,
        }
    }
}
