use core::cell::UnsafeCell;
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use embed_collections::avl::{AvlItem, AvlNode, AvlTree};
use rand::seq::SliceRandom;
use rand::{Rng, thread_rng};
use std::fmt;

// The same test setup from src/avl.rs
struct IntAvlNode {
    pub value: i64,
    pub node: UnsafeCell<AvlNode<Self, ()>>,
}
unsafe impl Send for IntAvlNode {}
impl fmt::Debug for IntAvlNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {:#?}", self.value, self.node)
    }
}
unsafe impl AvlItem<()> for IntAvlNode {
    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }
}
fn new_intnode(i: i64) -> Box<IntAvlNode> {
    Box::new(IntAvlNode { node: UnsafeCell::new(AvlNode::default()), value: i })
}
type IntAvlTree = AvlTree<Box<IntAvlNode>, ()>;
fn new_inttree() -> IntAvlTree {
    AvlTree::<Box<IntAvlNode>, ()>::new()
}
fn cmp_int_node(a: &IntAvlNode, b: &IntAvlNode) -> std::cmp::Ordering {
    a.value.cmp(&b.value)
}

fn cmp_int(a: &i64, b: &IntAvlNode) -> std::cmp::Ordering {
    a.cmp(&b.value)
}

fn bench_avl_insert(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<i64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    c.bench_function("avl_insert_10000", |b| {
        b.iter(|| {
            let mut tree = new_inttree();
            for &value in &values {
                tree.add(black_box(new_intnode(value)), cmp_int_node);
            }
        })
    });
}

fn bench_avl_search(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<i64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = new_inttree();
    for &value in &values {
        tree.add(new_intnode(value), cmp_int_node);
    }

    values.shuffle(&mut rng);

    c.bench_function("avl_search_10000", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.find(&value, cmp_int));
            }
        })
    });
}

criterion_group!(benches, bench_avl_insert, bench_avl_search);
criterion_main!(benches);
