use core::cell::UnsafeCell;
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_collections::avl::{AvlItem, AvlNode, AvlTree};
use rand::seq::SliceRandom;
use rand::{Rng, thread_rng};
use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

#[derive(Default)]
struct IntAvlNode {
    pub value: u64,
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

fn new_intnode_box(i: u64) -> Box<IntAvlNode> {
    Box::new(IntAvlNode { value: i, ..Default::default() })
}

fn new_intnode_arc(i: u64) -> Arc<IntAvlNode> {
    Arc::new(IntAvlNode { value: i, ..Default::default() })
}

type IntAvlTreeBox = AvlTree<Box<IntAvlNode>, ()>;
type IntAvlTreeArc = AvlTree<Arc<IntAvlNode>, ()>;

fn cmp_int_node(a: &IntAvlNode, b: &IntAvlNode) -> std::cmp::Ordering {
    a.value.cmp(&b.value)
}
fn cmp_int(a: &u64, b: &IntAvlNode) -> std::cmp::Ordering {
    a.cmp(&b.value)
}

fn bench_avl_insert_box(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("avl_insert");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("insert_10000_i64_box", |b| {
        b.iter(|| {
            let mut tree = IntAvlTreeBox::new();
            for &value in &values {
                tree.add(black_box(new_intnode_box(value)), cmp_int_node);
            }
        })
    });
    group.finish();
}

fn bench_avl_insert_arc(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("avl_insert");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("insert_10000_arc", |b| {
        b.iter(|| {
            let mut tree = IntAvlTreeArc::new();
            for &value in &values {
                tree.add(black_box(new_intnode_arc(value)), cmp_int_node);
            }
        })
    });
    group.finish();
}

fn bench_btreemap_box_insert(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("btreemap_box_insert");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("insert_10000_node", |b| {
        b.iter(|| {
            let mut tree = BTreeMap::new();
            for &value in &values {
                tree.insert(value, black_box(new_intnode_box(value)));
            }
        })
    });
    group.finish();
}

fn bench_avl_search_box(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = IntAvlTreeBox::new();
    for &value in &values {
        tree.add(new_intnode_box(value), cmp_int_node);
    }

    values.shuffle(&mut rng);

    let mut group = c.benchmark_group("avl_search");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("search_10000_i64_box", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.find(&value, cmp_int));
            }
        })
    });
    group.finish();
}

fn bench_avl_search_arc(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = IntAvlTreeArc::new();
    for &value in &values {
        tree.add(new_intnode_arc(value), cmp_int_node);
    }

    values.shuffle(&mut rng);

    let mut group = c.benchmark_group("avl_search");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("search_10000_i64_arc", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.find(&value, cmp_int));
            }
        })
    });
    group.finish();
}

fn bench_btreemap_box_search(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = BTreeMap::new();
    for &value in &values {
        tree.insert(value, new_intnode_box(value));
    }

    values.shuffle(&mut rng);

    let mut group = c.benchmark_group("btreemap_search_box");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("search_10000_node", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.get(&value));
            }
        })
    });
    group.finish();
}

fn bench_btreemap_u64_insert(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("btreemap_insert");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("insert_10000_u64_u64", |b| {
        b.iter(|| {
            let mut tree = BTreeMap::new();
            for &value in &values {
                tree.insert(value, black_box(value));
            }
        })
    });
    group.finish();
}

fn bench_btreemap_u64_search(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = BTreeMap::new();
    for &value in &values {
        tree.insert(value, value);
    }

    values.shuffle(&mut rng);

    let mut group = c.benchmark_group("btreemap_search");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("search_10000_u64_u64", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.get(&value));
            }
        })
    });
    group.finish();
}

fn bench_avl_drop(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<u64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("avl_drop");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("drop_10000", |b| {
        b.iter_with_setup(
            || {
                let mut tree = IntAvlTreeBox::new();
                for &value in &values {
                    tree.add(new_intnode_box(value), cmp_int_node);
                }
                tree
            },
            |tree| {
                black_box(tree);
            },
        )
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_avl_insert_box,
    bench_avl_insert_arc,
    bench_avl_search_box,
    bench_avl_search_arc,
    bench_btreemap_box_insert,
    bench_btreemap_box_search,
    bench_btreemap_u64_insert,
    bench_btreemap_u64_search,
    bench_avl_drop
);
criterion_main!(benches);
