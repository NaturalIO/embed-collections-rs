//! Benchmark for embed_collections::AvlTree

mod btree_common;

use core::cell::UnsafeCell;
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_avl::{AvlItem, AvlNode, AvlTree};
use std::fmt;
use std::sync::Arc;

use btree_common::{SIZES, TestData, size_desc};

#[derive(Default)]
struct IntAvlNode {
    pub value: u32,
    pub node: UnsafeCell<AvlNode<Self, ()>>,
}

unsafe impl Send for IntAvlNode {}

impl fmt::Debug for IntAvlNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {:#?}", self.value, self.node)
    }
}

unsafe impl AvlItem<()> for IntAvlNode {
    type Key = u32;
    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }

    #[inline]
    fn borrow_key(&self) -> &u32 {
        &self.value
    }
}

fn new_intnode_box(i: u32) -> Box<IntAvlNode> {
    Box::new(IntAvlNode { value: i, ..Default::default() })
}

fn new_intnode_arc(i: u32) -> Arc<IntAvlNode> {
    Arc::new(IntAvlNode { value: i, ..Default::default() })
}

type IntAvlTreeBox = AvlTree<Box<IntAvlNode>, ()>;
type IntAvlTreeArc = AvlTree<Arc<IntAvlNode>, ()>;

fn bench_insert_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeBox::new();
                for i in 0..size {
                    tree.add(black_box(new_intnode_box(data.keys[i])));
                }
            });
        });
        group.finish();
    }
}

fn bench_insert_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_rand_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeArc::new();
                for i in 0..size {
                    tree.add(black_box(new_intnode_arc(data.keys[i])));
                }
            });
        });
        group.finish();
    }
}

fn bench_insert_sequential_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_seq_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeBox::new();
                for i in 0..size {
                    tree.add(black_box(new_intnode_box(data.keys[i])));
                }
            });
        });
        group.finish();
    }
}

fn bench_insert_sequential_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_seq_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeArc::new();
                for i in 0..size {
                    tree.add(black_box(new_intnode_arc(data.keys[i])));
                }
            });
        });
        group.finish();
    }
}

fn bench_get_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeBox::new();
        for i in 0..size {
            tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.find(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_get_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeArc::new();
        for i in 0..size {
            tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_rand_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.find(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_get_sequential_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeBox::new();
        for i in 0..size {
            tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_seq_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.find(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_get_sequential_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeArc::new();
        for i in 0..size {
            tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_seq_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.find(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_iter_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeBox::new();
        for i in 0..size {
            tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("iter_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                let mut node = tree.first();
                while let Some(n) = node {
                    black_box(n);
                    node = tree.next(n);
                }
            });
        });
        group.finish();
    }
}

fn bench_iter_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeArc::new();
        for i in 0..size {
            tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("iter_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                let mut node = tree.first();
                while let Some(n) = node {
                    black_box(n);
                    node = tree.next(n);
                }
            });
        });
        group.finish();
    }
}

fn bench_remove_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("rand_remove_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeBox::new();
                    for i in 0..size {
                        tree.add(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |mut tree: IntAvlTreeBox| {
                    for i in 0..size {
                        black_box(tree.remove_by_key(&data.keys[i]));
                    }
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

fn bench_remove_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("rand_remove_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeArc::new();
                    for i in 0..size {
                        tree.add(new_intnode_arc(data.keys[i]));
                    }
                    tree
                },
                |mut tree: IntAvlTreeArc| {
                    for i in 0..size {
                        black_box(tree.remove_by_key(&data.keys[i]));
                    }
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

criterion_group!(
    benches,
    bench_insert_box,
    bench_insert_arc,
    bench_insert_sequential_box,
    bench_insert_sequential_arc,
    bench_get_box,
    bench_get_arc,
    bench_get_sequential_box,
    bench_get_sequential_arc,
    bench_iter_box,
    bench_iter_arc,
    bench_remove_box,
    bench_remove_arc
);
criterion_main!(benches);
