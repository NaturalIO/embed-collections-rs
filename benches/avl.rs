//! Benchmark for embed_collections::AvlTree

mod btree_common;

use core::cell::UnsafeCell;
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_avl::{AvlItem, AvlNode, AvlTree, impl_ord_with_borrow};
use std::borrow::Borrow;
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
    #[inline]
    fn get_node(&self) -> &mut AvlNode<Self, ()> {
        unsafe { &mut *self.node.get() }
    }
}

impl Borrow<u32> for IntAvlNode {
    #[inline]
    fn borrow(&self) -> &u32 {
        &self.value
    }
}
impl_ord_with_borrow!(IntAvlNode, u32);

fn new_intnode_box(i: u32) -> Box<IntAvlNode> {
    Box::new(IntAvlNode { value: i, ..Default::default() })
}

fn new_intnode_arc(i: u32) -> Arc<IntAvlNode> {
    Arc::new(IntAvlNode { value: i, ..Default::default() })
}

type IntAvlTreeBox = AvlTree<Box<IntAvlNode>, ()>;
type IntAvlTreeArc = AvlTree<Arc<IntAvlNode>, ()>;

fn bench_bulk_insert_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_bulk_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeBox::new();
                let mut ent = tree.last_entry();
                for i in 0..size {
                    ent = black_box(unsafe { ent.append_unchecked(new_intnode_box(data.keys[i])) });
                }
            });
        });
        group.finish();
    }
}

fn bench_bulk_insert_arc(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_bulk_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = IntAvlTreeArc::new();
                let mut ent = tree.last_entry();
                for i in 0..size {
                    ent = black_box(unsafe { ent.append_unchecked(new_intnode_arc(data.keys[i])) });
                }
            });
        });
        group.finish();
    }
}

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
                    let _ = black_box(tree.add(new_intnode_box(data.keys[i])));
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
                    let _ = black_box(tree.add(new_intnode_arc(data.keys[i])));
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
                    let _ = black_box(tree.add(new_intnode_box(data.keys[i])));
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
                    let _ = black_box(tree.add(new_intnode_arc(data.keys[i])));
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
            let _ = tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.get(&data.keys[i]));
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
            let _ = tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_rand_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.get(&data.keys[i]));
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
            let _ = tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_seq_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.get(&data.keys[i]));
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
            let _ = tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_seq_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(tree.get(&data.keys[i]));
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
            let _ = tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("iter_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                let mut iter = tree.iter();
                while let Some(_n) = black_box(iter.next()) {}
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
            let _ = tree.add(new_intnode_arc(data.keys[i]));
        }

        let mut group = c.benchmark_group("iter_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                let mut iter = tree.iter();
                while let Some(_n) = black_box(iter.next()) {}
            });
        });
        group.finish();
    }
}

fn bench_remove_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("remove_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeBox::new();
                    for i in 0..size {
                        let _ = tree.add(new_intnode_box(data.keys[i]));
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

        let mut group = c.benchmark_group("remove_rand_arc");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeArc::new();
                    for i in 0..size {
                        let _ = tree.add(new_intnode_arc(data.keys[i]));
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

fn bench_into_iter_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut tree = IntAvlTreeBox::new();
        for i in 0..size {
            let _ = tree.add(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("into_iter_box");
        group.throughput(Throughput::Elements(size as u64));

        group.bench_function(format!("all_{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeBox::new();
                    for i in 0..size {
                        let _ = tree.add(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |tree: IntAvlTreeBox| {
                    let mut iter = tree.into_iter();
                    while let Some(_n) = black_box(iter.next()) {}
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

fn bench_drop_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);
        let mut group = c.benchmark_group("drop_box");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = IntAvlTreeBox::new();
                    for i in 0..size {
                        let _ = tree.add(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |tree: IntAvlTreeBox| {
                    drop(tree);
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

criterion_group!(
    benches,
    bench_bulk_insert_box,
    bench_bulk_insert_arc,
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
    bench_remove_arc,
    bench_into_iter_box,
    bench_drop_box
);
criterion_main!(benches);
