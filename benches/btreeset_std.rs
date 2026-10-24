//! Benchmark for embed_collections::AvlTree

mod btree_common;

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt;
use std::time::Duration;

use btree_common::{SIZES, TestData, size_desc};

#[derive(Default, Debug, PartialEq, PartialOrd, Ord, Eq)]
struct IntNode {
    pub value: u32,
}

impl Borrow<u32> for Box<IntNode> {
    #[inline]
    fn borrow(&self) -> &u32 {
        &self.value
    }
}

fn new_intnode_box(i: u32) -> Box<IntNode> {
    Box::new(IntNode { value: i })
}

fn bench_insert_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = BTreeSet::new();
                for i in 0..size {
                    let _ = black_box(tree.insert(new_intnode_box(data.keys[i])));
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
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut tree = BTreeSet::new();
                for i in 0..size {
                    let _ = black_box(tree.insert(new_intnode_box(data.keys[i])));
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

        let mut tree = BTreeSet::new();
        for i in 0..size {
            let _ = tree.insert(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
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

        let mut tree = BTreeSet::new();
        for i in 0..size {
            let _ = tree.insert(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("get_seq_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
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

        let mut tree = BTreeSet::new();
        for i in 0..size {
            let _ = tree.insert(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("iter_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                let mut iter = tree.iter();
                while let Some(_n) = black_box(iter.next()) {}
            });
        });
        group.finish();
    }
}

fn bench_remove_seq_box(c: &mut Criterion) {
    for &size in &SIZES {
        let desc = size_desc(size);
        // the speed of remove in ordering is stable to compare because the dataset is fixed
        let mut group = c.benchmark_group("remove_seq_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = BTreeSet::new();
                    for i in 0..size {
                        let _ = tree.insert(new_intnode_box(i as u32));
                    }
                    tree
                },
                |mut tree: BTreeSet<Box<IntNode>>| {
                    for i in 0..size {
                        black_box(tree.remove(&(i as u32)));
                    }
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

fn bench_remove_rand_box(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("remove_rand_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = BTreeSet::new();
                    for i in 0..size {
                        let _ = tree.insert(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |mut tree: BTreeSet<Box<IntNode>>| {
                    for i in 0..size {
                        black_box(tree.remove(&data.keys[i]));
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

        let mut tree = BTreeSet::new();
        for i in 0..size {
            let _ = tree.insert(new_intnode_box(data.keys[i]));
        }

        let mut group = c.benchmark_group("into_iter_box");
        group.throughput(Throughput::Elements(size as u64));
        group.measurement_time(Duration::from_secs(15));

        group.bench_function(format!("all_{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = BTreeSet::new();
                    for i in 0..size {
                        let _ = tree.insert(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |tree: BTreeSet<Box<IntNode>>| {
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
        group.measurement_time(Duration::from_secs(15));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut tree = BTreeSet::new();
                    for i in 0..size {
                        let _ = tree.insert(new_intnode_box(data.keys[i]));
                    }
                    tree
                },
                |tree: BTreeSet<Box<IntNode>>| {
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
    bench_insert_box,
    bench_insert_sequential_box,
    bench_get_box,
    bench_get_sequential_box,
    bench_iter_box,
    bench_remove_seq_box,
    bench_remove_rand_box,
    bench_into_iter_box,
    bench_drop_box
);
criterion_main!(benches);
