//! Benchmark for embed_collections::BTreeMap

mod btree_common;

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_btree::BTreeMap;

use btree_common::{SIZES, TestData, size_desc};

fn bench_insert(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map: BTreeMap<u32, u32> = BTreeMap::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_insert_sequential(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("insert_seq");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map: BTreeMap<u32, u32> = BTreeMap::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_get(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map: BTreeMap<u32, u32> = BTreeMap::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("get_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(map.get(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_get_sequential(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut map: BTreeMap<u32, u32> = BTreeMap::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("get_seq");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                for i in 0..size {
                    black_box(map.get(&data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map: BTreeMap<u32, u32> = BTreeMap::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("iter");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("all_{}", desc), |b| {
            b.iter(|| {
                for (k, v) in &map {
                    black_box((k, v));
                }
            });
        });
        group.finish();
    }
}

fn bench_remove(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("remove_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |mut map: BTreeMap<u32, u32>| {
                    for i in 0..size {
                        black_box(map.remove(&data.keys[i]));
                    }
                },
                criterion::BatchSize::LargeInput,
            );
        });
        group.finish();
    }
}

fn bench_into_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("into_iter");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |map: BTreeMap<u32, u32>| {
                    for (k, v) in map {
                        black_box((k, v));
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
    bench_insert,
    bench_insert_sequential,
    bench_get,
    bench_get_sequential,
    bench_iter,
    bench_remove,
    bench_into_iter
);
criterion_main!(benches);
