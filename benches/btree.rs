//! Benchmark for embed_collections::BTreeMap

mod btree_common;

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_btree::{compact, large};

use btree_common::{SIZES, TestData, size_desc};

fn bench_large_insert_rand(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("large::insert_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map = large::BTreeMap::<u32, u32>::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_compact_insert_rand(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("compact::insert_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map = compact::BTreeMap::<u32, u32>::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_large_insert_seq(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("large::insert_seq");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map = large::BTreeMap::<u32, u32>::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_compact_insert_seq(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("compact::insert_seq");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter(|| {
                let mut map = compact::BTreeMap::<u32, u32>::new();
                for i in 0..size {
                    map.insert(black_box(data.keys[i]), black_box(data.keys[i]));
                }
            });
        });
        group.finish();
    }
}

fn bench_large_get_rand(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map = large::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("large::get_rand");
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

fn bench_compact_get_rand(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map = compact::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("large::get_rand");
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

fn bench_large_get_seq(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut map = large::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("large::get_seq");
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

fn bench_compact_get_seq(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut map = compact::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("compact::get_seq");
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

fn bench_large_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map = large::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("large::iter");
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

fn bench_compact_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut map = compact::BTreeMap::<u32, u32>::new();
        for i in 0..size {
            map.insert(data.keys[i], data.keys[i]);
        }

        let mut group = c.benchmark_group("compact::iter");
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

fn bench_large_remove(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("large::remove_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map = large::BTreeMap::<u32, u32>::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |mut map: large::BTreeMap<u32, u32>| {
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

fn bench_compact_remove(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_random(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("compact::remove_rand");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map = compact::BTreeMap::<u32, u32>::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |mut map: compact::BTreeMap<u32, u32>| {
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

fn bench_large_into_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("large_into_iter");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map = large::BTreeMap::<u32, u32>::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |map: large::BTreeMap<u32, u32>| {
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

fn bench_compact_into_iter(c: &mut Criterion) {
    for &size in &SIZES {
        let data = TestData::new_sequential(size);
        let desc = size_desc(size);

        let mut group = c.benchmark_group("compact::into_iter");
        group.throughput(Throughput::Elements(size as u64));
        group.bench_function(format!("{}", desc), |b| {
            b.iter_batched(
                || {
                    let mut map = compact::BTreeMap::<u32, u32>::new();
                    for i in 0..size {
                        map.insert(data.keys[i], data.keys[i]);
                    }
                    map
                },
                |map: compact::BTreeMap<u32, u32>| {
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
    bench_large_insert_rand,
    bench_compact_insert_rand,
    bench_large_insert_seq,
    bench_compact_insert_seq,
    bench_large_get_rand,
    bench_compact_get_rand,
    bench_large_get_seq,
    bench_compact_get_seq,
    bench_large_iter,
    bench_compact_iter,
    bench_large_remove,
    bench_compact_remove,
    bench_large_into_iter,
    bench_compact_into_iter,
);
criterion_main!(benches);
