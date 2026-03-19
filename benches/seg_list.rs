use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_collections::SegList;

#[inline]
fn bench_seglist(count: usize) {
    let mut list = SegList::<u64>::new();
    for i in 0..count {
        list.push(i as u64);
    }
    let mut total = 0;
    for item in list {
        total += item;
    }
    black_box(total);
}

#[inline]
fn bench_vec(count: usize) {
    let mut vec = Vec::<u64>::new();
    for i in 0..count {
        vec.push(i as u64);
    }
    let mut total = 0;
    for item in vec {
        total += item;
    }
    black_box(total);
}

#[inline]
fn bench_seglist_iter(count: usize) {
    let mut list = SegList::<u64>::new();
    for i in 0..count {
        list.push(i as u64);
    }
    let mut total = 0;
    for item in list.iter() {
        total += *item;
    }
    black_box(total);
}

#[inline]
fn bench_vec_iter(count: usize) {
    let mut vec = Vec::<u64>::new();
    for i in 0..count {
        vec.push(i as u64);
    }
    let mut total = 0;
    for item in vec.iter() {
        total += *item;
    }
    black_box(total);
}

fn bench_append_drain(c: &mut Criterion) {
    let counts = [10, 32, 100, 500];

    let mut group = c.benchmark_group("seg_list_append_drain");

    for count in counts {
        group.throughput(Throughput::Elements(count as u64));

        group.bench_with_input(BenchmarkId::new("SegList", count), &count, |b, &count| {
            b.iter(|| bench_seglist(count))
        });

        group.bench_with_input(BenchmarkId::new("Vec", count), &count, |b, &count| {
            b.iter(|| bench_vec(count))
        });
    }

    group.finish();
}

fn bench_iter(c: &mut Criterion) {
    let counts = [10, 32, 100, 500];

    let mut group = c.benchmark_group("seg_list_iter");

    for count in counts {
        group.throughput(Throughput::Elements(count as u64));

        group.bench_with_input(BenchmarkId::new("SegList", count), &count, |b, &count| {
            b.iter(|| bench_seglist_iter(count))
        });

        group.bench_with_input(BenchmarkId::new("Vec", count), &count, |b, &count| {
            b.iter(|| bench_vec_iter(count))
        });
    }

    group.finish();
}

criterion_group!(benches, bench_append_drain, bench_iter);
criterion_main!(benches);
