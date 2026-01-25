use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use embed_collections::range_tree_old::{DummyAllocator, RangeTree};

fn bench_range_tree_insert_fragmented_old(c: &mut Criterion) {
    let count = 10000;
    let fragment_size = 4096;
    let gap_size = 4096;

    let ranges: Vec<(u64, u64)> =
        (0..count).map(|i| (i as u64 * (fragment_size + gap_size), fragment_size)).collect();

    let mut group = c.benchmark_group("range_tree_fragmented_old");
    group.throughput(Throughput::Elements(count as u64));
    group.bench_function("insert_10000_fragments", |b| {
        b.iter(|| {
            let mut tree = RangeTree::<DummyAllocator>::new();
            for &(start, size) in &ranges {
                tree.add(black_box(start), black_box(size));
            }
        })
    });
    group.finish();
}

criterion_group!(benches, bench_range_tree_insert_fragmented_old);
criterion_main!(benches);
