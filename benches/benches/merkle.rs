use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use libssz_merkle::{hash_nodes, merkleize, mix_in_length, pack, pack_bits, Node};

fn make_chunks(n: usize) -> Vec<Node> {
    (0..n)
        .map(|i| {
            let mut node = [0u8; 32];
            node[..8].copy_from_slice(&(i as u64).to_le_bytes());
            node
        })
        .collect()
}

fn bench_hash_nodes(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/hash_nodes");
    let a: Node = [0xaa; 32];
    let b: Node = [0xbb; 32];
    group.bench_function("single", |bench| {
        bench.iter(|| hash_nodes(black_box(&a), black_box(&b)))
    });
    group.finish();
}

fn bench_pack(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/pack");
    for &size in &[32, 256, 1024, 32768] {
        let data: Vec<u8> = (0..size).map(|i| i as u8).collect();
        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| pack(black_box(data)));
        });
    }
    group.finish();
}

fn bench_pack_bits(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/pack_bits");
    for &num_bits in &[64usize, 512, 2048, 8192] {
        let num_bytes = num_bits.div_ceil(8);
        let data: Vec<u8> = (0..num_bytes).map(|i| i as u8).collect();
        group.bench_with_input(
            BenchmarkId::from_parameter(num_bits),
            &(data.clone(), num_bits),
            |b, (data, num_bits)| {
                b.iter(|| pack_bits(black_box(data), black_box(*num_bits)));
            },
        );
    }
    group.finish();
}

fn bench_merkleize(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/merkleize");
    for &n in &[1, 4, 16, 64, 256, 1024, 4096] {
        let chunks = make_chunks(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &chunks, |b, chunks| {
            b.iter(|| merkleize(black_box(chunks), None));
        });
    }
    group.finish();
}

fn bench_merkleize_with_limit(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/merkleize_with_limit");
    // Chunks present < limit — tests zero-hash padding path
    for &(n, limit) in &[(64, 1024), (256, 4096), (1024, 1_048_576)] {
        let chunks = make_chunks(n);
        let label = format!("{n}_of_{limit}");
        group.bench_with_input(BenchmarkId::new("chunks", &label), &chunks, |b, chunks| {
            b.iter(|| merkleize(black_box(chunks), Some(limit)));
        });
    }
    group.finish();
}

fn bench_mix_in_length(c: &mut Criterion) {
    let mut group = c.benchmark_group("merkle/mix_in_length");
    let root: Node = [0xcc; 32];
    group.bench_function("single", |b| {
        b.iter(|| mix_in_length(black_box(&root), black_box(1_000_000)))
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_hash_nodes,
    bench_pack,
    bench_pack_bits,
    bench_merkleize,
    bench_merkleize_with_limit,
    bench_mix_in_length,
);
criterion_main!(benches);
