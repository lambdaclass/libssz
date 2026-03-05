use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ssz_bench::fixtures::{
    make_bench_union, make_bitlist, make_bitlist_2048, make_bitvector, make_bitvector_512,
    make_header, make_list_u64, make_nested_container, make_validator, make_validator_list,
    make_variable_container, make_vec_u64, make_vector_bytes32,
};
use ssz_merkle::HashTreeRoot;

fn htr_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/primitives");
    group.bench_function("bool", |b| b.iter(|| black_box(true).hash_tree_root()));
    group.bench_function("u8", |b| b.iter(|| black_box(0xABu8).hash_tree_root()));
    group.bench_function("u16", |b| b.iter(|| black_box(0x1234u16).hash_tree_root()));
    group.bench_function("u32", |b| {
        b.iter(|| black_box(0x1234_5678u32).hash_tree_root())
    });
    group.bench_function("u64", |b| {
        b.iter(|| black_box(0x1234_5678_9abc_def0u64).hash_tree_root())
    });
    group.bench_function("u128", |b| b.iter(|| black_box(u128::MAX).hash_tree_root()));
    group.bench_function("bytes32", |b| {
        b.iter(|| black_box([0xabu8; 32]).hash_tree_root())
    });
    group.finish();
}

fn htr_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| black_box(data).hash_tree_root());
        });
    }
    group.finish();
}

fn htr_list_validator(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/list_validator");
    group.sample_size(10);
    for &size in &[100, 1_000, 10_000] {
        let list = make_validator_list(size);
        group.throughput(Throughput::Bytes((size * 121) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &list, |b, list| {
            b.iter(|| black_box(list).hash_tree_root());
        });
    }
    group.finish();
}

fn htr_vector_bytes32(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/vector_bytes32");
    let v100 = make_vector_bytes32::<100>();
    let v1000 = make_vector_bytes32::<1000>();
    group.throughput(Throughput::Bytes((100 * 32) as u64));
    group.bench_function("100", |b| b.iter(|| black_box(&v100).hash_tree_root()));
    group.throughput(Throughput::Bytes((1000 * 32) as u64));
    group.bench_function("1000", |b| b.iter(|| black_box(&v1000).hash_tree_root()));
    group.finish();
}

fn htr_bitfields(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/bitfields");
    for &bits in &[64, 512, 2048, 4096] {
        group.throughput(Throughput::Bytes((bits / 8) as u64));
        match bits {
            64 => {
                let bl = make_bitlist::<64>(64);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).hash_tree_root())
                });
                let bv = make_bitvector::<64>();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).hash_tree_root())
                });
            }
            512 => {
                let bv = make_bitvector_512();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).hash_tree_root())
                });
            }
            2048 => {
                let bl = make_bitlist_2048();
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).hash_tree_root())
                });
            }
            4096 => {
                let bl = make_bitlist::<4096>(4096);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).hash_tree_root())
                });
                let bv = make_bitvector::<4096>();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).hash_tree_root())
                });
            }
            _ => unreachable!(),
        }
    }
    group.finish();
}

fn htr_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/containers");
    let validator = make_validator(42);
    let header = make_header(42);
    group.bench_function("validator", |b| {
        b.iter(|| black_box(&validator).hash_tree_root())
    });
    group.bench_function("beacon_block_header", |b| {
        b.iter(|| black_box(&header).hash_tree_root())
    });
    group.finish();
}

fn htr_unions(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/unions");
    for variant in 0..4 {
        let data = make_bench_union(variant);
        group.bench_with_input(BenchmarkId::from_parameter(variant), &data, |b, data| {
            b.iter(|| black_box(data).hash_tree_root())
        });
    }
    group.finish();
}

fn htr_variable_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/variable_container");
    for &var_size in &[100, 1_000, 10_000] {
        let data = make_variable_container(var_size);
        group.throughput(Throughput::Bytes((8 + var_size + 32 + var_size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(var_size), &data, |b, data| {
            b.iter(|| black_box(data).hash_tree_root())
        });
    }
    group.finish();
}

fn htr_nested_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/nested_container");
    group.sample_size(10);
    for &n in &[10, 100, 1_000] {
        let data = make_nested_container(n);
        group.throughput(Throughput::Bytes((n * 121 + 120) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &data, |b, data| {
            b.iter(|| black_box(data).hash_tree_root());
        });
    }
    group.finish();
}

fn htr_list_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("hash_tree_root/list_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_list_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| black_box(data).hash_tree_root());
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    htr_primitives,
    htr_vec_u64,
    htr_list_validator,
    htr_vector_bytes32,
    htr_bitfields,
    htr_containers,
    htr_unions,
    htr_variable_container,
    htr_nested_container,
    htr_list_u64,
);
criterion_main!(benches);
