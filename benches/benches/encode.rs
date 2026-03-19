use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use libssz::SszEncode;
use ssz_bench::fixtures::{
    make_attestation_data, make_beacon_state, make_bench_union, make_bitlist, make_bitlist_2048,
    make_bitvector, make_bitvector_512, make_checkpoint, make_eth1_data, make_fork, make_header,
    make_list_u64, make_nested_container, make_pending_attestation, make_validator,
    make_validator_list, make_variable_container, make_vec_u64, make_vector_bytes32,
};

fn encode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/primitives");
    group.bench_function("bool", |b| b.iter(|| black_box(true).to_ssz()));
    group.bench_function("u8", |b| b.iter(|| black_box(0xABu8).to_ssz()));
    group.bench_function("u16", |b| b.iter(|| black_box(0x1234u16).to_ssz()));
    group.bench_function("u32", |b| b.iter(|| black_box(0x1234_5678u32).to_ssz()));
    group.bench_function("u64", |b| {
        b.iter(|| black_box(0x1234_5678_9abc_def0u64).to_ssz())
    });
    group.bench_function("u128", |b| b.iter(|| black_box(u128::MAX).to_ssz()));
    group.finish();
}

fn encode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/byte_arrays");
    let b32 = [0xabu8; 32];
    let b48 = [0xabu8; 48];
    let b96 = [0xabu8; 96];
    group.bench_function("bytes32", |b| b.iter(|| black_box(&b32).to_ssz()));
    group.bench_function("bytes48", |b| b.iter(|| black_box(&b48).to_ssz()));
    group.bench_function("bytes96", |b| b.iter(|| black_box(&b96).to_ssz()));
    group.finish();
}

fn encode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz());
        });
    }
    group.finish();
}

fn encode_list_validator(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/list_validator");
    group.sample_size(10);
    for &size in &[100, 1_000, 10_000] {
        let list = make_validator_list(size);
        group.throughput(Throughput::Bytes((size * 121) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &list, |b, list| {
            b.iter(|| black_box(list).to_ssz());
        });
    }
    group.finish();
}

fn encode_vector_bytes32(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/vector_bytes32");
    let v100 = make_vector_bytes32::<100>();
    let v1000 = make_vector_bytes32::<1000>();
    group.throughput(Throughput::Bytes((100 * 32) as u64));
    group.bench_function("100", |b| b.iter(|| black_box(&v100).to_ssz()));
    group.throughput(Throughput::Bytes((1000 * 32) as u64));
    group.bench_function("1000", |b| b.iter(|| black_box(&v1000).to_ssz()));
    group.finish();
}

fn encode_bitfields(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/bitfields");
    for &bits in &[64, 512, 2048, 4096] {
        group.throughput(Throughput::Bytes((bits / 8) as u64));
        match bits {
            64 => {
                let bl = make_bitlist::<64>(64);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).to_ssz())
                });
                let bv = make_bitvector::<64>();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).to_ssz())
                });
            }
            512 => {
                let bv = make_bitvector_512();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).to_ssz())
                });
            }
            2048 => {
                let bl = make_bitlist_2048();
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).to_ssz())
                });
            }
            4096 => {
                let bl = make_bitlist::<4096>(4096);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl, |b, bl| {
                    b.iter(|| black_box(bl).to_ssz())
                });
                let bv = make_bitvector::<4096>();
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv, |b, bv| {
                    b.iter(|| black_box(bv).to_ssz())
                });
            }
            _ => unreachable!(),
        }
    }
    group.finish();
}

fn encode_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/containers");
    let validator = make_validator(42);
    let header = make_header(42);
    group.bench_function("validator", |b| b.iter(|| black_box(&validator).to_ssz()));
    group.bench_function("beacon_block_header", |b| {
        b.iter(|| black_box(&header).to_ssz())
    });
    group.finish();
}

fn encode_unions(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/unions");
    for variant in 0..4 {
        let data = make_bench_union(variant);
        group.bench_with_input(BenchmarkId::from_parameter(variant), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz())
        });
    }
    group.finish();
}

fn encode_variable_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/variable_container");
    for &var_size in &[100, 1_000, 10_000] {
        let data = make_variable_container(var_size);
        group.throughput(Throughput::Bytes((8 + var_size + 32 + var_size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(var_size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz())
        });
    }
    group.finish();
}

fn encode_nested_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/nested_container");
    group.sample_size(10);
    for &n in &[10, 100, 1_000] {
        let data = make_nested_container(n);
        group.throughput(Throughput::Bytes((n * 121 + 120) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz());
        });
    }
    group.finish();
}

fn encode_list_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/list_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_list_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz());
        });
    }
    group.finish();
}

fn encode_ssz_append(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/ssz_append_reuse");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::new("to_ssz", size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz())
        });
        group.bench_with_input(BenchmarkId::new("ssz_append", size), &data, |b, data| {
            let mut buf = Vec::with_capacity(size * 8);
            b.iter(|| {
                buf.clear();
                black_box(data).ssz_append(&mut buf);
                black_box(&buf);
            });
        });
    }
    group.finish();
}

fn encode_consensus_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/consensus_containers");
    let fork = make_fork();
    let checkpoint = make_checkpoint(42);
    let eth1_data = make_eth1_data(42);
    let attestation_data = make_attestation_data(42);
    let pending_attestation = make_pending_attestation(42);
    group.bench_function("fork", |b| b.iter(|| black_box(&fork).to_ssz()));
    group.bench_function("checkpoint", |b| b.iter(|| black_box(&checkpoint).to_ssz()));
    group.bench_function("eth1_data", |b| b.iter(|| black_box(&eth1_data).to_ssz()));
    group.bench_function("attestation_data", |b| {
        b.iter(|| black_box(&attestation_data).to_ssz())
    });
    group.bench_function("pending_attestation", |b| {
        b.iter(|| black_box(&pending_attestation).to_ssz())
    });
    group.finish();
}

fn encode_beacon_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode/beacon_state");
    group.sample_size(10);
    for &n_validators in &[16384, 100_000, 300_000] {
        let state = make_beacon_state(n_validators);
        group.bench_with_input(
            BenchmarkId::from_parameter(n_validators),
            &state,
            |b, state| b.iter(|| black_box(state).to_ssz()),
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    encode_primitives,
    encode_byte_arrays,
    encode_vec_u64,
    encode_list_validator,
    encode_vector_bytes32,
    encode_bitfields,
    encode_containers,
    encode_unions,
    encode_variable_container,
    encode_nested_container,
    encode_list_u64,
    encode_ssz_append,
    encode_consensus_containers,
    encode_beacon_state,
);
criterion_main!(benches);
