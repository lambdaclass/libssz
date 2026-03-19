use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use libssz::SszDecode;
use ssz_bench::fixtures::{
    make_attestation_data, make_beacon_state, make_bench_union, make_bitlist, make_bitlist_2048,
    make_bitvector, make_bitvector_512, make_checkpoint, make_eth1_data, make_fork, make_header,
    make_list_u64, make_nested_container, make_pending_attestation, make_validator,
    make_validator_list, make_variable_container, make_vec_u64, make_vector_bytes32, pre_encode,
    AttestationData, BeaconBlockHeader, BeaconState, BenchUnion, Checkpoint, Eth1Data, Fork,
    NestedContainer, PendingAttestation, Validator, VariableContainer,
};
use libssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

fn decode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/primitives");
    let bool_bytes = pre_encode(&true);
    let u8_bytes = pre_encode(&0xABu8);
    let u16_bytes = pre_encode(&0x1234u16);
    let u32_bytes = pre_encode(&0x1234_5678u32);
    let u64_bytes = pre_encode(&0x1234_5678_9abc_def0u64);
    let u128_bytes = pre_encode(&u128::MAX);
    group.bench_function("bool", |b| {
        b.iter(|| bool::from_ssz_bytes(black_box(&bool_bytes)).unwrap())
    });
    group.bench_function("u8", |b| {
        b.iter(|| u8::from_ssz_bytes(black_box(&u8_bytes)).unwrap())
    });
    group.bench_function("u16", |b| {
        b.iter(|| u16::from_ssz_bytes(black_box(&u16_bytes)).unwrap())
    });
    group.bench_function("u32", |b| {
        b.iter(|| u32::from_ssz_bytes(black_box(&u32_bytes)).unwrap())
    });
    group.bench_function("u64", |b| {
        b.iter(|| u64::from_ssz_bytes(black_box(&u64_bytes)).unwrap())
    });
    group.bench_function("u128", |b| {
        b.iter(|| u128::from_ssz_bytes(black_box(&u128_bytes)).unwrap())
    });
    group.finish();
}

fn decode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/byte_arrays");
    let b32_bytes = pre_encode(&[0xabu8; 32]);
    let b48_bytes = pre_encode(&[0xabu8; 48]);
    let b96_bytes = pre_encode(&[0xabu8; 96]);
    group.bench_function("bytes32", |b| {
        b.iter(|| <[u8; 32]>::from_ssz_bytes(black_box(&b32_bytes)).unwrap())
    });
    group.bench_function("bytes48", |b| {
        b.iter(|| <[u8; 48]>::from_ssz_bytes(black_box(&b48_bytes)).unwrap())
    });
    group.bench_function("bytes96", |b| {
        b.iter(|| <[u8; 96]>::from_ssz_bytes(black_box(&b96_bytes)).unwrap())
    });
    group.finish();
}

fn decode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        let encoded = pre_encode(&data);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &encoded, |b, encoded| {
            b.iter(|| Vec::<u64>::from_ssz_bytes(black_box(encoded)).unwrap());
        });
    }
    group.finish();
}

fn decode_list_validator(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/list_validator");
    group.sample_size(10);
    for &size in &[100, 1_000, 10_000] {
        let list = make_validator_list(size);
        let encoded = pre_encode(&list);
        group.throughput(Throughput::Bytes((size * 121) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &encoded, |b, encoded| {
            b.iter(|| SszList::<Validator, 1_048_576>::from_ssz_bytes(black_box(encoded)).unwrap());
        });
    }
    group.finish();
}

fn decode_vector_bytes32(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/vector_bytes32");
    let v100 = make_vector_bytes32::<100>();
    let v1000 = make_vector_bytes32::<1000>();
    let enc100 = pre_encode(&v100);
    let enc1000 = pre_encode(&v1000);
    group.throughput(Throughput::Bytes((100 * 32) as u64));
    group.bench_function("100", |b| {
        b.iter(|| SszVector::<[u8; 32], 100>::from_ssz_bytes(black_box(&enc100)).unwrap())
    });
    group.throughput(Throughput::Bytes((1000 * 32) as u64));
    group.bench_function("1000", |b| {
        b.iter(|| SszVector::<[u8; 32], 1000>::from_ssz_bytes(black_box(&enc1000)).unwrap())
    });
    group.finish();
}

fn decode_bitfields(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/bitfields");
    for &bits in &[64, 512, 2048, 4096] {
        group.throughput(Throughput::Bytes((bits / 8) as u64));
        match bits {
            64 => {
                let bl = make_bitlist::<64>(64);
                let bl_enc = pre_encode(&bl);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl_enc, |b, enc| {
                    b.iter(|| SszBitlist::<64>::from_ssz_bytes(black_box(enc)).unwrap())
                });
                let bv = make_bitvector::<64>();
                let bv_enc = pre_encode(&bv);
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv_enc, |b, enc| {
                    b.iter(|| SszBitvector::<64>::from_ssz_bytes(black_box(enc)).unwrap())
                });
            }
            512 => {
                let bv = make_bitvector_512();
                let bv_enc = pre_encode(&bv);
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv_enc, |b, enc| {
                    b.iter(|| SszBitvector::<512>::from_ssz_bytes(black_box(enc)).unwrap())
                });
            }
            2048 => {
                let bl = make_bitlist_2048();
                let bl_enc = pre_encode(&bl);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl_enc, |b, enc| {
                    b.iter(|| SszBitlist::<2048>::from_ssz_bytes(black_box(enc)).unwrap())
                });
            }
            4096 => {
                let bl = make_bitlist::<4096>(4096);
                let bl_enc = pre_encode(&bl);
                group.bench_with_input(BenchmarkId::new("bitlist", bits), &bl_enc, |b, enc| {
                    b.iter(|| SszBitlist::<4096>::from_ssz_bytes(black_box(enc)).unwrap())
                });
                let bv = make_bitvector::<4096>();
                let bv_enc = pre_encode(&bv);
                group.bench_with_input(BenchmarkId::new("bitvector", bits), &bv_enc, |b, enc| {
                    b.iter(|| SszBitvector::<4096>::from_ssz_bytes(black_box(enc)).unwrap())
                });
            }
            _ => unreachable!(),
        }
    }
    group.finish();
}

fn decode_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/containers");
    let validator = make_validator(42);
    let header = make_header(42);
    let val_enc = pre_encode(&validator);
    let hdr_enc = pre_encode(&header);
    group.bench_function("validator", |b| {
        b.iter(|| Validator::from_ssz_bytes(black_box(&val_enc)).unwrap())
    });
    group.bench_function("beacon_block_header", |b| {
        b.iter(|| BeaconBlockHeader::from_ssz_bytes(black_box(&hdr_enc)).unwrap())
    });
    group.finish();
}

fn decode_unions(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/unions");
    for variant in 0..4 {
        let data = make_bench_union(variant);
        let encoded = pre_encode(&data);
        group.bench_with_input(
            BenchmarkId::from_parameter(variant),
            &encoded,
            |b, encoded| b.iter(|| BenchUnion::from_ssz_bytes(black_box(encoded)).unwrap()),
        );
    }
    group.finish();
}

fn decode_variable_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/variable_container");
    for &var_size in &[100, 1_000, 10_000] {
        let data = make_variable_container(var_size);
        let encoded = pre_encode(&data);
        group.throughput(Throughput::Bytes((8 + var_size + 32 + var_size * 8) as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(var_size),
            &encoded,
            |b, encoded| b.iter(|| VariableContainer::from_ssz_bytes(black_box(encoded)).unwrap()),
        );
    }
    group.finish();
}

fn decode_nested_container(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/nested_container");
    group.sample_size(10);
    for &n in &[10, 100, 1_000] {
        let data = make_nested_container(n);
        let encoded = pre_encode(&data);
        group.throughput(Throughput::Bytes((n * 121 + 120) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &encoded, |b, encoded| {
            b.iter(|| NestedContainer::from_ssz_bytes(black_box(encoded)).unwrap());
        });
    }
    group.finish();
}

fn decode_list_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/list_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_list_u64(size);
        let encoded = pre_encode(&data);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &encoded, |b, encoded| {
            b.iter(|| SszList::<u64, 1_048_576>::from_ssz_bytes(black_box(encoded)).unwrap());
        });
    }
    group.finish();
}

fn decode_consensus_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/consensus_containers");
    let fork = make_fork();
    let checkpoint = make_checkpoint(42);
    let eth1_data = make_eth1_data(42);
    let attestation_data = make_attestation_data(42);
    let pending_attestation = make_pending_attestation(42);
    let fork_enc = pre_encode(&fork);
    let checkpoint_enc = pre_encode(&checkpoint);
    let eth1_data_enc = pre_encode(&eth1_data);
    let attestation_data_enc = pre_encode(&attestation_data);
    let pending_attestation_enc = pre_encode(&pending_attestation);
    group.bench_function("fork", |b| {
        b.iter(|| Fork::from_ssz_bytes(black_box(&fork_enc)).unwrap())
    });
    group.bench_function("checkpoint", |b| {
        b.iter(|| Checkpoint::from_ssz_bytes(black_box(&checkpoint_enc)).unwrap())
    });
    group.bench_function("eth1_data", |b| {
        b.iter(|| Eth1Data::from_ssz_bytes(black_box(&eth1_data_enc)).unwrap())
    });
    group.bench_function("attestation_data", |b| {
        b.iter(|| AttestationData::from_ssz_bytes(black_box(&attestation_data_enc)).unwrap())
    });
    group.bench_function("pending_attestation", |b| {
        b.iter(|| PendingAttestation::from_ssz_bytes(black_box(&pending_attestation_enc)).unwrap())
    });
    group.finish();
}

fn decode_beacon_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode/beacon_state");
    group.sample_size(10);
    for &n_validators in &[16384, 100_000, 300_000] {
        let state = make_beacon_state(n_validators);
        let encoded = pre_encode(&state);
        group.throughput(Throughput::Bytes(encoded.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(n_validators),
            &encoded,
            |b, encoded| {
                b.iter(|| BeaconState::from_ssz_bytes(black_box(encoded)).unwrap());
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    decode_primitives,
    decode_byte_arrays,
    decode_vec_u64,
    decode_list_validator,
    decode_vector_bytes32,
    decode_bitfields,
    decode_containers,
    decode_unions,
    decode_variable_container,
    decode_nested_container,
    decode_list_u64,
    decode_consensus_containers,
    decode_beacon_state,
);
criterion_main!(benches);
