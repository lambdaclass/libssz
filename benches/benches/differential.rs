use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ssz::{SszDecode, SszEncode};
use ssz_bench::fixtures::{make_header, make_vec_u64, pre_encode, BeaconBlockHeader};
use ssz_merkle::HashTreeRoot;

// ---------------------------------------------------------------------------
// Lighthouse helpers for BeaconBlockHeader (our type, not lighthouse-derived)
// ---------------------------------------------------------------------------

fn lighthouse_encode_header(h: &BeaconBlockHeader) -> Vec<u8> {
    let mut buf = Vec::new();
    <u64 as lighthouse_ssz::Encode>::ssz_append(&h.slot, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&h.proposer_index, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.parent_root, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.state_root, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.body_root, &mut buf);
    buf
}

fn lighthouse_decode_header(bytes: &[u8]) -> (u64, u64, [u8; 32], [u8; 32], [u8; 32]) {
    let slot = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
    let proposer_index = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
    let parent_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[16..48]).unwrap();
    let state_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[48..80]).unwrap();
    let body_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[80..112]).unwrap();
    (slot, proposer_index, parent_root, state_root, body_root)
}

// ---------------------------------------------------------------------------
// Encode benchmarks
// ---------------------------------------------------------------------------

fn diff_encode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/primitives");

    macro_rules! bench_encode {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
        };
    }

    bench_encode!("bool", true);
    bench_encode!("u8", 0xABu8);
    bench_encode!("u16", 0xABCDu16);
    bench_encode!("u32", 0xDEAD_BEEFu32);
    bench_encode!("u64", 0x1234_5678_9ABC_DEF0u64);
    bench_encode!("u128", u128::MAX);
    group.finish();
}

fn diff_encode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/byte_arrays");

    macro_rules! bench_encode_bytes {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
        };
    }

    bench_encode_bytes!("bytes32", [0xABu8; 32]);
    bench_encode_bytes!("bytes48", [0xABu8; 48]);
    bench_encode_bytes!("bytes96", [0xABu8; 96]);
    group.finish();
}

fn diff_encode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::new("libssz", size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz());
        });
        group.bench_with_input(BenchmarkId::new("lighthouse", size), &data, |b, data| {
            b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(data)));
        });
    }
    group.finish();
}

fn diff_encode_header(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/header");
    let header = make_header(42);
    group.bench_function("libssz", |b| b.iter(|| black_box(&header).to_ssz()));
    group.bench_function("lighthouse", |b| {
        b.iter(|| lighthouse_encode_header(black_box(&header)))
    });
    group.finish();
}

// ---------------------------------------------------------------------------
// Decode benchmarks
// ---------------------------------------------------------------------------

fn diff_decode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/primitives");

    macro_rules! bench_decode {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
        };
    }

    bench_decode!("bool", bool, true);
    bench_decode!("u8", u8, 0xABu8);
    bench_decode!("u16", u16, 0xABCDu16);
    bench_decode!("u32", u32, 0xDEAD_BEEFu32);
    bench_decode!("u64", u64, 0x1234_5678_9ABC_DEF0u64);
    bench_decode!("u128", u128, u128::MAX);
    group.finish();
}

fn diff_decode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/byte_arrays");

    macro_rules! bench_decode_bytes {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
        };
    }

    bench_decode_bytes!("bytes32", [u8; 32], [0xABu8; 32]);
    bench_decode_bytes!("bytes48", [u8; 48], [0xABu8; 48]);
    bench_decode_bytes!("bytes96", [u8; 96], [0xABu8; 96]);
    group.finish();
}

fn diff_decode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        let bytes = pre_encode(&data);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::new("libssz", size), &bytes, |b, bytes| {
            b.iter(|| <Vec<u64> as SszDecode>::from_ssz_bytes(black_box(bytes)).unwrap());
        });
        group.bench_with_input(BenchmarkId::new("lighthouse", size), &bytes, |b, bytes| {
            b.iter(|| {
                <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(bytes)).unwrap()
            });
        });
    }
    group.finish();
}

fn diff_decode_header(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/header");
    let header = make_header(42);
    let bytes = pre_encode(&header);
    group.bench_function("libssz", |b| {
        b.iter(|| BeaconBlockHeader::from_ssz_bytes(black_box(&bytes)).unwrap())
    });
    group.bench_function("lighthouse", |b| {
        b.iter(|| lighthouse_decode_header(black_box(&bytes)))
    });
    group.finish();
}

// ---------------------------------------------------------------------------
// Hash tree root benchmarks
// ---------------------------------------------------------------------------

fn diff_htr(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/htr");

    // bool
    group.bench_function("libssz/bool", |b| {
        b.iter(|| black_box(true).hash_tree_root())
    });
    group.bench_function("lighthouse/bool", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&true)).0)
    });

    // u64
    let val_u64 = 0x1234_5678_9ABC_DEF0u64;
    group.bench_function("libssz/u64", |b| {
        b.iter(|| black_box(val_u64).hash_tree_root())
    });
    group.bench_function("lighthouse/u64", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&val_u64)).0)
    });

    // [u8; 32]
    let val_bytes32 = [0xABu8; 32];
    group.bench_function("libssz/bytes32", |b| {
        b.iter(|| black_box(&val_bytes32).hash_tree_root())
    });
    group.bench_function("lighthouse/bytes32", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&val_bytes32)).0)
    });

    // Note: tree_hash does NOT support u128, so we skip it for HTR.

    group.finish();
}

// ---------------------------------------------------------------------------
// Criterion harness
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    diff_encode_primitives,
    diff_encode_byte_arrays,
    diff_encode_vec_u64,
    diff_encode_header,
    diff_decode_primitives,
    diff_decode_byte_arrays,
    diff_decode_vec_u64,
    diff_decode_header,
    diff_htr,
);
criterion_main!(benches);
