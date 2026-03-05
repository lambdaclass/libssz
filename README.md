# libssz

A fast, modular [Simple Serialize (SSZ)](https://ethereum.github.io/consensus-specs/ssz/simple-serialize) library for Ethereum consensus, written in Rust.

Built for `no_std` from day one — runs in zkVMs, WASM, and embedded targets. Faster than Lighthouse on every benchmark. Fuzz-tested against the reference implementation.

## Performance

Benchmarked against [Lighthouse](https://github.com/sigp/lighthouse) (`ethereum_ssz` + `tree_hash`), `--release` with thin LTO.

### Apple M3 Max (ARM)

| Operation | libssz | Lighthouse | Speedup |
|-----------|--------|-----------|---------|
| Encode `BeaconBlockHeader` | 13.4 ns | 110 ns | **8.2x** |
| Encode `Vec<u64>` (100K) | 10.3 µs | 55.6 µs | **5.4x** |
| Encode `Vec<u64>` (1K) | 117 ns | 433 ns | **3.7x** |
| Encode `[u8; 96]` | 12.1 ns | 16.1 ns | **1.3x** |
| Decode `BeaconBlockHeader` | 12.6 ns | 12.2 ns | ~1x |
| Decode `Vec<u64>` (1K) | 747 ns | 1.22 µs | **1.6x** |
| HashTreeRoot `[u8; 32]` | 3.59 ns | 3.60 ns | ~1x |

### AMD Ryzen 9 9950X3D (x86_64)

| Operation | libssz | Lighthouse | Speedup |
|-----------|--------|-----------|---------|
| Encode `BeaconBlockHeader` | 10.1 ns | 68.3 ns | **6.7x** |
| Encode `Vec<u64>` (100K) | 9.44 µs | 28.4 µs | **3.0x** |
| Encode `Vec<u64>` (1K) | 54.1 ns | 315 ns | **5.8x** |
| Encode `u64` | 3.40 ns | 11.0 ns | **3.2x** |
| Decode `BeaconBlockHeader` | 9.15 ns | 7.32 ns | ~1x |
| Decode `Vec<u64>` (1K) | 518 ns | 813 ns | **1.6x** |
| Decode `Vec<u64>` (100K) | 24.1 µs | 55.0 µs | **2.3x** |
| HashTreeRoot `[u8; 32]` | 2.80 ns | 2.80 ns | ~1x |

libssz wins or ties on every benchmark across both platforms. Full results: `cargo bench --bench differential`.

<details>
<summary>How</summary>

- **All-fixed containers** bypass `ContainerEncoder`/`ContainerDecoder` entirely — the derive macro generates direct field-by-field append/decode when all fields are fixed-size, eliminating heap allocations and offset bookkeeping
- **Bulk memcpy for integer vectors** — `Vec<u64>` encoding reinterprets the slice as bytes on little-endian platforms, replacing 100K individual `extend_from_slice` calls with a single copy
- **Aggressive inlining** — `#[inline(always)]` on all trait impls that cross crate boundaries

</details>

## `no_std` Support

libssz is built from the ground up for `no_std + alloc`. Every crate — encoding, decoding, Merkleization, derive macros, bounded collections — works without the standard library. This makes it suitable for:

- **zkVMs** — prove Ethereum state transitions inside SP1, RISC Zero, or any STARK/SNARK VM
- **WASM** — run in browsers or light clients compiled to `wasm32-unknown-unknown`
- **Embedded** — ARM Cortex-M and other targets with a global allocator

CI verifies `no_std` compilation against `thumbv7m-none-eabi` on every commit.

```toml
[dependencies]
ssz        = { version = "0.1", default-features = false, features = ["alloc"] }
ssz-types  = { version = "0.1", default-features = false, features = ["alloc"] }
ssz-merkle = { version = "0.1", default-features = false, features = ["alloc"] }
ssz-derive = "0.1"  # proc-macro, no std/alloc distinction
```

```rust
#![no_std]
extern crate alloc;

use ssz::{SszEncode, SszDecode};

fn encode_slot(slot: u64) -> alloc::vec::Vec<u8> {
    slot.to_ssz()
}

fn decode_slot(bytes: &[u8]) -> Result<u64, ssz::DecodeError> {
    u64::from_ssz_bytes(bytes)
}
```

Features propagate through dependencies — `ssz-types = { features = ["alloc"] }` automatically enables `ssz/alloc` and `ssz-merkle/alloc`.

## Quick Start

```rust
use ssz::{SszEncode, SszDecode};

let value: u64 = 42;
let encoded = value.to_ssz();
let decoded = u64::from_ssz_bytes(&encoded).unwrap();
assert_eq!(decoded, 42);
```

### Derive Macros

```rust
use ssz_derive::{SszEncode, SszDecode, HashTreeRoot};
use ssz::{SszEncode, SszDecode};
use ssz_merkle::HashTreeRoot;

#[derive(SszEncode, SszDecode, HashTreeRoot)]
struct BeaconBlockHeader {
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
}

let header = BeaconBlockHeader {
    slot: 1,
    proposer_index: 0,
    parent_root: [0u8; 32],
    state_root: [0u8; 32],
    body_root: [0u8; 32],
};

let bytes = header.to_ssz();
let decoded = BeaconBlockHeader::from_ssz_bytes(&bytes).unwrap();
let root = header.hash_tree_root();
```

### Bounded Collections

```rust
use ssz_types::{SszVector, SszList, Bitvector, Bitlist};

// Vector: exactly 4 elements
let v = SszVector::<u64, 4>::try_from(vec![1, 2, 3, 4]).unwrap();

// List: at most 1024 elements
let mut l = SszList::<u64, 1024>::default();
l.push(42).unwrap();

// Bitvector: exactly 8 bits
let bv = Bitvector::<8>::default();

// Bitlist: at most 64 bits
let mut bl = Bitlist::<64>::default();
bl.push(true).unwrap();
```

### Union Types

```rust
use ssz_derive::{SszEncode, SszDecode, HashTreeRoot};

#[derive(SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
enum ExecutionPayload {
    Bellatrix(BellatrixPayload),
    Capella(CapellaPayload),
    Deneb(DenebPayload),
}
```

## Crates

| Crate | Description |
|-------|-------------|
| [`ssz`](crates/ssz) | Core `SszEncode` / `SszDecode` traits, primitive and container impls |
| [`ssz-types`](crates/ssz-types) | Bounded collections: `SszVector`, `SszList`, `Bitvector`, `Bitlist` |
| [`ssz-merkle`](crates/ssz-merkle) | `HashTreeRoot` trait, `merkleize`, precomputed zero hashes |
| [`ssz-derive`](crates/ssz-derive) | `#[derive(SszEncode, SszDecode, HashTreeRoot)]` |

Dependency graph: `ssz-derive` → `ssz-merkle` → `ssz` ← `ssz-types`

## Supported Types

| SSZ type | Rust type | Encode | Decode | HashTreeRoot |
|----------|-----------|--------|--------|-------------|
| `bool` | `bool` | Y | Y | Y |
| `uint8`..`uint128` | `u8`..`u128` | Y | Y | Y |
| `Bytes4`..`Bytes96` | `[u8; N]` | Y | Y | Y |
| `Vector[T, N]` | `SszVector<T, N>` | Y | Y | Y |
| `List[T, N]` | `SszList<T, N>` | Y | Y | Y |
| `Bitvector[N]` | `Bitvector<N>` | Y | Y | Y |
| `Bitlist[N]` | `Bitlist<N>` | Y | Y | Y |
| Container | `struct` + derive | Y | Y | Y |
| Union | `enum` + `#[ssz(enum_behaviour = "union")]` | Y | Y | Y |
| Transparent | `struct` + `#[ssz(transparent)]` | Y | Y | Y |

## Testing

```sh
make test          # unit + integration tests
make test-alloc    # no_std + alloc only
make fuzz-quick    # 10s smoke fuzz per target (19 targets)
make bench         # criterion benchmarks
make ci            # full CI pipeline locally
```

The library is differential-fuzz-tested against Lighthouse across 19 fuzz targets, run nightly in CI.

## Documentation

- [Architecture](docs/architecture.md) — crate layout, dependency graph, design rationale
- [Technical Design](docs/technical-design.md) — trait design, encoding/decoding algorithms
- [SSZ Spec Summary](docs/ssz-spec-summary.md) — concise reference of the spec as implemented

## License

Licensed under either of

- [Apache License, Version 2.0](LICENSE-APACHE)
- [MIT License](LICENSE-MIT)

at your option.
