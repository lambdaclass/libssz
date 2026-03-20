# libssz

A fast, zkVM-friendly [Simple Serialize (SSZ)](https://ethereum.github.io/consensus-specs/ssz/simple-serialize) library for Ethereum consensus.

`no_std + alloc` from day one. Up to 2.9x faster than Lighthouse on BeaconState encode and decode. Validated against 62,489 official Ethereum consensus spec test cases across all 9 forks (phase0 through eip7805). Fuzz-tested against both reference implementations.

## Performance

Benchmarked against [Lighthouse](https://github.com/sigp/lighthouse) (`ethereum_ssz` + `tree_hash`) and [ssz_rs](https://github.com/ralexstokes/ssz-rs) v0.9, `--release` with thin LTO.

### Apple M3 Max (ARM)

#### Encode

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `bool` | 214 ps | 3.9 ns | 29 ns | **18x** | **135x** |
| `u64` | 235 ps | 4.0 ns | 29 ns | **17x** | **123x** |
| `[u8; 32]` | 4.1 ns | 4.2 ns | 30 ns | ~1x | **7.3x** |
| `BeaconBlockHeader` | 13.7 ns | 113 ns | 1.8 µs | **8.2x** | **131x** |
| `Vec<u64>` (1K) | 118 ns | 433 ns | 14 µs | **3.7x** | **119x** |
| `Vec<u64>` (100K) | 10.4 µs | 56 µs | 1.5 ms | **5.4x** | **144x** |

#### Decode

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `bool` | 430 ps | 430 ps | 432 ps | ~1x | ~1x |
| `u64` | 461 ps | 461 ps | 480 ps | ~1x | ~1x |
| `[u8; 32]` | 4.1 ns | 3.8 ns | 66 ns | ~1x | **16x** |
| `BeaconBlockHeader` | 12.7 ns | 12.3 ns | 207 ns | ~1x | **16x** |
| `Vec<u64>` (1K) | 123 ns | 1.23 µs | 780 ns | **10x** | **6.3x** |
| `Vec<u64>` (100K) | 10.3 µs | 154 µs | 112 µs | **15x** | **10.9x** |

#### BeaconState (21 fields, variable-length)

| Benchmark | Validators | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|-----------|-----------|--------|------------|--------|---------------|-----------|
| Encode | 16K | 808 µs | 756 µs | 75.1 ms | ~1x | **93x** |
| Encode | 100K | 654 µs | 5.61 ms | 215 ms | **8.6x** | **329x** |
| Encode | 300K | 11.9 ms | 18.0 ms | 551 ms | **1.5x** | **46x** |
| Encode | 1M | 5.67 ms | 19.0 ms | 1.73 s | **3.4x** | **305x** |
| Decode | 16K | 123 µs | 237 µs | 9.16 ms | **1.9x** | **74x** |
| Decode | 100K | 539 µs | 804 µs | 28.4 ms | **1.5x** | **53x** |
| Decode | 300K | 1.51 ms | 2.23 ms | 76.1 ms | **1.5x** | **50x** |
| Decode | 1M | 4.94 ms | 7.22 ms | 230 ms | **1.5x** | **47x** |

#### Hash Tree Root

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `bool` | 3.1 ns | 3.2 ns | 3.2 ns | ~1x | ~1x |
| `u64` | 3.1 ns | 3.2 ns | 48.6 ns | ~1x | **15.7x** |
| `[u8; 32]` | 3.6 ns | 3.6 ns | 88.3 ns | ~1x | **24.5x** |

### AMD Ryzen 9 9950X3D (x86_64)

#### Encode

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `u64` | 3.39 ns | 11.0 ns | 11.1 ns | **3.2x** | **3.3x** |
| `[u8; 32]` | 3.47 ns | 11.1 ns | 539 ns | **3.2x** | **155x** |
| `BeaconBlockHeader` | 10.1 ns | 84.2 ns | 1.71 µs | **8.4x** | **170x** |
| `Vec<u64>` (1K) | 58.6 ns | 400 ns | 23.9 µs | **6.8x** | **407x** |
| `Vec<u64>` (100K) | 9.20 µs | 35.8 µs | 2.36 ms | **3.9x** | **257x** |

#### Decode

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `u64` | 315 ps | 317 ps | 317 ps | ~1x | ~1x |
| `[u8; 32]` | 3.2 ns | 3.4 ns | 72 ns | ~1x | **23x** |
| `BeaconBlockHeader` | 8.96 ns | 7.08 ns | 196 ns | 0.8x | **22x** |
| `Vec<u64>` (1K) | 55.7 ns | 843 ns | 591 ns | **15x** | **11x** |
| `Vec<u64>` (100K) | 9.24 µs | 59.7 µs | 31.8 µs | **6.5x** | **3.4x** |

#### BeaconState (21 fields, variable-length)

| Benchmark | Validators | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|-----------|-----------|--------|------------|--------|---------------|-----------|
| Encode | 16K | 148 µs | 160 µs | 74.9 ms | ~1x | **506x** |
| Encode | 100K | 450 µs | 773 µs | 201 ms | **1.7x** | **446x** |
| Encode | 300K | 3.22 ms | 6.21 ms | 513 ms | **1.9x** | **159x** |
| Encode | 1M | 10.1 ms | 20.3 ms | 1.58 s | **2.0x** | **156x** |
| Decode | 16K | 72.5 µs | 185 µs | 6.83 ms | **2.6x** | **94x** |
| Decode | 100K | 313 µs | 908 µs | 20.5 ms | **2.9x** | **66x** |
| Decode | 300K | 2.74 ms | 4.18 ms | 55.2 ms | **1.5x** | **20x** |
| Decode | 1M | 9.27 ms | 13.9 ms | 172 ms | **1.5x** | **19x** |

#### Hash Tree Root

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `bool` | 2.24 ns | 2.20 ns | 2.30 ns | ~1x | ~1x |
| `u64` | 2.36 ns | 2.10 ns | 33.0 ns | ~1x | **14x** |
| `[u8; 32]` | 2.79 ns | 2.79 ns | 57.8 ns | ~1x | **21x** |

libssz beats Lighthouse on both BeaconState encode and decode at every validator count, and dominates on primitives and vectors. Full results: `cargo bench --bench differential`.

<details>
<summary>How</summary>

- **Direct-write `ContainerEncoder`** — variable data writes directly to the output buffer with no intermediate allocation. Fixed fields are patched in-place into a pre-allocated region. Eliminates the double-write that a separate variable buffer would cause
- **All-fixed containers** bypass `ContainerEncoder`/`ContainerDecoder` entirely — the derive macro generates direct field-by-field append/decode, eliminating heap allocations and offset bookkeeping
- **Inlined bulk encode/decode** — the derive macro generates `ssz_append_fixed_slice` and `ssz_decode_fixed_vec` overrides that inline per-field operations directly into the loop body, skipping per-item struct-level length checks
- **Bulk memcpy for `[u8; N]` and integers** — both encode and decode use a single memcpy on little-endian platforms instead of per-element iteration
- **Aggressive inlining** — `#[inline(always)]` on all trait impls that cross crate boundaries

</details>

## Getting Started

### Adding dependencies

Add libssz to your project from [crates.io](https://crates.io/crates/libssz):

```bash
cargo add libssz libssz-derive libssz-merkle libssz-types
```

Or add them to your `Cargo.toml`:

```toml
[dependencies]
libssz       = "0.1"
libssz-types = "0.1"
libssz-merkle = "0.1"
libssz-derive = "0.1"
```

For `no_std` environments (zkVMs, WASM, embedded), disable default features and enable `alloc`:

```toml
[dependencies]
libssz       = { version = "0.1", default-features = false, features = ["alloc"] }
libssz-types = { version = "0.1", default-features = false, features = ["alloc"] }
libssz-merkle = { version = "0.1", default-features = false, features = ["alloc"] }
libssz-derive = "0.1"
```

Features propagate through dependencies: `libssz-types = { features = ["alloc"] }` automatically enables `libssz/alloc` and `libssz-merkle/alloc`.

### Encode and decode

```rust
use libssz::{SszEncode, SszDecode};

let value: u64 = 42;
let encoded = value.to_ssz();
let decoded = u64::from_ssz_bytes(&encoded).unwrap();
assert_eq!(decoded, 42);
```

### Derive macros

```rust
use libssz_derive::{SszEncode, SszDecode, HashTreeRoot};
use libssz::{SszEncode, SszDecode};
use libssz_merkle::HashTreeRoot;

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

### Bounded collections

```rust
use libssz_types::{SszVector, SszList, SszBitvector, SszBitlist};

// Vector: exactly 4 elements
let v = SszVector::<u64, 4>::try_from(vec![1, 2, 3, 4]).unwrap();

// List: at most 1024 elements
let mut l = SszList::<u64, 1024>::default();
l.push(42).unwrap();

// Bitvector: exactly 8 bits
let bv = SszBitvector::<8>::default();

// Bitlist: at most 64 bits
let mut bl = SszBitlist::<64>::default();
bl.push(true).unwrap();
```

### Union types

```rust
use libssz_derive::{SszEncode, SszDecode, HashTreeRoot};

#[derive(SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
enum ExecutionPayload {
    Bellatrix(BellatrixPayload),
    Capella(CapellaPayload),
    Deneb(DenebPayload),
}
```

### `no_std` usage

Every crate works without the standard library. CI verifies `no_std` compilation against `thumbv7m-none-eabi` on every commit.

```rust
#![no_std]
extern crate alloc;

use libssz::{SszEncode, SszDecode};

fn encode_slot(slot: u64) -> alloc::vec::Vec<u8> {
    slot.to_ssz()
}

fn decode_slot(bytes: &[u8]) -> Result<u64, libssz::DecodeError> {
    u64::from_ssz_bytes(bytes)
}
```

## Crates

| Crate | Description |
|-------|-------------|
| [`libssz`](crates/ssz) | Core `SszEncode` / `SszDecode` traits, primitive and container impls |
| [`libssz-types`](crates/ssz-types) | Bounded collections: `SszVector`, `SszList`, `SszBitvector`, `SszBitlist`, `ProgressiveList`, `ProgressiveBitlist` |
| [`libssz-merkle`](crates/ssz-merkle) | `HashTreeRoot` trait, `merkleize`, `merkleize_progressive`, precomputed zero hashes |
| [`libssz-derive`](crates/ssz-derive) | `#[derive(SszEncode, SszDecode, HashTreeRoot)]` |

Dependency graph: `libssz-derive` → `libssz-merkle` → `libssz` ← `libssz-types`

## Supported Types

| SSZ type | Rust type | Encode | Decode | HashTreeRoot |
|----------|-----------|--------|--------|-------------|
| `bool` | `bool` | Y | Y | Y |
| `uint8`..`uint128` | `u8`..`u128` | Y | Y | Y |
| `Bytes4`..`Bytes96` | `[u8; N]` | Y | Y | Y |
| `Vector[T, N]` | `SszVector<T, N>` | Y | Y | Y |
| `List[T, N]` | `SszList<T, N>` | Y | Y | Y |
| `Bitvector[N]` | `SszBitvector<N>` | Y | Y | Y |
| `Bitlist[N]` | `SszBitlist<N>` | Y | Y | Y |
| `ProgressiveList[T]` | `ProgressiveList<T>` | Y | Y | Y |
| `ProgressiveBitlist` | `ProgressiveBitlist` | Y | Y | Y |
| Container | `struct` + derive | Y | Y | Y |
| Union | `enum` + `#[ssz(enum_behaviour = "union")]` | Y | Y | Y |
| Transparent | `struct` + `#[ssz(transparent)]` | Y | Y | Y |

## Testing

```sh
make test                  # unit + integration tests
make test-alloc            # no_std + alloc only
make download-spec-tests   # download consensus spec vectors (~1.25GB, cached)
make spec-tests            # run 62,489 spec test cases (downloads if needed)
make fuzz-quick            # 10s smoke fuzz per target (19 targets)
make bench                 # criterion benchmarks
make ci                    # full CI pipeline locally
```

### Consensus Spec Tests

The library is validated against the official [Ethereum consensus spec test vectors](https://github.com/ethereum/consensus-specs) (v1.6.1). This covers:

- **ssz_generic**: all SSZ primitive types, vectors, lists, bitfields, containers, progressive types (EIP-7916), and compatible unions — valid and invalid cases
- **ssz_static mainnet**: all Ethereum consensus types (BeaconState, BeaconBlock, Attestation, etc.) across 9 forks (phase0, altair, bellatrix, capella, deneb, electra, fulu, gloas, eip7805) at mainnet parameters
- **ssz_static minimal**: same types at minimal preset parameters

Each test case verifies decode, re-encode roundtrip, and hash tree root correctness.

### Fuzzing

Differential fuzz-tested against Lighthouse and ssz_rs across 19 fuzz targets, run nightly in CI.

## Documentation

- [Architecture](docs/architecture.md) — crate layout, dependency graph, design rationale
- [Technical Design](docs/technical-design.md) — trait design, encoding/decoding algorithms
- [SSZ Spec Summary](docs/ssz-spec-summary.md) — concise reference of the spec as implemented

## License

Licensed under either of

- [Apache License, Version 2.0](LICENSE-APACHE)
- [MIT License](LICENSE-MIT)

at your option.
