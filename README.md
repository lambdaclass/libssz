# libssz

A fast, zkVM-friendly [Simple Serialize (SSZ)](https://ethereum.github.io/consensus-specs/ssz/simple-serialize) library for Ethereum consensus.

`no_std + alloc` from day one. Up to 2.5x faster than Lighthouse on BeaconState encode and decode. Validated against 62,489 official Ethereum consensus spec test cases across all 9 forks (phase0 through eip7805). Fuzz-tested against both reference implementations.

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
| `u64` | 3.40 ns | 11.1 ns | 11.0 ns | **3.3x** | **3.2x** |
| `[u8; 32]` | 3.49 ns | 11.3 ns | 501 ns | **3.2x** | **144x** |
| `BeaconBlockHeader` | 10.1 ns | 77.5 ns | 1.52 µs | **7.7x** | **150x** |
| `Vec<u64>` (1K) | 66.8 ns | 327 ns | 22.5 µs | **4.9x** | **337x** |
| `Vec<u64>` (100K) | 9.54 µs | 30.0 µs | 2.27 ms | **3.1x** | **238x** |

#### Decode

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `u64` | 312 ps | 312 ps | 358 ps | ~1x | ~1x |
| `[u8; 32]` | 3.1 ns | 3.3 ns | 51 ns | ~1x | **16x** |
| `BeaconBlockHeader` | 9.15 ns | 7.33 ns | 189 ns | 0.8x | **21x** |
| `Vec<u64>` (1K) | 609 ns | 799 ns | 522 ns | **1.3x** | 0.9x |
| `Vec<u64>` (100K) | 42.7 µs | 60.3 µs | 33.7 µs | **1.4x** | 0.8x |

#### BeaconState (21 fields, variable-length)

| Benchmark | Validators | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|-----------|-----------|--------|------------|--------|---------------|-----------|
| Encode | 16K | 139 µs | 170 µs | 70.0 ms | **1.2x** | **503x** |
| Encode | 100K | 433 µs | 854 µs | 185 ms | **2.0x** | **427x** |
| Encode | 300K | 3.54 ms | 6.53 ms | 475 ms | **1.8x** | **134x** |
| Encode | 1M | 11.4 ms | 24.3 ms | 1.46 s | **2.1x** | **128x** |
| Decode | 16K | 76 µs | 190 µs | 6.80 ms | **2.5x** | **89x** |
| Decode | 100K | 335 µs | 849 µs | 19.7 ms | **2.5x** | **59x** |
| Decode | 300K | 3.09 ms | 4.04 ms | 52.9 ms | **1.3x** | **17x** |
| Decode | 1M | 11.1 ms | 14.3 ms | 167 ms | **1.3x** | **15x** |

#### Hash Tree Root

| Type | libssz | Lighthouse | ssz_rs | vs Lighthouse | vs ssz_rs |
|------|--------|------------|--------|---------------|-----------|
| `bool` | 2.3 ns | 2.2 ns | 2.3 ns | ~1x | ~1x |
| `u64` | 2.4 ns | 2.1 ns | 31 ns | ~1x | **13x** |
| `[u8; 32]` | 2.80 ns | 2.80 ns | 57.8 ns | ~1x | **21x** |

libssz beats Lighthouse on both BeaconState encode and decode at every validator count, and dominates on primitives and vectors. Full results: `cargo bench --bench differential`.

<details>
<summary>How</summary>

- **Direct-write `ContainerEncoder`** — variable data writes directly to the output buffer with no intermediate allocation. Fixed fields are patched in-place into a pre-allocated region. Eliminates the double-write that a separate variable buffer would cause
- **All-fixed containers** bypass `ContainerEncoder`/`ContainerDecoder` entirely — the derive macro generates direct field-by-field append/decode, eliminating heap allocations and offset bookkeeping
- **Inlined bulk encode/decode** — the derive macro generates `ssz_append_fixed_slice` and `ssz_decode_fixed_vec` overrides that inline per-field operations directly into the loop body, skipping per-item struct-level length checks
- **Bulk memcpy for `[u8; N]` and integers** — both encode and decode use a single memcpy on little-endian platforms instead of per-element iteration
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
use ssz_types::{SszVector, SszList, SszBitvector, SszBitlist};

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
| [`ssz-types`](crates/ssz-types) | Bounded collections: `SszVector`, `SszList`, `SszBitvector`, `SszBitlist`, `ProgressiveList`, `ProgressiveBitlist` |
| [`ssz-merkle`](crates/ssz-merkle) | `HashTreeRoot` trait, `merkleize`, `merkleize_progressive`, precomputed zero hashes |
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
