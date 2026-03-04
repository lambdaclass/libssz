# libssz

A full-spec [Simple Serialize (SSZ)](https://ethereum.github.io/consensus-specs/ssz/simple-serialize) library for Ethereum consensus, written in Rust.

<!-- Badges -->
<!-- [![no_std](https://img.shields.io/badge/no__std-compatible-blue)]() -->
<!-- [![crates.io](https://img.shields.io/crates/v/ssz.svg)](https://crates.io/crates/ssz) -->
<!-- [![docs.rs](https://docs.rs/ssz/badge.svg)](https://docs.rs/ssz) -->

## Features

- `no_std + alloc` compatible -- use in embedded, WASM, or zkVM targets
- Full SSZ spec coverage: encoding, decoding, and Merkleization
- Const-generic bounded collections (`Vector<T, N>`, `List<T, N>`, `Bitvector<N>`, `Bitlist<N>`)
- Derive macros for zero-boilerplate struct encoding, decoding, and hashing
- Precomputed zero hashes for efficient Merkleization
- Zero-copy decoding where possible, minimal allocations throughout

## Quick start

```rust
use ssz::{SszEncode, SszDecode};

// Encode a u64
let value: u64 = 42;
let encoded = value.to_ssz();
assert_eq!(encoded, vec![42, 0, 0, 0, 0, 0, 0, 0]);

// Decode it back
let decoded = u64::from_ssz_bytes(&encoded).unwrap();
assert_eq!(decoded, 42);
```

Encoding a container manually with `ContainerEncoder` / `ContainerDecoder`:

```rust
use ssz::{SszEncode, SszDecode, ContainerEncoder, ContainerDecoder};

// Container: { slot: u64, data: Vec<u8> }
let slot: u64 = 100;
let data: Vec<u8> = vec![0xAA, 0xBB];

// Encode
let mut encoder = ContainerEncoder::new();
encoder.append_fixed(&slot);       // u64 is fixed-size
encoder.append_variable(&data);    // Vec<u8> is variable-size
let mut buf = Vec::new();
encoder.finalize(&mut buf);

// Decode
let fixed_part_len = 8 + 4; // u64 (8 bytes) + offset (4 bytes)
let mut decoder = ContainerDecoder::new(&buf, fixed_part_len).unwrap();
let dec_slot: u64 = decoder.decode_fixed().unwrap();
decoder.read_variable_offset().unwrap();
let dec_data: Vec<u8> = decoder.decode_variable().unwrap();

assert_eq!(dec_slot, 100);
assert_eq!(dec_data, vec![0xAA, 0xBB]);
```

## Crate overview

| Crate | Description | Status |
|-------|-------------|--------|
| [`ssz`](crates/ssz) | Core `SszEncode`/`SszDecode` traits and primitive implementations | Ready |
| [`ssz-types`](crates/ssz-types) | Bounded collections: `SszVector`, `SszList`, `Bitvector`, `Bitlist` | In progress |
| [`ssz-merkle`](crates/ssz-merkle) | Merkleization: `HashTreeRoot`, `merkleize`, precomputed zero hashes | In progress |
| [`ssz-derive`](crates/ssz-derive) | Proc macros: `#[derive(SszEncode, SszDecode, HashTreeRoot)]` | Planned |

## Feature flags

| Flag | Default | Description |
|------|---------|-------------|
| `std` | Yes | Enables `std` support (implies `alloc`) |
| `alloc` | No | Enables `alloc` for `no_std` environments with a global allocator |

Each crate propagates feature flags to its dependencies (e.g., `ssz-types/std` enables `ssz/std`).

## Documentation

- [Architecture](docs/architecture.md) -- crate layout, dependency graph, design rationale
- [Technical design](docs/technical-design.md) -- trait design, algorithms, performance strategy
- [SSZ spec summary](docs/ssz-spec-summary.md) -- concise reference of the SSZ specification as implemented

## License

TBD
