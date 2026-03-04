# Technical design

## Trait design

### SszEncode -- infallible encoding

```rust
pub trait SszEncode {
    fn is_fixed_size() -> bool;
    fn fixed_size() -> usize;
    fn encoded_len(&self) -> usize;
    fn ssz_append(&self, buf: &mut Vec<u8>);
    fn to_ssz(&self) -> Vec<u8>;  // default impl
}
```

**Rationale: encoding is infallible.** All validation happens at type construction time (e.g., `SszVector::try_from` rejects wrong-length vectors). By the time a value exists, it is always valid SSZ, so `ssz_append` returns nothing -- no `Result`, no panics.

`ssz_append` takes `&mut Vec<u8>` rather than returning a new allocation. This lets callers reuse a single buffer across many fields (which is exactly what `ContainerEncoder` does).

`to_ssz` provides a convenience wrapper that allocates a pre-sized buffer using `encoded_len`.

`is_fixed_size` and `fixed_size` are associated functions (not methods) because they describe the type, not a value. The decoder needs these to parse the fixed part of containers without having an instance.

### SszDecode -- fallible decoding

```rust
pub trait SszDecode: Sized {
    fn is_fixed_size() -> bool;
    fn fixed_size() -> usize;
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError>;
}
```

**Rationale: decoding is fallible.** Untrusted input can violate any constraint: wrong length, invalid boolean byte, out-of-bounds offset, non-monotonic offsets. Every decode returns `Result<Self, DecodeError>`.

`from_ssz_bytes` takes `&[u8]` (a borrowed slice) rather than consuming a buffer. This enables zero-copy workflows where the caller owns the buffer and the decoded types borrow from it (though the current basic types copy into owned values).

### HashTreeRoot -- infallible hashing

```rust
pub trait HashTreeRoot {
    fn hash_tree_root(&self) -> [u8; 32];
}
```

Like encoding, hashing is infallible. A well-typed value always produces a valid 32-byte Merkle root.

## SSZ type mapping

| SSZ spec type | Rust type | Fixed/Variable | Size |
|---------------|-----------|----------------|------|
| `boolean` | `bool` | Fixed | 1 byte |
| `uint8` | `u8` | Fixed | 1 byte |
| `uint16` | `u16` | Fixed | 2 bytes |
| `uint32` | `u32` | Fixed | 4 bytes |
| `uint64` | `u64` | Fixed | 8 bytes |
| `uint128` | `u128` | Fixed | 16 bytes |
| `uint256` | `[u8; 32]` | Fixed | 32 bytes |
| `Bytes4`, `Bytes20`, etc. | `[u8; N]` | Fixed | N bytes |
| `Vector[T, N]` | `SszVector<T, N>` | Fixed iff T is fixed | N * size(T) or variable |
| `List[T, N]` | `SszList<T, N>` | Variable | depends on content |
| `Bitvector[N]` | `Bitvector<N>` | Fixed | ceil(N / 8) bytes |
| `Bitlist[N]` | `Bitlist<N>` | Variable | ceil(len / 8) + 1 bytes |
| Container | Named struct | Fixed iff all fields fixed | sum of field sizes |

## Serialization algorithm

SSZ serialization splits every composite type into a **fixed part** and a **variable part**.

### Fixed-size types

Encoded directly as their byte representation:
- `bool`: `0x00` (false) or `0x01` (true)
- Integers: little-endian bytes
- Byte arrays: raw bytes

### Variable-size types (Vec, List)

For a list of fixed-size elements, just concatenate their encodings.

For a list of variable-size elements:

```
┌──────────────────────────┬───────────────────────────┐
│       Fixed part         │      Variable part        │
│  (offsets, 4 bytes each) │  (concatenated data)      │
├──────────────────────────┼───────────────────────────┤
│ offset[0] │ offset[1] │ ...  │ data[0] │ data[1] │ ...   │
└──────────────────────────┴───────────────────────────┘
```

Each offset is a 4-byte little-endian `u32` pointing to the start of that element's data, measured from the beginning of the serialized output.

### Container encoding

A container (struct) interleaves fixed fields and offset placeholders:

```
┌─────────────────────────────────────────┬──────────────────────────┐
│              Fixed part                 │      Variable part       │
│  fixed fields inline, offsets for var   │  var field data          │
├─────────────────────────────────────────┼──────────────────────────┤
│ field_a (4B) │ offset_b (4B) │ field_c (2B) │ data_b (3B)        │
└─────────────────────────────────────────┴──────────────────────────┘
```

`ContainerEncoder` implements this in two passes:
1. **Append pass:** `append_fixed` writes field bytes directly. `append_variable` writes a 4-byte placeholder and stashes the encoded data.
2. **Finalize:** patches each placeholder with the real offset (fixed_part_len + cumulative variable data), then writes fixed part followed by variable part.

Example for `{ a: u32, b: Vec<u8>, c: u16 }` with values `(42, [0xAA, 0xBB, 0xCC], 1000)`:

```
Byte:  0  1  2  3  4  5  6  7  8  9  10 11 12
       ├─ a ──────┤  ├─ off_b ─┤  ├─ c ─┤  ├─ b data ─┤
       42 00 00 00   0A 00 00 00   E8 03    AA BB CC
```

Offset `0x0A = 10` because the fixed part is 4 + 4 + 2 = 10 bytes.

## Deserialization algorithm

### Fixed-size types

Validate that `bytes.len() == fixed_size()`, then read directly.

### Variable-size lists

For fixed-size elements: validate `bytes.len() % item_size == 0`, then chunk and decode.

For variable-size elements:
1. Read the first offset to determine the number of items: `num_items = first_offset / 4`.
2. Validate `first_offset % 4 == 0` (offsets must be aligned).
3. Read all `num_items` offsets. Validate monotonically increasing and within bounds.
4. Slice the variable data region using consecutive offset pairs. The last item extends to `bytes.len()`.
5. Decode each slice independently.

### Container decoding

`ContainerDecoder` processes fields in declaration order:

1. `new(bytes, fixed_part_len)` -- validate minimum length.
2. For each field in order:
   - Fixed field: `decode_fixed::<T>()` -- reads `T::fixed_size()` bytes at cursor.
   - Variable field: `read_variable_offset()` -- reads 4-byte offset, advances cursor.
3. After the fixed part, call `decode_variable::<T>()` for each variable field (in order). Each call slices from `offsets[i]` to `offsets[i+1]` (or `bytes.len()` for the last).
4. For all-fixed containers, `finish_fixed()` verifies no trailing bytes.

### Offset validation

Offsets are validated at multiple levels:
- Must not exceed `bytes.len()` (`OffsetOutOfBounds`)
- Must be monotonically non-decreasing (`OffsetsAreNotMonotonicallyIncreasing`)
- First offset must be a multiple of `BYTES_PER_LENGTH_OFFSET` (`InvalidFirstOffset`)

## Merkleization algorithm

SSZ Merkleization converts any value into a 32-byte Merkle root using SHA-256.

### Basic types

Serialize to bytes, right-pad with zeros to 32 bytes. This single chunk is the hash tree root.

### Containers

1. Compute `hash_tree_root` of each field.
2. Use these roots as leaf chunks.
3. Merkleize the chunk list.

### Vectors and lists of basic types (packing)

1. Serialize all elements contiguously.
2. Split into 32-byte chunks, zero-padding the last chunk if needed.
3. Merkleize the chunks.
4. For lists: `mix_in_length(root, length)` where `mix_in_length(root, len) = hash(root || len_as_32_byte_le)`.

### Bitvectors and bitlists

1. Pack bits into bytes (little-endian bit ordering).
2. Split into 32-byte chunks.
3. Merkleize with `limit = ceil(N / 256)` chunks.
4. For bitlists: `mix_in_length(root, length)`.

### The merkleize function

```
merkleize(chunks, limit):
    depth = ceil(log2(limit))      // or 0 if limit <= 1
    pad chunks to `limit` using ZERO_HASHES[0]  (virtual, not materialized)
    for level in 0..depth:
        hash pairs: chunk[2i] || chunk[2i+1] -> parent[i]
        use ZERO_HASHES[level] for missing right siblings
    return root
```

**Virtual padding:** rather than allocating `limit` chunks, the implementation uses precomputed `ZERO_HASHES[level]` for any subtree that would be all zeros. This keeps memory usage proportional to the actual number of non-zero chunks.

### Zero hash table

`ZERO_HASHES` is a static array of 65 entries (depth 0 through 64), computed at build time by `ssz-merkle/build.rs`:

```
ZERO_HASHES[0] = [0u8; 32]
ZERO_HASHES[i] = SHA256(ZERO_HASHES[i-1] || ZERO_HASHES[i-1])
```

Build-time computation avoids both runtime cost and `lazy_static` / `once_cell` dependencies.

## Performance design

### Allocation avoidance

- `ssz_append(&self, buf: &mut Vec<u8>)` writes into a caller-provided buffer, avoiding per-field allocations.
- `ContainerEncoder` accumulates the fixed part in a single buffer and patches offsets in place.
- `encoded_len()` enables pre-allocation: `Vec::with_capacity(self.encoded_len())`.

### Inline strategy

All trait methods on basic types are `#[inline(always)]`. For primitives like `u64::ssz_append`, the entire implementation is a single `extend_from_slice` call -- any call overhead would dominate.

### SmallVec

`smallvec` is a dependency for stack-allocating small buffers (e.g., offset lists for containers with few variable fields), avoiding heap allocation in the common case.

### Precomputed zero hashes

Build-time computation of `ZERO_HASHES` eliminates 64 SHA-256 hash calls from the hot path. The table is a static array with no initialization cost.

## no_std strategy

The library targets `no_std + alloc` as the minimum requirement:

```toml
[features]
default = ["std"]
std = ["alloc"]
alloc = []
```

- **`alloc`**: enables `Vec`, `String`, and other heap types via `extern crate alloc`. Required because SSZ serialization produces variable-length byte sequences.
- **`std`**: additionally enables `Display` / `Error` impls and any other std-only functionality.
- Without either feature, the crate provides only the trait definitions (no implementations that need allocation).

Each crate in the workspace propagates feature flags to `ssz`:

```toml
# ssz-types/Cargo.toml
[features]
std = ["alloc", "ssz/std"]
alloc = ["ssz/alloc"]
```

## Error handling

### DecodeError

A flat enum with descriptive variants:

| Variant | Cause |
|---------|-------|
| `InvalidByteLength` | Input length doesn't match expected (e.g., list not divisible by item size) |
| `InvalidFixedLength` | Fixed-size type received wrong byte count |
| `OffsetOutOfBounds` | An offset points past the input buffer |
| `OffsetsAreNotMonotonicallyIncreasing` | Variable-length offsets go backward |
| `InvalidFirstOffset` | First offset is not a valid multiple of 4 |
| `InvalidBooleanByte` | Boolean byte is not 0 or 1 |
| `ExtraBytesRemaining` | Unconsumed trailing bytes |
| `EmptyInput` | Zero bytes when input was required |
| `InvalidUnionSelector` | Union selector byte out of range |
| `ExcessBitsNotZero` | Bitfield padding bits are set |
| `MissingDelimiterBit` | Bitlist missing its length delimiter |
| `AdditionalBytes` | All-fixed container has trailing bytes |

Implements `Display` and `Error` only under `std` (behind feature gate).

### TypeError

Used by `ssz-types` for construction-time validation:

| Variant | Cause |
|---------|-------|
| `InvalidLength` | Wrong element count for a `Vector` |
| `OverCapacity` | Too many elements for a `List` or `Bitlist` |
| `Custom` | Freeform message (std only) |

### Philosophy

Errors are data, not strings. Each variant carries the numeric values needed to diagnose the problem (expected vs. got, offset value, etc.). This makes errors machine-readable and testable with `assert_eq!`.

## Comparison with other libraries

| Aspect | libssz | sigp/ethereum_ssz | ssz-rs |
|--------|--------|--------------------|--------|
| Bounded types | Const generics | typenum | typenum |
| no_std | `no_std + alloc` | `std` only | `no_std + alloc` |
| Merkleization | Separate crate | Separate crate (eth2_hashing) | Integrated |
| Derive macros | Separate crate | Separate crate | Integrated |
| Zero hashes | Build-time precomputed | `lazy_static` | Computed at init |
| Error types | Flat enum | Flat enum | Flat enum |
| Hash function | sha2 crate | ring / sha2 | sha2 |
