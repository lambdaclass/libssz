# SSZ spec summary

A concise reference of the [SSZ specification](https://ethereum.github.io/consensus-specs/ssz/simple-serialize) as implemented in libssz.

## Types

### Basic types

Basic types have a fixed size and are serialized directly.

| Type | Size | Serialization |
|------|------|---------------|
| `boolean` | 1 byte | `0x00` = false, `0x01` = true. Any other value is invalid. |
| `uint8` | 1 byte | Little-endian |
| `uint16` | 2 bytes | Little-endian |
| `uint32` | 4 bytes | Little-endian |
| `uint64` | 8 bytes | Little-endian |
| `uint128` | 16 bytes | Little-endian |
| `uint256` | 32 bytes | Little-endian |

### Composite types

| Type | Fixed/Variable | Description |
|------|----------------|-------------|
| `Vector[T, N]` | Fixed iff T is fixed | Fixed-length homogeneous collection of exactly N elements |
| `List[T, N]` | Variable | Variable-length homogeneous collection of at most N elements |
| `Bitvector[N]` | Fixed | Fixed-length bit sequence of exactly N bits |
| `Bitlist[N]` | Variable | Variable-length bit sequence of at most N bits |
| Container | Fixed iff all fields fixed | Heterogeneous record with named fields |

## Serialization

### General rules

- All integers are little-endian.
- Offsets are 4-byte little-endian unsigned integers (`uint32`).
- The serialized form of a composite type has two regions: a **fixed part** and a **variable part**.

### Fixed-size types

Serialized as their raw byte representation, concatenated in field order.

### Variable-size composite types

The fixed part contains:
- For each fixed-size field/element: the serialized value inline.
- For each variable-size field/element: a 4-byte offset pointing into the variable part.

The variable part contains the serialized variable-size fields/elements concatenated in order.

Offsets are relative to the start of the serialized object (not the variable part).

### Vectors

- **Fixed-element vectors:** concatenate the serialization of each element.
- **Variable-element vectors:** write offsets in the fixed part, data in the variable part.

### Lists

Same encoding as vectors. The length is not explicitly encoded in the serialization -- it is inferred from the total byte length and element sizes (for fixed elements) or from the offset structure (for variable elements).

The maximum length `N` is not enforced during serialization. It is enforced at construction time by the type system.

### Bitvectors

Serialize N bits into `ceil(N / 8)` bytes. Bits are packed in little-endian bit order: bit `i` is stored at byte `i / 8`, bit position `i % 8`. Unused high bits in the last byte must be zero.

### Bitlists

Same bit packing as bitvectors, plus a **delimiter bit**: a `1` bit is appended after the last data bit to mark the boundary. This means a bitlist of length `L` serializes to `ceil((L + 1) / 8)` bytes. The decoder locates the highest set bit in the last byte to determine the actual length.

### Containers

Fields are serialized in declaration order. The container's fixed part is the concatenation of:
- Serialized value for each fixed-size field.
- 4-byte offset for each variable-size field.

The variable part follows with the serialized variable-size fields in order.

## Deserialization

### Fixed-size types

Validate that the input length equals the expected size, then read bytes directly.

### Variable-size lists (fixed elements)

Validate that `input.len() % element_size == 0`. Chunk by element size, decode each chunk.

### Variable-size lists (variable elements)

1. Read the first 4-byte offset to determine item count: `count = first_offset / 4`.
2. Validate `first_offset % 4 == 0`.
3. Read `count` offsets. Validate:
   - Monotonically non-decreasing.
   - Each offset <= `input.len()`.
4. Slice between consecutive offsets (last item extends to end of input).
5. Decode each slice.

### Containers

1. Compute the expected fixed-part length from the type definition.
2. Validate `input.len() >= fixed_part_len`.
3. Walk the fixed part: read fixed fields inline, read offsets for variable fields.
4. Validate offsets (monotonic, in bounds).
5. Decode variable fields from their slices.
6. For all-fixed containers, validate no trailing bytes.

## Merkleization

All Merkleization uses SHA-256 as the hash function. Chunks are always 32 bytes.

### hash_tree_root by type

| Type | Algorithm |
|------|-----------|
| Basic type | Serialize, right-pad to 32 bytes |
| Vector of basic | Pack serialized elements into 32-byte chunks, `merkleize(chunks, N_chunks)` |
| Vector of composite | `merkleize([hash_tree_root(elem) for elem], N)` |
| List of basic | Pack into chunks, `mix_in_length(merkleize(chunks, limit), length)` |
| List of composite | `mix_in_length(merkleize([hash_tree_root(elem) for elem], limit), length)` |
| Bitvector | Pack bits into chunks, `merkleize(chunks, ceil(N / 256))` |
| Bitlist | Pack bits into chunks, `mix_in_length(merkleize(chunks, limit), length)` |
| Container | `merkleize([hash_tree_root(field) for field])` |

Where:
- `limit` for lists: `ceil(N / elements_per_chunk)` for basic types, `N` for composite types
- `elements_per_chunk` = `32 / element_size` for basic types

### merkleize(chunks, limit)

1. If `limit == 0`, return `ZERO_HASHES[0]`.
2. Compute `depth = ceil(log2(limit))`.
3. Virtually pad `chunks` to `limit` entries with zero chunks.
4. Build the Merkle tree bottom-up, hashing pairs of siblings.
5. Missing subtrees use precomputed `ZERO_HASHES[level]`.
6. Return the root (single 32-byte hash).

### mix_in_length

```
mix_in_length(root, length) = SHA256(root || length_as_256bit_le)
```

The length is encoded as a 32-byte little-endian integer (only the first 8 bytes are non-zero for practical lengths).

### Zero hashes

```
ZERO_HASHES[0] = 0x0000...0000  (32 zero bytes)
ZERO_HASHES[i] = SHA256(ZERO_HASHES[i-1] || ZERO_HASHES[i-1])
```

Used for virtual padding in sparse Merkle trees. Precomputed at build time up to depth 64.

## Edge cases and constraints

- **Empty lists:** serialize to zero bytes. Decode produces an empty collection.
- **Empty variable-element lists:** serialize to zero bytes (no offsets, no data).
- **Boolean validation:** only `0x00` and `0x01` are valid. `0x02`..`0xFF` produce `InvalidBooleanByte`.
- **Bitlist delimiter:** a zero-length bitlist serializes to `[0x01]` (just the delimiter bit). An empty byte slice is invalid.
- **Bitvector excess bits:** unused high bits in the last byte must be zero; nonzero bits produce `ExcessBitsNotZero`.
- **Maximum offset:** offsets are `uint32`, so a single SSZ object cannot exceed 2^32 - 1 bytes (~4 GiB).
- **Container with zero fields:** not valid in the SSZ spec.
- **Union types:** supported via a 1-byte selector prefix. Selector `0` is `None`, selectors `1..=127` are type indices. Not yet implemented in libssz.

## References

- [SSZ Simple Serialize -- Ethereum Consensus Specs](https://ethereum.github.io/consensus-specs/ssz/simple-serialize)
- [SSZ Merkleization -- Ethereum Consensus Specs](https://ethereum.github.io/consensus-specs/ssz/merkle-proofs)
- [EIP-2982: Serenity Phase 0](https://eips.ethereum.org/EIPS/eip-2982)
