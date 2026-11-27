//! A naive model of SSZ Merkleization and bitfield encoding, written from
//! the consensus-specs `simple-serialize.md` text.
//!
//! Everything here favours obviousness over speed: trees are materialized
//! to their full padded width and bits are packed one at a time. It uses
//! `sha2` directly and nothing from libssz, so a bug in libssz cannot also
//! be a bug in the model. Keep the limits passed to [`merkleize`] small.

use sha2::{Digest, Sha256};

pub type Chunk = [u8; 32];

pub const ZERO: Chunk = [0u8; 32];

pub fn hash_pair(a: &Chunk, b: &Chunk) -> Chunk {
    let mut hasher = Sha256::new();
    hasher.update(a);
    hasher.update(b);
    hasher.finalize().into()
}

/// `merkleize(chunks, limit)`: pad with zero chunks to
/// `next_pow_of_two(limit)` leaves (one leaf when the limit is 0) and hash
/// pairs level by level.
pub fn merkleize(chunks: &[Chunk], limit: usize) -> Chunk {
    assert!(
        chunks.len() <= limit,
        "test bug: {} chunks over limit {limit}",
        chunks.len()
    );
    assert!(
        limit <= 1 << 16,
        "test bug: limit {limit} too large to materialize"
    );
    let width = limit.next_power_of_two();
    let mut layer = chunks.to_vec();
    layer.resize(width, ZERO);
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len() / 2);
        let mut i = 0;
        while i < layer.len() {
            next.push(hash_pair(&layer[i], &layer[i + 1]));
            i += 2;
        }
        layer = next;
    }
    layer[0]
}

/// EIP-7916 `merkleize_progressive(chunks, num_leaves=1)`.
pub fn merkleize_progressive(chunks: &[Chunk]) -> Chunk {
    progressive_from(chunks, 1)
}

fn progressive_from(chunks: &[Chunk], num_leaves: usize) -> Chunk {
    if chunks.is_empty() {
        return ZERO;
    }
    let split = chunks.len().min(num_leaves);
    let left = merkleize(&chunks[..split], num_leaves);
    let right = progressive_from(&chunks[split..], num_leaves * 4);
    hash_pair(&left, &right)
}

/// Pack serialized bytes into chunks, right-padding the last one with zeros.
pub fn pack(bytes: &[u8]) -> Vec<Chunk> {
    let mut chunks = Vec::new();
    for (i, byte) in bytes.iter().enumerate() {
        if i % 32 == 0 {
            chunks.push(ZERO);
        }
        chunks.last_mut().expect("pushed above")[i % 32] = *byte;
    }
    chunks
}

/// Bits in little-endian bit order: bit `i` is bit `i % 8` of byte `i / 8`.
pub fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    let mut bytes = vec![0u8; bits.len().div_ceil(8)];
    for (i, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[i / 8] |= 1 << (i % 8);
        }
    }
    bytes
}

/// The serialization of a bitlist: its bits followed by a single 1 bit.
pub fn bitlist_encoding(bits: &[bool]) -> Vec<u8> {
    let mut with_delimiter = bits.to_vec();
    with_delimiter.push(true);
    bits_to_bytes(&with_delimiter)
}

pub fn mix_in_length(root: &Chunk, length: usize) -> Chunk {
    let mut length_chunk = ZERO;
    length_chunk[..8].copy_from_slice(&(length as u64).to_le_bytes());
    hash_pair(root, &length_chunk)
}

pub fn mix_in_selector(root: &Chunk, selector: u8) -> Chunk {
    let mut selector_chunk = ZERO;
    selector_chunk[0] = selector;
    hash_pair(root, &selector_chunk)
}

/// EIP-7495: mix in the `active_fields` bitvector, packed into one chunk.
pub fn mix_in_active_fields(root: &Chunk, active_fields: &[bool]) -> Chunk {
    assert!(
        active_fields.len() <= 256,
        "test bug: too many active fields"
    );
    let mut chunk = ZERO;
    let bytes = bits_to_bytes(active_fields);
    chunk[..bytes.len()].copy_from_slice(&bytes);
    hash_pair(root, &chunk)
}

/// The root of a basic value: its little-endian bytes in one chunk.
pub fn basic_root(le_bytes: &[u8]) -> Chunk {
    let mut chunk = ZERO;
    chunk[..le_bytes.len()].copy_from_slice(le_bytes);
    chunk
}

/// `List[uintN, limit]`, given the elements already serialized.
pub fn basic_list_root(serialized: &[u8], length: usize, limit: usize, elem_size: usize) -> Chunk {
    let chunk_limit = (limit * elem_size).div_ceil(32);
    mix_in_length(&merkleize(&pack(serialized), chunk_limit), length)
}

/// `Vector[uintN, length]`, given the elements already serialized.
pub fn basic_vector_root(serialized: &[u8], length: usize, elem_size: usize) -> Chunk {
    merkleize(&pack(serialized), (length * elem_size).div_ceil(32))
}

/// `Vector[byte, N]` (`ByteVector[N]`): a composite type, so it is its own
/// tree even when it fits in one chunk.
pub fn byte_vector_root(bytes: &[u8]) -> Chunk {
    basic_vector_root(bytes, bytes.len(), 1)
}

/// `List[T, limit]` of a composite `T`, given the element roots.
pub fn composite_list_root(roots: &[Chunk], limit: usize) -> Chunk {
    mix_in_length(&merkleize(roots, limit), roots.len())
}

/// `Vector[T, N]` of a composite `T`, given the element roots.
pub fn composite_vector_root(roots: &[Chunk]) -> Chunk {
    merkleize(roots, roots.len())
}

/// `Bitlist[limit]`.
pub fn bitlist_root(bits: &[bool], limit: usize) -> Chunk {
    let chunks = pack(&bits_to_bytes(bits));
    mix_in_length(&merkleize(&chunks, limit.div_ceil(256)), bits.len())
}

/// `Bitvector[N]`.
pub fn bitvector_root(bits: &[bool]) -> Chunk {
    merkleize(&pack(&bits_to_bytes(bits)), bits.len().div_ceil(256))
}

/// `ProgressiveList[uintN]`, given the elements already serialized.
pub fn progressive_basic_list_root(serialized: &[u8], length: usize) -> Chunk {
    mix_in_length(&merkleize_progressive(&pack(serialized)), length)
}

/// `ProgressiveBitlist`.
pub fn progressive_bitlist_root(bits: &[bool]) -> Chunk {
    let chunks = pack(&bits_to_bytes(bits));
    mix_in_length(&merkleize_progressive(&chunks), bits.len())
}
