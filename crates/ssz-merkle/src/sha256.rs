//! Default SHA-256 backend: the `sha2` crate, or `hashtree` with the `hashtree` feature.

use crate::{Node, Sha256Hasher};

/// Default SHA-256 hasher.
///
/// Merkle pairs are hashed by calling the SHA-256 compression function directly
/// on the 64-byte message and a constant padding block, skipping the
/// general-purpose `Digest` buffering. `sha2` selects CPU SHA instructions at
/// runtime (x86 SHA-NI, ARMv8 SHA2) and falls back to software otherwise.
///
/// With the `hashtree` feature, pairs are hashed by the
/// [`hashtree`](https://github.com/OffchainLabs/hashtree) library instead:
/// assembly specialized for 64-byte inputs that also hashes several pairs at
/// once (SHA-NI, AVX-512 x16, AVX2 x8, ARMv8 SHA2, NEON x4).
pub struct Sha2Hasher;

impl Sha256Hasher for Sha2Hasher {
    fn hash(&self, data: &[u8]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).into()
    }

    #[cfg(not(feature = "hashtree"))]
    fn hash_pairs(&self, pairs: &[[Node; 2]], out: &mut [Node]) {
        assert_eq!(pairs.len(), out.len(), "one output node per pair");
        for (pair, out) in pairs.iter().zip(out) {
            *out = hash_pair(pair);
        }
    }

    #[cfg(feature = "hashtree")]
    fn hash_pairs(&self, pairs: &[[Node; 2]], out: &mut [Node]) {
        // `hashtree_rs::hash` performs no length checks of its own.
        assert_eq!(pairs.len(), out.len(), "one output node per pair");
        if pairs.is_empty() {
            return;
        }
        // The C library selects its implementation lazily by writing a static
        // function pointer on first use; do that once, before any concurrent call.
        static INIT: std::sync::Once = std::sync::Once::new();
        INIT.call_once(|| {
            hashtree_rs::init();
        });
        hashtree_rs::hash(
            out.as_flattened_mut(),
            pairs.as_flattened().as_flattened(),
            pairs.len(),
        );
    }
}

/// SHA-256 initial hash value (FIPS 180-4, 5.3.3).
const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Padding for a 64-byte message, which always fills a block of its own:
/// `0x80`, zeros, then the message length in bits (512) as a big-endian `u64`.
const PADDING_BLOCK: [u8; 64] = {
    let mut block = [0u8; 64];
    block[0] = 0x80;
    block[62] = 0x02;
    block
};

/// SHA-256 of `pair[0] || pair[1]`, as two calls to the compression function.
#[cfg_attr(feature = "hashtree", allow(dead_code))]
#[inline]
fn hash_pair(pair: &[Node; 2]) -> Node {
    let mut message = [0u8; 64];
    message[..32].copy_from_slice(&pair[0]);
    message[32..].copy_from_slice(&pair[1]);

    let mut state = IV;
    sha2::block_api::compress256(&mut state, &[message, PADDING_BLOCK]);

    let mut digest = [0u8; 32];
    let (words, _) = digest.as_chunks_mut::<4>();
    for (bytes, word) in words.iter_mut().zip(state) {
        *bytes = word.to_be_bytes();
    }
    digest
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use sha2::{Digest, Sha256};

    /// Pairs whose bytes differ in every position and set high bits, so a
    /// misplaced word or byte-order slip changes the digest.
    fn sample_pairs(count: usize) -> Vec<[Node; 2]> {
        (0..count)
            .map(|i| {
                let mut pair = [[0u8; 32]; 2];
                for (j, byte) in pair.as_flattened_mut().iter_mut().enumerate() {
                    *byte = (i * 131 + j * 29 + 0x80) as u8;
                }
                pair
            })
            .collect()
    }

    fn digest(pair: &[Node; 2]) -> Node {
        Sha256::digest(pair.as_flattened()).into()
    }

    #[test]
    fn hash_pair_matches_digest() {
        for pair in sample_pairs(16) {
            assert_eq!(hash_pair(&pair), digest(&pair));
        }
    }

    /// Covers the batch path used by `merkleize`, including the `hashtree`
    /// backend when that feature is enabled, across every SIMD batch remainder.
    #[test]
    fn hash_pairs_matches_digest_for_every_count() {
        for count in 0..=33 {
            let pairs = sample_pairs(count);
            let mut out = alloc::vec![[0u8; 32]; count];
            Sha2Hasher.hash_pairs(&pairs, &mut out);
            for (i, (pair, node)) in pairs.iter().zip(&out).enumerate() {
                assert_eq!(*node, digest(pair), "pair {i} of {count}");
            }
        }
    }

    #[test]
    #[should_panic(expected = "one output node per pair")]
    fn hash_pairs_rejects_mismatched_output() {
        let pairs = sample_pairs(3);
        let mut out = [[0u8; 32]; 2];
        Sha2Hasher.hash_pairs(&pairs, &mut out);
    }
}
