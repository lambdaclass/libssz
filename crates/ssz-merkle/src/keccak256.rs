//! Default Keccak-256 backend.
//!
//! A Merkle pair is a 64-byte message, which fits in a single Keccak-256 block
//! (the rate is 136 bytes), so each pair costs exactly one Keccak-f\[1600\]
//! permutation. The permutation is run directly on a state with the padding
//! already applied, and a batch of pairs runs several permutations at once in
//! SIMD lanes when the CPU supports it.

use crate::{MerkleHasher, Node};

/// Default Keccak-256 hasher.
///
/// This is the original Keccak-256 used by Ethereum's execution layer (`0x01`
/// padding), not NIST SHA3-256.
///
/// Merkle pairs are hashed with one Keccak-f\[1600\] permutation each, skipping
/// the general-purpose sponge. A batch of pairs runs several permutations at
/// once, choosing at runtime: AVX-512 (8 pairs), AVX2 (4) or the ARMv8 SHA3
/// extension (2). With AVX-512 a part-filled batch runs in SIMD too; with AVX2
/// or SHA3 a single leftover pair, like every pair on other CPUs, uses the
/// scalar permutation from the `keccak` crate.
pub struct KeccakHasher;

impl MerkleHasher for KeccakHasher {
    fn hash(&self, data: &[u8]) -> [u8; 32] {
        use sha3::{Digest, Keccak256};
        Keccak256::digest(data).into()
    }

    fn hash_pairs(&self, pairs: &[[Node; 2]], out: &mut [Node]) {
        assert_eq!(pairs.len(), out.len(), "one output node per pair");

        #[cfg(target_arch = "x86_64")]
        {
            if x86::has_avx512() {
                // SAFETY: the CPU supports AVX-512F.
                return unsafe { x86::hash_pairs_x8(pairs, out) };
            }
            if x86::has_avx2() {
                // SAFETY: the CPU supports AVX2.
                return unsafe { x86::hash_pairs_x4(pairs, out) };
            }
        }

        #[cfg(target_arch = "aarch64")]
        if aarch64::has_sha3() {
            // SAFETY: the CPU supports the SHA3 extension.
            return unsafe { aarch64::hash_pairs_x2(pairs, out) };
        }

        hash_pairs_scalar(pairs, out);
    }
}

/// Keccak padding of a 64-byte message, as state lanes: the `0x01` domain byte
/// goes at byte 64 (lane 8) and the final `0x80` at byte 135, the last byte of
/// the 136-byte rate (lane 16).
const PAD_LANE_8: u64 = 0x01;
const PAD_LANE_16: u64 = 0x80 << 56;

/// Keccak-f\[1600\] round constants (ι step).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

fn hash_pairs_scalar(pairs: &[[Node; 2]], out: &mut [Node]) {
    for (pair, out) in pairs.iter().zip(out) {
        *out = hash_pair(pair);
    }
}

/// Keccak-256 of `pair[0] || pair[1]`: one permutation of a pre-padded state.
#[inline]
fn hash_pair(pair: &[Node; 2]) -> Node {
    let mut state = [0u64; 25];
    let (words, _) = pair.as_flattened().as_chunks::<8>();
    for (lane, word) in state.iter_mut().zip(words) {
        *lane = u64::from_le_bytes(*word);
    }
    state[8] = PAD_LANE_8;
    state[16] = PAD_LANE_16;

    keccak::f1600(&mut state);

    let mut digest = [0u8; 32];
    let (bytes, _) = digest.as_chunks_mut::<8>();
    for (bytes, lane) in bytes.iter_mut().zip(&state) {
        *bytes = lane.to_le_bytes();
    }
    digest
}

/// Message words of up to `W` pairs, transposed so `words[i][k]` is word `i`
/// of pair `k`. Unused columns stay zero.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[inline(always)]
fn transpose_in<const W: usize>(pairs: &[[Node; 2]]) -> [[u64; W]; 8] {
    let mut words = [[0u64; W]; 8];
    for (k, pair) in pairs.iter().enumerate() {
        let (chunks, _) = pair.as_flattened().as_chunks::<8>();
        for (row, chunk) in words.iter_mut().zip(chunks) {
            row[k] = u64::from_le_bytes(*chunk);
        }
    }
    words
}

/// Write digests from the first four state lanes, where `lanes[i][k]` is lane
/// `i` of the state for pair `k`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[inline(always)]
fn transpose_out<const W: usize>(lanes: &[[u64; W]; 4], out: &mut [Node]) {
    for (k, node) in out.iter_mut().enumerate() {
        let (chunks, _) = node.as_chunks_mut::<8>();
        for (chunk, row) in chunks.iter_mut().zip(lanes) {
            *chunk = row[k].to_le_bytes();
        }
    }
}

/// Keccak-f\[1600\] on `$a: [V; 25]`, where each vector `V` holds the same lane
/// of several independent states. The vector operations come from
/// per-architecture macros, so every intrinsic call is expanded inside the
/// caller's `#[target_feature]` function and can be inlined:
///
/// - `xor5!(a, b, c, d, e)`: `a ^ b ^ c ^ d ^ e`
/// - `rol1_xor!(a, b)`: `a ^ b.rotate_left(1)`
/// - `xor_rotl!(a, d, N)`: `(a ^ d).rotate_left(N)` for a literal `N` in `0..64`
/// - `chi!(a, b, c)`: `a ^ (!b & c)`
/// - `xor_rc!(a, rc)`: `a ^ rc` in every lane
///
/// The tests check every backend against `sha3::Keccak256`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
macro_rules! keccak_f1600 {
    ($a:ident, $xor5:ident, $rol1_xor:ident, $xor_rotl:ident, $chi:ident, $xor_rc:ident) => {
        for &rc in &RC {
            // θ: column parities, then the correction for each column.
            let c0 = $xor5!($a[0], $a[5], $a[10], $a[15], $a[20]);
            let c1 = $xor5!($a[1], $a[6], $a[11], $a[16], $a[21]);
            let c2 = $xor5!($a[2], $a[7], $a[12], $a[17], $a[22]);
            let c3 = $xor5!($a[3], $a[8], $a[13], $a[18], $a[23]);
            let c4 = $xor5!($a[4], $a[9], $a[14], $a[19], $a[24]);
            let d0 = $rol1_xor!(c4, c1);
            let d1 = $rol1_xor!(c0, c2);
            let d2 = $rol1_xor!(c1, c3);
            let d3 = $rol1_xor!(c2, c4);
            let d4 = $rol1_xor!(c3, c0);

            // θ applied, then ρ (rotation) and π (lane permutation): lane
            // (X, Y) takes the old lane ((X + 3Y) mod 5, X).
            let b0 = $xor_rotl!($a[0], d0, 0);
            let b1 = $xor_rotl!($a[6], d1, 44);
            let b2 = $xor_rotl!($a[12], d2, 43);
            let b3 = $xor_rotl!($a[18], d3, 21);
            let b4 = $xor_rotl!($a[24], d4, 14);
            let b5 = $xor_rotl!($a[3], d3, 28);
            let b6 = $xor_rotl!($a[9], d4, 20);
            let b7 = $xor_rotl!($a[10], d0, 3);
            let b8 = $xor_rotl!($a[16], d1, 45);
            let b9 = $xor_rotl!($a[22], d2, 61);
            let b10 = $xor_rotl!($a[1], d1, 1);
            let b11 = $xor_rotl!($a[7], d2, 6);
            let b12 = $xor_rotl!($a[13], d3, 25);
            let b13 = $xor_rotl!($a[19], d4, 8);
            let b14 = $xor_rotl!($a[20], d0, 18);
            let b15 = $xor_rotl!($a[4], d4, 27);
            let b16 = $xor_rotl!($a[5], d0, 36);
            let b17 = $xor_rotl!($a[11], d1, 10);
            let b18 = $xor_rotl!($a[17], d2, 15);
            let b19 = $xor_rotl!($a[23], d3, 56);
            let b20 = $xor_rotl!($a[2], d2, 62);
            let b21 = $xor_rotl!($a[8], d3, 55);
            let b22 = $xor_rotl!($a[14], d4, 39);
            let b23 = $xor_rotl!($a[15], d0, 41);
            let b24 = $xor_rotl!($a[21], d1, 2);

            // χ along each row.
            $a[0] = $chi!(b0, b1, b2);
            $a[1] = $chi!(b1, b2, b3);
            $a[2] = $chi!(b2, b3, b4);
            $a[3] = $chi!(b3, b4, b0);
            $a[4] = $chi!(b4, b0, b1);
            $a[5] = $chi!(b5, b6, b7);
            $a[6] = $chi!(b6, b7, b8);
            $a[7] = $chi!(b7, b8, b9);
            $a[8] = $chi!(b8, b9, b5);
            $a[9] = $chi!(b9, b5, b6);
            $a[10] = $chi!(b10, b11, b12);
            $a[11] = $chi!(b11, b12, b13);
            $a[12] = $chi!(b12, b13, b14);
            $a[13] = $chi!(b13, b14, b10);
            $a[14] = $chi!(b14, b10, b11);
            $a[15] = $chi!(b15, b16, b17);
            $a[16] = $chi!(b16, b17, b18);
            $a[17] = $chi!(b17, b18, b19);
            $a[18] = $chi!(b18, b19, b15);
            $a[19] = $chi!(b19, b15, b16);
            $a[20] = $chi!(b20, b21, b22);
            $a[21] = $chi!(b21, b22, b23);
            $a[22] = $chi!(b22, b23, b24);
            $a[23] = $chi!(b23, b24, b20);
            $a[24] = $chi!(b24, b20, b21);

            // ι.
            $a[0] = $xor_rc!($a[0], rc);
        }
    };
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use super::{
        hash_pairs_scalar, transpose_in, transpose_out, Node, PAD_LANE_16, PAD_LANE_8, RC,
    };
    use core::arch::x86_64::*;

    // `cpufeatures::new!` expands to the deprecated `u8::max_value()`.
    #[allow(deprecated)]
    mod cpuid {
        cpufeatures::new!(avx512, "avx512f");
        cpufeatures::new!(avx2, "avx2");

        pub(crate) fn has_avx512() -> bool {
            avx512::get()
        }

        pub(crate) fn has_avx2() -> bool {
            avx2::get()
        }
    }
    pub(super) use cpuid::{has_avx2, has_avx512};

    /// Smallest leftover batch worth an 8-way permutation instead of scalar
    /// ones. On Zen 5 one 8-way permutation (about 145 ns) already beats one
    /// scalar permutation (about 190 ns).
    const X8_MIN_PARTIAL: usize = 1;
    /// Smallest leftover batch worth a 4-way permutation instead of scalar
    /// ones. On Zen 5 a 4-way permutation takes about 250 ns.
    const X4_MIN_PARTIAL: usize = 2;

    // AVX-512: `vpternlogq` folds three-input logic into one instruction and
    // `vprolq` rotates 64-bit lanes.
    macro_rules! avx512_xor5 {
        ($a:expr, $b:expr, $c:expr, $d:expr, $e:expr) => {
            _mm512_ternarylogic_epi64::<0x96>(_mm512_ternarylogic_epi64::<0x96>($a, $b, $c), $d, $e)
        };
    }
    macro_rules! avx512_rol1_xor {
        ($a:expr, $b:expr) => {
            _mm512_xor_si512($a, _mm512_rol_epi64::<1>($b))
        };
    }
    macro_rules! avx512_xor_rotl {
        ($a:expr, $d:expr, 0) => {
            _mm512_xor_si512($a, $d)
        };
        ($a:expr, $d:expr, $n:literal) => {
            _mm512_rol_epi64::<$n>(_mm512_xor_si512($a, $d))
        };
    }
    macro_rules! avx512_chi {
        // 0xD2 is the truth table of `a ^ (!b & c)`.
        ($a:expr, $b:expr, $c:expr) => {
            _mm512_ternarylogic_epi64::<0xD2>($a, $b, $c)
        };
    }
    macro_rules! avx512_xor_rc {
        ($a:expr, $rc:expr) => {
            _mm512_xor_si512($a, _mm512_set1_epi64($rc as i64))
        };
    }

    /// Hash up to 8 pairs with one 8-way permutation.
    ///
    /// # Safety
    ///
    /// The CPU must support AVX-512F.
    #[target_feature(enable = "avx512f")]
    unsafe fn hash_batch_x8(pairs: &[[Node; 2]], out: &mut [Node]) {
        debug_assert!(pairs.len() <= 8 && pairs.len() == out.len());
        let words = transpose_in::<8>(pairs);

        let mut a = [_mm512_setzero_si512(); 25];
        a[0] = _mm512_loadu_si512(words[0].as_ptr().cast());
        a[1] = _mm512_loadu_si512(words[1].as_ptr().cast());
        a[2] = _mm512_loadu_si512(words[2].as_ptr().cast());
        a[3] = _mm512_loadu_si512(words[3].as_ptr().cast());
        a[4] = _mm512_loadu_si512(words[4].as_ptr().cast());
        a[5] = _mm512_loadu_si512(words[5].as_ptr().cast());
        a[6] = _mm512_loadu_si512(words[6].as_ptr().cast());
        a[7] = _mm512_loadu_si512(words[7].as_ptr().cast());
        a[8] = _mm512_set1_epi64(PAD_LANE_8 as i64);
        a[16] = _mm512_set1_epi64(PAD_LANE_16 as i64);

        keccak_f1600!(
            a,
            avx512_xor5,
            avx512_rol1_xor,
            avx512_xor_rotl,
            avx512_chi,
            avx512_xor_rc
        );

        let mut lanes = [[0u64; 8]; 4];
        _mm512_storeu_si512(lanes[0].as_mut_ptr().cast(), a[0]);
        _mm512_storeu_si512(lanes[1].as_mut_ptr().cast(), a[1]);
        _mm512_storeu_si512(lanes[2].as_mut_ptr().cast(), a[2]);
        _mm512_storeu_si512(lanes[3].as_mut_ptr().cast(), a[3]);
        transpose_out::<8>(&lanes, out);
    }

    /// Hash `pairs` 8 at a time.
    ///
    /// # Safety
    ///
    /// The CPU must support AVX-512F.
    #[target_feature(enable = "avx512f")]
    pub(super) unsafe fn hash_pairs_x8(pairs: &[[Node; 2]], out: &mut [Node]) {
        let (batches, rest) = pairs.as_chunks::<8>();
        let (out_batches, out_rest) = out.as_chunks_mut::<8>();
        for (batch, out) in batches.iter().zip(out_batches) {
            hash_batch_x8(batch, out);
        }
        if rest.len() >= X8_MIN_PARTIAL {
            hash_batch_x8(rest, out_rest);
        } else {
            hash_pairs_scalar(rest, out_rest);
        }
    }

    // AVX2 has no 64-bit rotate or three-input logic, so rotations are two
    // shifts and an OR.
    macro_rules! avx2_rotl {
        ($x:expr, $n:literal) => {{
            let x = $x;
            _mm256_or_si256(
                _mm256_slli_epi64::<$n>(x),
                _mm256_srli_epi64::<{ 64 - $n }>(x),
            )
        }};
    }
    macro_rules! avx2_xor5 {
        ($a:expr, $b:expr, $c:expr, $d:expr, $e:expr) => {
            _mm256_xor_si256(
                _mm256_xor_si256(_mm256_xor_si256($a, $b), _mm256_xor_si256($c, $d)),
                $e,
            )
        };
    }
    macro_rules! avx2_rol1_xor {
        ($a:expr, $b:expr) => {
            _mm256_xor_si256($a, avx2_rotl!($b, 1))
        };
    }
    macro_rules! avx2_xor_rotl {
        ($a:expr, $d:expr, 0) => {
            _mm256_xor_si256($a, $d)
        };
        ($a:expr, $d:expr, $n:literal) => {
            avx2_rotl!(_mm256_xor_si256($a, $d), $n)
        };
    }
    macro_rules! avx2_chi {
        // `_mm256_andnot_si256(b, c)` is `!b & c`.
        ($a:expr, $b:expr, $c:expr) => {
            _mm256_xor_si256($a, _mm256_andnot_si256($b, $c))
        };
    }
    macro_rules! avx2_xor_rc {
        ($a:expr, $rc:expr) => {
            _mm256_xor_si256($a, _mm256_set1_epi64x($rc as i64))
        };
    }

    /// Hash up to 4 pairs with one 4-way permutation.
    ///
    /// Each state row is assembled in registers from 64-bit message words.
    /// On Zen 5 this measured about 20% faster per full batch than
    /// transposing through a stack buffer. The cause is not established:
    /// timings of this function shifted with unrelated code layout changes.
    ///
    /// # Safety
    ///
    /// The CPU must support AVX2.
    #[target_feature(enable = "avx2")]
    unsafe fn hash_batch_x4(pairs: &[[Node; 2]], out: &mut [Node]) {
        debug_assert!(pairs.len() <= 4 && pairs.len() == out.len());
        // Message word `i` of pair `k`, or zero past the end.
        let word = |k: usize, i: usize| -> i64 {
            match pairs.get(k) {
                Some(pair) => i64::from_le_bytes(pair.as_flattened().as_chunks::<8>().0[i]),
                None => 0,
            }
        };

        let mut a = [_mm256_setzero_si256(); 25];
        for (i, row) in a[..8].iter_mut().enumerate() {
            *row = _mm256_set_epi64x(word(3, i), word(2, i), word(1, i), word(0, i));
        }
        a[8] = _mm256_set1_epi64x(PAD_LANE_8 as i64);
        a[16] = _mm256_set1_epi64x(PAD_LANE_16 as i64);

        keccak_f1600!(
            a,
            avx2_xor5,
            avx2_rol1_xor,
            avx2_xor_rotl,
            avx2_chi,
            avx2_xor_rc
        );

        let mut lanes = [[0u64; 4]; 4];
        _mm256_storeu_si256(lanes[0].as_mut_ptr().cast(), a[0]);
        _mm256_storeu_si256(lanes[1].as_mut_ptr().cast(), a[1]);
        _mm256_storeu_si256(lanes[2].as_mut_ptr().cast(), a[2]);
        _mm256_storeu_si256(lanes[3].as_mut_ptr().cast(), a[3]);
        transpose_out::<4>(&lanes, out);
    }

    /// Hash `pairs` 4 at a time.
    ///
    /// # Safety
    ///
    /// The CPU must support AVX2.
    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn hash_pairs_x4(pairs: &[[Node; 2]], out: &mut [Node]) {
        let (batches, rest) = pairs.as_chunks::<4>();
        let (out_batches, out_rest) = out.as_chunks_mut::<4>();
        for (batch, out) in batches.iter().zip(out_batches) {
            hash_batch_x4(batch, out);
        }
        if rest.len() >= X4_MIN_PARTIAL {
            hash_batch_x4(rest, out_rest);
        } else {
            hash_pairs_scalar(rest, out_rest);
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use super::{
        hash_pairs_scalar, transpose_in, transpose_out, Node, PAD_LANE_16, PAD_LANE_8, RC,
    };
    use core::arch::aarch64::*;

    // `cpufeatures::new!` expands to the deprecated `u8::max_value()`.
    #[allow(deprecated)]
    mod cpuid {
        cpufeatures::new!(sha3_ext, "sha3");

        pub(crate) fn has_sha3() -> bool {
            sha3_ext::get()
        }
    }
    pub(super) use cpuid::has_sha3;

    // The ARMv8.2 SHA3 extension provides three-way XOR (`eor3`), XOR with a
    // one-bit rotate (`rax1`), XOR then rotate right (`xar`) and bit-clear-XOR
    // (`bcax`), on two 64-bit lanes per register.
    macro_rules! sha3_xor5 {
        ($a:expr, $b:expr, $c:expr, $d:expr, $e:expr) => {
            veor3q_u64(veor3q_u64($a, $b, $c), $d, $e)
        };
    }
    macro_rules! sha3_rol1_xor {
        ($a:expr, $b:expr) => {
            vrax1q_u64($a, $b)
        };
    }
    macro_rules! sha3_xor_rotl {
        ($a:expr, $d:expr, 0) => {
            veorq_u64($a, $d)
        };
        ($a:expr, $d:expr, $n:literal) => {
            vxarq_u64::<{ 64 - $n }>($a, $d)
        };
    }
    macro_rules! sha3_chi {
        // `vbcaxq_u64(a, c, b)` is `a ^ (c & !b)`.
        ($a:expr, $b:expr, $c:expr) => {
            vbcaxq_u64($a, $c, $b)
        };
    }
    macro_rules! sha3_xor_rc {
        ($a:expr, $rc:expr) => {
            veorq_u64($a, vdupq_n_u64($rc))
        };
    }

    /// Hash exactly 2 pairs with one 2-way permutation.
    ///
    /// # Safety
    ///
    /// The CPU must support the SHA3 extension.
    #[target_feature(enable = "neon,sha3")]
    unsafe fn hash_batch_x2(pairs: &[[Node; 2]; 2], out: &mut [Node; 2]) {
        let words = transpose_in::<2>(pairs);

        let mut a = [vdupq_n_u64(0); 25];
        a[0] = vld1q_u64(words[0].as_ptr());
        a[1] = vld1q_u64(words[1].as_ptr());
        a[2] = vld1q_u64(words[2].as_ptr());
        a[3] = vld1q_u64(words[3].as_ptr());
        a[4] = vld1q_u64(words[4].as_ptr());
        a[5] = vld1q_u64(words[5].as_ptr());
        a[6] = vld1q_u64(words[6].as_ptr());
        a[7] = vld1q_u64(words[7].as_ptr());
        a[8] = vdupq_n_u64(PAD_LANE_8);
        a[16] = vdupq_n_u64(PAD_LANE_16);

        keccak_f1600!(
            a,
            sha3_xor5,
            sha3_rol1_xor,
            sha3_xor_rotl,
            sha3_chi,
            sha3_xor_rc
        );

        let mut lanes = [[0u64; 2]; 4];
        vst1q_u64(lanes[0].as_mut_ptr(), a[0]);
        vst1q_u64(lanes[1].as_mut_ptr(), a[1]);
        vst1q_u64(lanes[2].as_mut_ptr(), a[2]);
        vst1q_u64(lanes[3].as_mut_ptr(), a[3]);
        transpose_out::<2>(&lanes, out);
    }

    /// Hash `pairs` 2 at a time; an odd last pair uses the scalar permutation.
    ///
    /// # Safety
    ///
    /// The CPU must support the SHA3 extension.
    #[target_feature(enable = "neon,sha3")]
    pub(super) unsafe fn hash_pairs_x2(pairs: &[[Node; 2]], out: &mut [Node]) {
        let (batches, rest) = pairs.as_chunks::<2>();
        let (out_batches, out_rest) = out.as_chunks_mut::<2>();
        for (batch, out) in batches.iter().zip(out_batches) {
            hash_batch_x2(batch, out);
        }
        hash_pairs_scalar(rest, out_rest);
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use sha3::{Digest, Keccak256};

    /// Pairs whose bytes differ in every position and set high bits, so a
    /// misplaced lane or byte-order slip changes the digest.
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
        Keccak256::digest(pair.as_flattened()).into()
    }

    /// Check a pair-hashing function against `sha3::Keccak256` for every batch
    /// count up to five 8-way batches plus remainder, and on all-zero pairs.
    fn check_backend(name: &str, hash_pairs: impl Fn(&[[Node; 2]], &mut [Node])) {
        for count in 0..=41 {
            let pairs = sample_pairs(count);
            let mut out = vec![[0u8; 32]; count];
            hash_pairs(&pairs, &mut out);
            for (i, (pair, node)) in pairs.iter().zip(&out).enumerate() {
                assert_eq!(*node, digest(pair), "{name}: pair {i} of {count}");
            }
        }
        let zeros = [[[0u8; 32]; 2]; 9];
        let mut out = [[0xffu8; 32]; 9];
        hash_pairs(&zeros, &mut out);
        assert!(
            out.iter().all(|node| *node == crate::ZERO_HASHES[1]),
            "{name}: all-zero pairs must hash to ZERO_HASHES[1]"
        );
    }

    #[test]
    fn scalar_matches_digest() {
        check_backend("scalar", hash_pairs_scalar);
    }

    #[test]
    fn dispatch_matches_digest() {
        check_backend("dispatch", |pairs, out| KeccakHasher.hash_pairs(pairs, out));
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn avx512_matches_digest() {
        if x86::has_avx512() {
            // SAFETY: AVX-512F support was just checked.
            check_backend("avx512", |pairs, out| unsafe {
                x86::hash_pairs_x8(pairs, out)
            });
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn avx2_matches_digest() {
        if x86::has_avx2() {
            // SAFETY: AVX2 support was just checked.
            check_backend("avx2", |pairs, out| unsafe {
                x86::hash_pairs_x4(pairs, out)
            });
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn sha3_extension_matches_digest() {
        if aarch64::has_sha3() {
            // SAFETY: SHA3 extension support was just checked.
            check_backend("sha3", |pairs, out| unsafe {
                aarch64::hash_pairs_x2(pairs, out)
            });
        }
    }

    #[test]
    #[should_panic(expected = "one output node per pair")]
    fn hash_pairs_rejects_mismatched_output() {
        let pairs = sample_pairs(3);
        let mut out = [[0u8; 32]; 2];
        KeccakHasher.hash_pairs(&pairs, &mut out);
    }
}
