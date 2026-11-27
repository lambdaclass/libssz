//! libssz-merkle against the naive reference model, on generated chunk
//! counts and limits. Chunk counts straddle the powers of two and the
//! progressive subtree boundaries (1, 5, 21, 85, 341 chunks).
//!
//! The reference model materializes full trees and debug builds hash slowly,
//! so the tree properties run fewer cases by default; `make
//! property-tests-long` runs them in release with a large budget.

use ephyra::gens;
use libssz_merkle::{
    merkleize, merkleize_progressive, mix_in_active_fields, mix_in_length, mix_in_selector, pack,
    pack_bits, Sha2Hasher,
};
use property_tests::reference::{self, Chunk};

/// Distinct, cheap chunks: each seed repeated across the chunk.
fn chunks_from(seeds: &[u64]) -> Vec<Chunk> {
    seeds
        .iter()
        .map(|seed| {
            let mut chunk = [0u8; 32];
            for word in chunk.as_chunks_mut::<8>().0 {
                *word = seed.to_le_bytes();
            }
            chunk
        })
        .collect()
}

/// `(seeds, extra)`: `extra` is how far the limit sits above the chunk count.
#[ephyra::test(
    gen = (
        gens::vec(gens::int(0u64..=u64::MAX)).len(0..=70),
        gens::int(0usize..=200),
    ),
    tests = 1_000
)]
fn merkleize_with_limit_matches_reference(input: (Vec<u64>, usize)) {
    let chunks = chunks_from(&input.0);
    let limit = chunks.len() + input.1;
    assert_eq!(
        merkleize(&Sha2Hasher, &chunks, Some(limit)),
        reference::merkleize(&chunks, limit)
    );
}

#[ephyra::test(gen = gens::vec(gens::int(0u64..=u64::MAX)).len(0..=70), tests = 2_000)]
fn merkleize_without_limit_matches_reference(seeds: Vec<u64>) {
    let chunks = chunks_from(&seeds);
    assert_eq!(
        merkleize(&Sha2Hasher, &chunks, None),
        reference::merkleize(&chunks, chunks.len())
    );
}

#[ephyra::test(gen = gens::vec(gens::int(0u64..=u64::MAX)).len(0..=400), tests = 300)]
fn merkleize_progressive_matches_reference(seeds: Vec<u64>) {
    let chunks = chunks_from(&seeds);
    assert_eq!(
        merkleize_progressive(&Sha2Hasher, &chunks),
        reference::merkleize_progressive(&chunks)
    );
}

#[ephyra::test(gen = gens::vec(gens::int(0u8..=255)).len(0..=200))]
fn pack_matches_reference(bytes: Vec<u8>) {
    assert_eq!(pack(&bytes), reference::pack(&bytes));
}

#[ephyra::test(gen = gens::vec(gens::bool()).len(0..=600))]
fn pack_bits_matches_reference(bits: Vec<bool>) {
    let bytes = reference::bits_to_bytes(&bits);
    assert_eq!(pack_bits(&bytes, bits.len()), reference::pack(&bytes));
}

#[ephyra::test(gen = (gens::int(0u64..=u64::MAX), gens::int(0usize..=usize::MAX)))]
fn mix_in_length_matches_reference(input: (u64, usize)) {
    let root = chunks_from(&[input.0])[0];
    assert_eq!(
        mix_in_length(&Sha2Hasher, &root, input.1),
        reference::mix_in_length(&root, input.1)
    );
}

#[ephyra::test(gen = (gens::int(0u64..=u64::MAX), gens::int(0u8..=127)))]
fn mix_in_selector_matches_reference(input: (u64, u8)) {
    let root = chunks_from(&[input.0])[0];
    assert_eq!(
        mix_in_selector(&Sha2Hasher, &root, input.1),
        reference::mix_in_selector(&root, input.1)
    );
}

#[ephyra::test(gen = (gens::int(0u64..=u64::MAX), gens::vec(gens::bool()).len(1..=256)))]
fn mix_in_active_fields_matches_reference(input: (u64, Vec<bool>)) {
    let root = chunks_from(&[input.0])[0];
    assert_eq!(
        mix_in_active_fields(&Sha2Hasher, &root, &input.1),
        reference::mix_in_active_fields(&root, &input.1)
    );
}
