#![no_main]

//! Fuzz merkle primitives (hash_nodes, pack, pack_bits, merkleize, mix_in_length)
//! with adversarial sizes and data.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz_merkle::{hash_nodes, merkleize, mix_in_length, pack, pack_bits, Node};

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    node_a: [u8; 32],
    node_b: [u8; 32],
    pack_data: Vec<u8>,
    bits_data: Vec<u8>,
    num_bits: usize,
    num_chunks: u16,
    limit: Option<u16>,
    mix_length: usize,
}

fuzz_target!(|input: FuzzInput| {
    // hash_nodes — must never panic
    let _ = hash_nodes(&input.node_a, &input.node_b);

    // pack — any byte slice, must not panic
    if input.pack_data.len() <= 32768 {
        let _ = pack(&input.pack_data);
    }

    // pack_bits — adversarial num_bits vs actual data length
    if input.bits_data.len() <= 4096 {
        let max_bits = input.bits_data.len() * 8;
        // Only call with valid num_bits (within data bounds) to test internal logic
        if input.num_bits <= max_bits {
            let _ = pack_bits(&input.bits_data, input.num_bits);
        }
    }

    // merkleize — variable chunk counts, with and without limits
    let n = (input.num_chunks as usize).min(4096);
    if n > 0 {
        let chunks: Vec<Node> = (0..n)
            .map(|i| {
                let mut node = [0u8; 32];
                let bytes = (i as u64).to_le_bytes();
                node[..8].copy_from_slice(&bytes);
                node
            })
            .collect();

        // Without limit — must not panic
        let _ = merkleize(&chunks, None);

        // With limit >= chunks — must not panic
        if let Some(raw_limit) = input.limit {
            let limit = (raw_limit as usize).max(n);
            let _ = merkleize(&chunks, Some(limit));
        }
    }

    // merkleize with 0 chunks — edge case
    let _ = merkleize(&[], None);
    let _ = merkleize(&[], Some(1));
    let _ = merkleize(&[], Some(0));

    // mix_in_length — must not panic
    let _ = mix_in_length(&input.node_a, input.mix_length);
});
