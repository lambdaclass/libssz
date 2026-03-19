use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use libssz_merkle::{hash_nodes, merkleize, pack, Node};

fn make_chunks(n: usize) -> Vec<Node> {
    (0..n)
        .map(|i| {
            let mut node = [0u8; 32];
            node[..8].copy_from_slice(&(i as u64).to_le_bytes());
            node
        })
        .collect()
}

#[library_benchmark]
fn iai_hash_nodes() -> Node {
    let a: Node = [0xaa; 32];
    let b: Node = [0xbb; 32];
    hash_nodes(&a, &b)
}

#[library_benchmark]
fn iai_merkleize_64() -> Node {
    let chunks = make_chunks(64);
    merkleize(&chunks, None)
}

#[library_benchmark]
fn iai_merkleize_1024() -> Node {
    let chunks = make_chunks(1024);
    merkleize(&chunks, None)
}

#[library_benchmark]
fn iai_pack_1kb() -> Vec<Node> {
    let data: Vec<u8> = (0..1024).map(|i| i as u8).collect();
    pack(&data)
}

library_benchmark_group!(
    name = merkle_group;
    benchmarks = iai_hash_nodes, iai_merkleize_64, iai_merkleize_1024, iai_pack_1kb
);

main!(library_benchmark_groups = merkle_group);
