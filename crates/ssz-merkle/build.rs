use sha2::{Digest, Sha256};
use std::env;
use std::fs;
use std::path::Path;

const MAX_DEPTH: usize = 64;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("zero_hashes.rs");

    let mut zero_hashes = [[0u8; 32]; MAX_DEPTH + 1];
    // zero_hashes[0] is already all zeros

    for i in 1..=MAX_DEPTH {
        let mut hasher = Sha256::new();
        hasher.update(zero_hashes[i - 1]);
        hasher.update(zero_hashes[i - 1]);
        let result = hasher.finalize();
        zero_hashes[i].copy_from_slice(&result);
    }

    let mut code = String::new();
    code.push_str("/// Precomputed zero hashes for SSZ Merkleization.\n");
    code.push_str("/// ZERO_HASHES\\[i\\] = hash(ZERO_HASHES\\[i-1\\], ZERO_HASHES\\[i-1\\]), with ZERO_HASHES\\[0\\] = \\[0u8; 32\\].\n");
    code.push_str(&format!(
        "pub static ZERO_HASHES: [[u8; 32]; {}] = [\n",
        MAX_DEPTH + 1
    ));
    for hash in &zero_hashes {
        code.push_str("    [");
        for (j, byte) in hash.iter().enumerate() {
            if j > 0 {
                code.push_str(", ");
            }
            code.push_str(&format!("{byte}"));
        }
        code.push_str("],\n");
    }
    code.push_str("];\n");

    fs::write(dest, code).unwrap();
}
