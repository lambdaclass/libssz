//! Differential tests of the SHA-NI kernel of `ssz-merkle` (libssz).
//!
//! The Lean proofs in `lean/Libssz/Merkle/Proofs/` state that the Aeneas model of
//! `shani.rs` computes EthLib's `combine` *assuming* that the eight intrinsics of
//! `core::arch::x86_64` do what the hand-written models in
//! `lean/Libssz/Merkle/Intrinsics.lean` say. This tests that assumption and the rest of the
//! chain:
//!
//! * `intrinsics_match_their_lean_models`: each intrinsic, executed by the processor, against
//!   its Lean model, on random and edge inputs;
//! * `kernel_matches_its_lean_model_and_the_spec`: `Sha2Hasher` (which on this machine
//!   dispatches to the SHA-NI kernel) against the Aeneas model, against EthLib's `combine` and
//!   against the `sha2` crate, for one pair, two pairs and whole layers (also in place and
//!   with short outputs, which must panic on both sides).
//!
//! The Lean executable is `lean/.lake/build/bin/difftest-merkle` (`lake build
//! difftest-merkle`); its format is described in `lean/DiffTestMerkle.lean`.
#![cfg(target_arch = "x86_64")]

use core::arch::x86_64::{
    __m128i, _mm_add_epi32, _mm_alignr_epi8, _mm_extract_epi32, _mm_set_epi32,
    _mm_sha256msg1_epu32, _mm_sha256msg2_epu32, _mm_sha256rnds2_epu32, _mm_shuffle_epi32,
};
use std::io::Write;
use std::process::{Command, Stdio};

use merkle::{Sha256Hasher, Sha2Hasher};
use sha2::{Digest, Sha256};

type Node = [u8; 32];

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn vec(&mut self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.next().to_le_bytes());
        out[8..].copy_from_slice(&self.next().to_le_bytes());
        out
    }
    fn node(&mut self) -> Node {
        let mut out = [0u8; 32];
        for part in out.chunks_mut(8) {
            part.copy_from_slice(&self.next().to_le_bytes());
        }
        out
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn hex_nodes(nodes: &[Node]) -> String {
    if nodes.is_empty() {
        "-".to_string()
    } else {
        nodes.iter().map(|n| hex(n)).collect()
    }
}

fn has_kernel() -> bool {
    is_x86_feature_detected!("sha")
        && is_x86_feature_detected!("sse2")
        && is_x86_feature_detected!("ssse3")
        && is_x86_feature_detected!("sse4.1")
}

/// The 16 bytes of the vector as laid out in memory. Does not go through any intrinsic.
fn bytes_of(v: __m128i) -> [u8; 16] {
    unsafe { core::mem::transmute(v) }
}

fn vec_of(b: [u8; 16]) -> __m128i {
    unsafe { core::mem::transmute(b) }
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn add(a: __m128i, b: __m128i) -> __m128i {
    _mm_add_epi32(a, b)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn msg1(a: __m128i, b: __m128i) -> __m128i {
    _mm_sha256msg1_epu32(a, b)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn msg2(a: __m128i, b: __m128i) -> __m128i {
    _mm_sha256msg2_epu32(a, b)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn rnds2(a: __m128i, b: __m128i, k: __m128i) -> __m128i {
    _mm_sha256rnds2_epu32(a, b, k)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn set(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    _mm_set_epi32(e3, e2, e1, e0)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn shuffle<const IMM: i32>(a: __m128i) -> __m128i {
    _mm_shuffle_epi32::<IMM>(a)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn alignr<const IMM: i32>(a: __m128i, b: __m128i) -> __m128i {
    _mm_alignr_epi8::<IMM>(a, b)
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn extract<const IMM: i32>(a: __m128i) -> i32 {
    _mm_extract_epi32::<IMM>(a)
}

type Shuffle = (i32, fn(__m128i) -> __m128i);
type Alignr = (i32, fn(__m128i, __m128i) -> __m128i);
type Extract = (i32, fn(__m128i) -> i32);

/// The immediates are const generics: there is one function per tested value.
macro_rules! with_imms {
    ($f:ident(a) -> $out:ty: $($imm:literal)*) => {
        [$(($imm, (|a: __m128i| unsafe { $f::<$imm>(a) }) as fn(__m128i) -> $out)),*]
    };
    ($f:ident(a, b): $($imm:literal)*) => {
        [$((
            $imm,
            (|a: __m128i, b: __m128i| unsafe { $f::<$imm>(a, b) })
                as fn(__m128i, __m128i) -> __m128i,
        )),*]
    };
}

/// The `PSHUFD` immediate values the kernel uses (`0x0e`) and others that move every lane to
/// every position.
fn shuffles() -> Vec<Shuffle> {
    let all: [Shuffle; 20] = with_imms!(shuffle(a) -> __m128i:
        0x00 0x0e 0x1b 0x4e 0xb1 0xe4 0xff 0x93 0x39 0x55 0xaa 0x01 0x04 0x10 0x40 0x02 0x08
        0x20 0x80 0xc6);
    all.to_vec()
}

/// `PALIGNR`: the kernel uses 4. Shifts that cross from one operand to the other and those
/// that leave everything zero (32 or more) are tested too.
fn alignrs() -> Vec<Alignr> {
    let all: [Alignr; 22] = with_imms!(alignr(a, b):
        0 1 2 3 4 5 7 8 9 12 13 15 16 17 20 24 28 31 32 33 64 255);
    all.to_vec()
}

fn extracts() -> Vec<Extract> {
    let all: [Extract; 4] = with_imms!(extract(a) -> i32: 0 1 2 3);
    all.to_vec()
}

/// Random and edge vectors: all zeros, all ones, a single bit, and lanes distinct from each
/// other (so that a lane-order error shows up).
fn vectors(r: &mut Rng, random: usize) -> Vec<[u8; 16]> {
    let mut out = vec![[0u8; 16], [0xff; 16], [0x80; 16], [0x7f; 16]];
    let mut lanes = [0u8; 16];
    for (i, b) in lanes.iter_mut().enumerate() {
        *b = i as u8 + 1;
    }
    out.push(lanes);
    for at in 0..16 {
        for bit in [0x01, 0x80] {
            let mut v = [0u8; 16];
            v[at] = bit;
            out.push(v);
        }
    }
    for _ in 0..random {
        out.push(r.vec());
    }
    out
}

/// Runs the Lean executable on the given lines and returns one answer per line.
fn lean(input: Vec<String>) -> Vec<String> {
    let exe = std::env::var("LEAN_DIFFTEST_MERKLE").unwrap_or_else(|_| {
        format!(
            "{}/../lean/.lake/build/bin/difftest-merkle",
            env!("CARGO_MANIFEST_DIR")
        )
    });
    let mut child = Command::new(exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Lean executable not found: run `lake build difftest-merkle` in ../lean");
    let mut stdin = child.stdin.take().unwrap();
    let text = input.join("\n") + "\n";
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()).unwrap());
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    let out = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<String> = out.lines().map(str::to_string).collect();
    assert_eq!(
        lines.len(),
        input.len(),
        "the Lean executable did not answer every case"
    );
    lines
}

/// Compares and counts: `cases` are pairs (line for Lean, answer expected by Rust).
fn compare(what: &str, cases: Vec<(String, String)>) -> usize {
    let (input, want): (Vec<String>, Vec<String>) = cases.into_iter().unzip();
    let got = lean(input.clone());
    let mut bad = 0;
    for ((line, want), got) in input.iter().zip(&want).zip(&got) {
        if want != got {
            bad += 1;
            if bad <= 10 {
                println!("LEAN ≠ RUST  {line}\n    Rust: {want}\n    Lean: {got}");
            }
        }
    }
    println!("{what}: {} cases, {bad} mismatches", input.len());
    bad
}

#[test]
fn intrinsics_match_their_lean_models() {
    assert!(
        has_kernel(),
        "this processor lacks the SHA extensions: the intrinsics cannot be tested"
    );
    let mut r = Rng(0x5eed_1234_abcd_ef01);
    let vs = vectors(&mut r, 400);
    let mut cases = Vec::new();
    let mut count = std::collections::BTreeMap::new();
    let mut push = |name: &'static str, line: String, want: String| {
        *count.entry(name).or_insert(0usize) += 1;
        cases.push((line, want));
    };

    // Two operands: each vector with the next one, with a pseudo-random one and with itself.
    for (i, a) in vs.iter().enumerate() {
        for b in [vs[(i + 1) % vs.len()], vs[(7 * i + 3) % vs.len()], *a] {
            let (va, vb) = (vec_of(*a), vec_of(b));
            let args = format!("{} {}", hex(a), hex(&b));
            push(
                "add",
                format!("add {args}"),
                hex(&bytes_of(unsafe { add(va, vb) })),
            );
            push(
                "msg1",
                format!("msg1 {args}"),
                hex(&bytes_of(unsafe { msg1(va, vb) })),
            );
            push(
                "msg2",
                format!("msg2 {args}"),
                hex(&bytes_of(unsafe { msg2(va, vb) })),
            );
            let k = vs[(5 * i + 11) % vs.len()];
            push(
                "rnds2",
                format!("rnds2 {args} {}", hex(&k)),
                hex(&bytes_of(unsafe { rnds2(va, vb, vec_of(k)) })),
            );
        }
    }
    for (i, a) in vs.iter().enumerate().take(120) {
        let va = vec_of(*a);
        for (imm, f) in shuffles() {
            push(
                "shuffle",
                format!("shuffle {imm} {}", hex(a)),
                hex(&bytes_of(f(va))),
            );
        }
        for (imm, f) in extracts() {
            push(
                "extract",
                format!("extract {imm} {}", hex(a)),
                format!("{:08x}", f(va) as u32),
            );
        }
        let b = vs[(3 * i + 1) % vs.len()];
        for (imm, f) in alignrs() {
            push(
                "alignr",
                format!("alignr {imm} {} {}", hex(a), hex(&b)),
                hex(&bytes_of(f(va, vec_of(b)))),
            );
        }
    }
    let mut words = vec![0u32, 1, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff, 0x0102_0304];
    for _ in 0..200 {
        words.push(r.next() as u32);
    }
    for i in 0..words.len() {
        let e = [
            words[i],
            words[(i + 1) % words.len()],
            words[(3 * i + 2) % words.len()],
            words[(5 * i + 4) % words.len()],
        ];
        push(
            "set",
            format!("set {:08x} {:08x} {:08x} {:08x}", e[0], e[1], e[2], e[3]),
            hex(&bytes_of(unsafe {
                set(e[0] as i32, e[1] as i32, e[2] as i32, e[3] as i32)
            })),
        );
    }
    println!("cases per intrinsic: {count:?}");
    let bad = compare("intrinsics: processor vs Lean model", cases);
    assert_eq!(
        bad, 0,
        "{bad} mismatches between the processor and the Lean models"
    );
}

fn sha2_pair(a: &Node, b: &Node) -> Node {
    let mut h = Sha256::new();
    h.update(a);
    h.update(b);
    h.finalize().into()
}

fn edge_nodes() -> Vec<Node> {
    let mut out = vec![[0u8; 32], [0xff; 32], [0x80; 32], [0x7f; 32]];
    for at in 0..32 {
        let mut node = [0u8; 32];
        node[at] = 0x80;
        out.push(node);
        node[at] = 0x01;
        out.push(node);
        let mut node = [0xff; 32];
        node[at] = 0;
        out.push(node);
    }
    out
}

/// Rust's `hash_layer`; `None` if it panics.
fn rust_layer(below: &[Node], level: &[Node], in_place: bool, zero: &Node) -> Option<Vec<Node>> {
    let mut out = level.to_vec();
    let run = std::panic::AssertUnwindSafe(|| {
        if in_place {
            Sha2Hasher.hash_layer_in_place(&mut out, zero)
        } else {
            Sha2Hasher.hash_layer(below, &mut out, zero)
        }
    });
    std::panic::catch_unwind(run).ok()?;
    Some(out)
}

#[test]
fn kernel_matches_its_lean_model_and_the_spec() {
    assert!(
        has_kernel(),
        "this processor lacks the SHA extensions: `Sha2Hasher` would not use the kernel"
    );
    std::panic::set_hook(Box::new(|_| {}));
    let mut r = Rng(0x0dd_ba11_cafe_f00d);
    let mut cases = Vec::new();

    // One pair: Rust (kernel) = sha2 = Aeneas model = EthLib.
    let mut nodes = edge_nodes();
    for _ in 0..400 {
        nodes.push(r.node());
    }
    let mut pairs = 0;
    for (i, a) in nodes.iter().enumerate() {
        for b in [
            nodes[(i + 1) % nodes.len()],
            nodes[(7 * i + 5) % nodes.len()],
            *a,
        ] {
            let got = Sha2Hasher.hash_pair(a, &b);
            assert_eq!(got, sha2_pair(a, &b), "kernel ≠ sha2");
            cases.push((
                format!("pair {} {}", hex(a), hex(&b)),
                format!("{}\t{}", hex(&got), hex(&got)),
            ));
            pairs += 1;
        }
    }

    // Two interleaved pairs: the model against sha2 of each pair.
    let mut quads = 0;
    for i in 0..nodes.len() {
        let q = [
            nodes[i],
            nodes[(3 * i + 1) % nodes.len()],
            nodes[(5 * i + 2) % nodes.len()],
            nodes[(11 * i + 7) % nodes.len()],
        ];
        cases.push((
            format!(
                "pairs2 {} {} {} {}",
                hex(&q[0]),
                hex(&q[1]),
                hex(&q[2]),
                hex(&q[3])
            ),
            format!(
                "{},{}",
                hex(&sha2_pair(&q[0], &q[1])),
                hex(&sha2_pair(&q[2], &q[3]))
            ),
        ));
        quads += 1;
    }

    // Four interleaved pairs: the model against sha2 of each pair.
    let mut octs = 0;
    for i in 0..nodes.len() {
        let o: Vec<Node> = (0..8)
            .map(|j| nodes[(13 * i + 7 * j + j * j) % nodes.len()])
            .collect();
        cases.push((
            format!(
                "pairs4 {}",
                o.iter().map(|n| hex(n)).collect::<Vec<_>>().join(" ")
            ),
            format!(
                "{},{},{},{}",
                hex(&sha2_pair(&o[0], &o[1])),
                hex(&sha2_pair(&o[2], &o[3])),
                hex(&sha2_pair(&o[4], &o[5])),
                hex(&sha2_pair(&o[6], &o[7]))
            ),
        ));
        octs += 1;
    }

    // Whole layers, into another buffer and in place, with room to spare and too little room.
    let mut layers = 0;
    let mut panics = 0;
    let zero = r.node();
    for len in (0..=21usize).chain([31, 32, 33, 64, 65]) {
        let below: Vec<Node> = (0..len).map(|_| r.node()).collect();
        let parents = len.div_ceil(2);
        let mut sizes = vec![parents, parents + 1, parents + 3];
        if parents > 0 {
            sizes.push(parents - 1);
            sizes.push(0);
        }
        for size in sizes {
            let level = vec![[0xaa; 32]; size];
            let got = rust_layer(&below, &level, false, &zero);
            if let Some(out) = &got {
                for (k, pair) in below.chunks(2).enumerate() {
                    let right = pair.get(1).unwrap_or(&zero);
                    assert_eq!(out[k], sha2_pair(&pair[0], right), "layer ≠ sha2");
                }
                assert!(out[parents..].iter().all(|n| *n == [0xaa; 32]));
            } else {
                panics += 1;
            }
            cases.push((
                format!(
                    "layer 0 {} {} {}",
                    hex(&zero),
                    hex_nodes(&below),
                    hex_nodes(&level)
                ),
                got.map_or("PANIC".to_string(), |out| hex_nodes(&out)),
            ));
            layers += 1;
        }
        // In place. `below` is not read: any value is passed.
        let got = rust_layer(&[], &below, true, &zero).expect("in place there is no panic");
        for (k, pair) in below.chunks(2).enumerate() {
            let right = pair.get(1).unwrap_or(&zero);
            assert_eq!(got[k], sha2_pair(&pair[0], right), "in-place layer ≠ sha2");
        }
        assert_eq!(got[parents..], below[parents..]);
        for other in [vec![], vec![[0x55; 32]; 3]] {
            cases.push((
                format!(
                    "layer 1 {} {} {}",
                    hex(&zero),
                    hex_nodes(&other),
                    hex_nodes(&below)
                ),
                hex_nodes(&got),
            ));
            layers += 1;
        }
    }
    println!(
        "{pairs} pairs, {quads} double pairs, {octs} quadruple pairs, {layers} layers ({panics} panicking on both sides)"
    );
    let bad = compare("kernel: Rust vs Aeneas model vs EthLib", cases);
    assert_eq!(bad, 0, "{bad} mismatches");
}
