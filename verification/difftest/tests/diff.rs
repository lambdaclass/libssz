//! Differential tests of libssz.
//!
//! Two versions of the library are compared, as two dependencies:
//!
//! * `orig`: libssz at upstream commit f6c22eb, before the verification rewrite (it has
//!   `unsafe` code, `memcpy`s and iterators);
//! * `verif`: libssz in this repository (`../../crates/ssz`), the code that Charon + Aeneas
//!   translate to Lean and that is proven equal to the EthLib spec.
//!
//! The tests:
//!
//! * `orig_vs_verif`: `orig` against `verif`, over many types, including the paths where
//!   `orig` had `unsafe` code (`ssz_decode_fixed_vec`, `ssz_append_fixed_slice`), long lists
//!   (also longer than 8 KB, which in `verif` take the blockwise path), lists of fixed-size
//!   containers, containers built with `ContainerEncoder`/`ContainerDecoder` (one with more
//!   than eight variable-size fields) and random sequences of operations on
//!   `ContainerEncoder`. In all of them the re-encoding is computed with `to_ssz` and with
//!   `ssz_append` on a buffer that already has bytes, and both have to agree.
//! * `lean_model_and_spec`: the same cases, run on the **Lean model** Aeneas generates for
//!   libssz and on the **EthLib spec** (`../lean/DiffTest.lean`).
//!   - model vs Rust: they must give exactly the same result (this validates the Charon +
//!     Aeneas translation, also for functions that do not have a proof yet);
//!   - EthLib vs Rust: they must accept and reject the same inputs, with the same value and
//!     the same re-encoding. The pairs of errors are counted and shown.
//!
//! Everything is deterministic (an LCG with a fixed seed).

// The code `ssz-derive` generates refers to the library as `libssz::`.
extern crate orig as libssz;

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::process::{Command, Stdio};

// ── Input generation ──

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

/// "Interesting" random values (edge cases included).
trait Gen: Sized {
    fn gen(r: &mut Rng) -> Self;
}

macro_rules! gen_uint {
    ($($t:ty),*) => {$(
        impl Gen for $t {
            fn gen(r: &mut Rng) -> Self {
                match r.below(4) {
                    0 => 0,
                    1 => <$t>::MAX,
                    2 => (r.below(256)) as $t,
                    _ => ((r.next() as u128) << 64 | r.next() as u128) as $t,
                }
            }
        }
    )*};
}
gen_uint!(u8, u16, u32, u64, u128);

impl Gen for bool {
    fn gen(r: &mut Rng) -> Self {
        r.below(2) == 1
    }
}

impl<const N: usize> Gen for [u8; N] {
    fn gen(r: &mut Rng) -> Self {
        let mut a = [0u8; N];
        for x in a.iter_mut() {
            *x = r.next() as u8;
        }
        a
    }
}

impl<T: Gen> Gen for Vec<T> {
    fn gen(r: &mut Rng) -> Self {
        let n = r.below(6) as usize;
        (0..n).map(|_| T::gen(r)).collect()
    }
}

/// A valid encoding and mutations of it (a changed byte, truncated, extended), plus random
/// bytes.
fn mutations(r: &mut Rng, valid: Vec<u8>, out: &mut Vec<Vec<u8>>) {
    out.push(valid.clone());
    let mut m = valid.clone();
    if !m.is_empty() {
        let i = r.below(m.len() as u64) as usize;
        m[i] ^= 1 << r.below(8);
    }
    out.push(m);
    let cut = r.below(valid.len() as u64 + 1) as usize;
    out.push(valid[..cut].to_vec());
    let mut ext = valid;
    let extra = 1 + r.below(4) as usize;
    ext.extend(r.bytes(extra));
    out.push(ext);
    let len = r.below(40) as usize;
    out.push(r.bytes(len));
}

/// Inputs for a type: valid encodings (made with `orig`) and mutations.
fn corpus<T: Gen + orig::SszEncode>(r: &mut Rng, n: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..n {
        let valid = orig::SszEncode::to_ssz(&T::gen(r));
        mutations(r, valid, &mut out);
    }
    out
}

/// Inputs for `Vec<T>` with long lists (up to `max` items) and their mutations. These are the
/// ones that take the blockwise paths: the `memcpy` in `orig`; in `verif`, `to_vec`,
/// `as_chunks`, `as_flattened` and the loops over already-reserved memory.
fn big_corpus<T: Gen + orig::SszEncode>(r: &mut Rng, n: usize, max: u64) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..n {
        let len = r.below(max + 1) as usize;
        let v: Vec<T> = (0..len).map(|_| T::gen(r)).collect();
        let valid = orig::SszEncode::to_ssz(&v);
        mutations(r, valid, &mut out);
    }
    out
}

/// Lists of `T` whose length is close to a multiple of `block` items (and their mutations).
/// In `verif`, integers wider than one byte are encoded in 8 KB batches
/// (`block = 8192 / size_of::<T>()` items): with less than one batch they take one path, with
/// one or more another, and the remainder of the last batch is handled separately.
fn blk_corpus<T: Gen + orig::SszEncode>(r: &mut Rng, block: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let lens = [
        block - 1,
        block,
        block + 1,
        2 * block - 1,
        2 * block,
        2 * block + 3,
        3 * block + block / 2,
    ];
    for len in lens {
        let v: Vec<T> = (0..len).map(|_| T::gen(r)).collect();
        let valid = orig::SszEncode::to_ssz(&v);
        mutations(r, valid, &mut out);
    }
    out
}

/// The same for the Lean model, which is slow with lists this long (its "vectors" are linked
/// lists: tens of seconds per case): only the valid encodings of lengths `lens` and one of
/// them with one byte less.
fn blk_lean_corpus<T: Gen + orig::SszEncode>(r: &mut Rng, lens: &[usize]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for &len in lens {
        let v: Vec<T> = (0..len).map(|_| T::gen(r)).collect();
        out.push(orig::SszEncode::to_ssz(&v));
    }
    if let Some(first) = out.first() {
        let mut cut = first.clone();
        cut.pop();
        out.push(cut);
    }
    out
}

/// Inputs for a list of fixed-size containers of `w` bytes: 0 to 5 random items (with the
/// `bool_at` byte of each item almost always valid) and their mutations.
fn fixed_list_corpus(r: &mut Rng, w: usize, bool_at: Option<usize>) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..500 {
        let n = r.below(6) as usize;
        let mut b = r.bytes(n * w);
        if let Some(i) = bool_at {
            for k in 0..n {
                if r.below(8) != 0 {
                    b[k * w + i] = r.below(2) as u8;
                }
            }
        }
        mutations(r, b, &mut out);
    }
    out
}

/// All strings of length ≤ 2.
fn exhaustive2() -> Vec<Vec<u8>> {
    let mut out = vec![vec![]];
    for a in 0..=255u8 {
        out.push(vec![a]);
        for b in 0..=255u8 {
            out.push(vec![a, b]);
        }
    }
    out
}

// ── Running each Rust version ──

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn quiet<R>(f: impl FnOnce() -> R) -> Option<R> {
    catch_unwind(AssertUnwindSafe(f)).ok()
}

/// A text clipped for display (some inputs are larger than 8 KB).
fn clip(s: &str) -> String {
    if s.chars().count() <= 400 {
        s.to_string()
    } else {
        let head: String = s.chars().take(400).collect();
        format!("{head}… ({} characters)", s.chars().count())
    }
}

/// An `assert_eq!` that also prints the difference: the panic hook is silenced (see
/// `silence_panics`), so the message of a plain `assert_eq!` would not be shown.
macro_rules! check_eq {
    ($o:expr, $v:expr, $($arg:tt)*) => {{
        let (o, v) = (&$o, &$v);
        if o != v {
            eprintln!(
                "MISMATCH in {}\n  orig: {}\n  {}: {}",
                clip(&format!($($arg)*)),
                clip(&format!("{o:?}")),
                version(),
                clip(&format!("{v:?}")),
            );
            panic!("mismatch between orig and {}", version());
        }
    }};
}

/// With `DIFF_ONLY=<prefix>` in the environment, only the types (or groups of cases: `cont`,
/// `wide`, `ops`, `list-max`) whose name starts with that prefix are run. Useful to quickly
/// repeat a case; without the variable everything runs.
fn selected(name: &str) -> bool {
    match std::env::var("DIFF_ONLY") {
        Ok(p) => name.starts_with(&p),
        Err(_) => true,
    }
}

/// The bytes already in the buffer the re-encoding is appended to (the same ones
/// `DiffTest.lean` uses).
const PREFIX: [u8; 3] = [0x5a, 0xa5, 0x00];

/// The re-encoding of a value, in hex: `to_ssz`. Also, `ssz_append` on a buffer that already
/// has `PREFIX` must give those bytes followed by the same thing, and `encoded_len` must be
/// the length; otherwise the text says so and the comparison with the other version (or with
/// the Lean model) fails.
macro_rules! reenc_impl {
    ($m:ident, $f:ident) => {
        fn $f<T: $m::SszEncode>(v: &T) -> String {
            quiet(|| {
                let e = $m::SszEncode::to_ssz(v);
                let mut buf = PREFIX.to_vec();
                $m::SszEncode::ssz_append(v, &mut buf);
                let mut s = hex(&e);
                if buf[..PREFIX.len()] != PREFIX || buf[PREFIX.len()..] != e[..] {
                    s.push_str(&format!(" ssz_append={}", hex(&buf)));
                }
                let n = $m::SszEncode::encoded_len(v);
                if n != e.len() {
                    s.push_str(&format!(" encoded_len={n}"));
                }
                s
            })
            .unwrap_or("PANIC".into())
        }
    };
}
reenc_impl!(orig, reenc_orig);
reenc_impl!(verif, reenc_verif);

/// (decode, re-encode) in the format `DiffTest.lean` prints.
fn run_orig<T>(b: &[u8]) -> (String, String)
where
    T: orig::SszDecode + orig::SszEncode + Debug,
{
    quiet(|| match <T as orig::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_orig(&v);
            (format!("Ok({v:?})"), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

fn run_verif<T>(b: &[u8]) -> (String, String)
where
    T: verif::SszDecode + verif::SszEncode + Debug,
{
    quiet(|| match <T as verif::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_verif(&v);
            (format!("Ok({v:?})"), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

/// The paths that were `unsafe`/`memcpy` in `orig`, called directly.
fn fixed_paths_orig<T>(b: &[u8]) -> String
where
    T: orig::SszDecode + orig::SszEncode + Debug,
{
    quiet(|| match <T as orig::SszDecode>::ssz_decode_fixed_vec(b) {
        Ok(v) => {
            let mut buf = vec![0xAA];
            let re = quiet(|| {
                <T as orig::SszEncode>::ssz_append_fixed_slice(&v, &mut buf);
                hex(&buf)
            });
            format!("Ok({v:?}) {re:?}")
        }
        Err(e) => format!("Err({e:?})"),
    })
    .unwrap_or("PANIC".into())
}

fn fixed_paths_verif<T>(b: &[u8]) -> String
where
    T: verif::SszDecode + verif::SszEncode + Debug,
{
    quiet(|| match <T as verif::SszDecode>::ssz_decode_fixed_vec(b) {
        Ok(v) => {
            let mut buf = vec![0xAA];
            let re = quiet(|| {
                <T as verif::SszEncode>::ssz_append_fixed_slice(&v, &mut buf);
                hex(&buf)
            });
            format!("Ok({v:?}) {re:?}")
        }
        Err(e) => format!("Err({e:?})"),
    })
    .unwrap_or("PANIC".into())
}

// ── A container: { a: u64, b: Vec<u8>, c: bool, d: Vec<u16> } ──

type Cont = (u64, Vec<u8>, bool, Vec<u16>);
const CONT_FIXED: usize = 8 + 4 + 1 + 4;

macro_rules! container_impl {
    ($m:ident, $enc:ident, $dec:ident) => {
        fn $enc(x: &Cont) -> Vec<u8> {
            let mut buf = vec![0x55];
            let mut e = $m::ContainerEncoder::new(&mut buf, CONT_FIXED);
            e.append_fixed(&x.0);
            e.append_variable(&x.1);
            e.append_fixed(&x.2);
            e.append_variable(&x.3);
            e.finalize();
            buf
        }
        fn $dec(b: &[u8]) -> Result<Cont, $m::DecodeError> {
            let mut d = $m::ContainerDecoder::new(b, CONT_FIXED)?;
            let a = d.decode_fixed::<u64>()?;
            d.read_variable_offset()?;
            let c = d.decode_fixed::<bool>()?;
            d.read_variable_offset()?;
            let bb = d.decode_variable::<Vec<u8>>()?;
            let dd = d.decode_variable::<Vec<u16>>()?;
            Ok((a, bb, c, dd))
        }
    };
}
container_impl!(orig, cont_enc_orig, cont_dec_orig);
container_impl!(verif, cont_enc_verif, cont_dec_verif);

// ── A container with more than eight variable-size fields ──
//
// The `ContainerDecoder` of `verif` stores the first eight offsets inline and the rest in a
// `Vec`. This container has `vars` lists and a fixed `u16` after the fifth one, and `vars`
// goes from 7 to 12 to cover both sides of the boundary.

type Wide = (Vec<Vec<u8>>, u16);

macro_rules! wide_impl {
    ($m:ident, $enc:ident, $dec:ident) => {
        fn $enc(x: &Wide) -> Vec<u8> {
            let mut buf = vec![0x55];
            let mut e = $m::ContainerEncoder::new(&mut buf, 4 * x.0.len() + 2);
            for (i, f) in x.0.iter().enumerate() {
                if i == 5 {
                    e.append_fixed(&x.1);
                }
                e.append_variable(f);
            }
            e.finalize();
            buf
        }
        fn $dec(b: &[u8], vars: usize) -> Result<Wide, $m::DecodeError> {
            let mut d = $m::ContainerDecoder::new(b, 4 * vars + 2)?;
            let mut fixed = 0u16;
            for i in 0..vars {
                if i == 5 {
                    fixed = d.decode_fixed::<u16>()?;
                }
                d.read_variable_offset()?;
            }
            let mut fields = Vec::new();
            for _ in 0..vars {
                fields.push(d.decode_variable::<Vec<u8>>()?);
            }
            Ok((fields, fixed))
        }
    };
}
wide_impl!(orig, wide_enc_orig, wide_dec_orig);
wide_impl!(verif, wide_enc_verif, wide_dec_verif);

// ── Sequences of operations on `ContainerEncoder` ──
//
// The `append_fixed` of `verif` writes the field directly in place if the type allows it
// (`ssz_write_fixed`), and otherwise appends it at the end and moves it, like `orig`.
// `Plain` is a type from outside the library that implements only the required methods of
// the trait, so it takes the second path.

#[derive(Debug, Clone, Copy)]
struct Plain([u8; 3]);

macro_rules! plain_impl {
    ($m:ident) => {
        impl $m::SszEncode for Plain {
            fn is_fixed_size() -> bool {
                true
            }
            fn fixed_size() -> usize {
                3
            }
            fn encoded_len(&self) -> usize {
                3
            }
            fn ssz_append(&self, buf: &mut Vec<u8>) {
                buf.extend_from_slice(&self.0);
            }
        }
    };
}
plain_impl!(orig);
plain_impl!(verif);

#[derive(Debug, Clone)]
enum Op {
    U64(u64),
    U16(u16),
    U128(u128),
    Bool(bool),
    B4([u8; 4]),
    Plain(Plain),
    Cp(u64, [u8; 32]),
    Val(Box<[u8; 121]>),
    VarU8(Vec<u8>),
    VarU64(Vec<u64>),
    VarPlain(Vec<Plain>),
}

impl Op {
    fn gen(r: &mut Rng) -> Op {
        match r.below(11) {
            0 => Op::U64(Gen::gen(r)),
            1 => Op::U16(Gen::gen(r)),
            2 => Op::U128(Gen::gen(r)),
            3 => Op::Bool(Gen::gen(r)),
            4 => Op::B4(Gen::gen(r)),
            5 => Op::Plain(Plain(Gen::gen(r))),
            6 => Op::Cp(Gen::gen(r), Gen::gen(r)),
            7 => {
                let mut b: [u8; 121] = Gen::gen(r);
                b[88] = r.below(2) as u8;
                Op::Val(Box::new(b))
            }
            8 => Op::VarU8(Gen::gen(r)),
            9 => Op::VarU64(Gen::gen(r)),
            _ => {
                let n = r.below(4) as usize;
                Op::VarPlain((0..n).map(|_| Plain(Gen::gen(r))).collect())
            }
        }
    }
    /// Its size in the fixed part of the container.
    fn fixed_len(&self) -> usize {
        match self {
            Op::U64(_) => 8,
            Op::U16(_) => 2,
            Op::U128(_) => 16,
            Op::Bool(_) => 1,
            Op::B4(_) => 4,
            Op::Plain(_) => 3,
            Op::Cp(..) => 40,
            Op::Val(_) => 121,
            Op::VarU8(_) | Op::VarU64(_) | Op::VarPlain(_) => 4,
        }
    }
}

macro_rules! ops_impl {
    ($m:ident, $f:ident, $cp:ty, $val:ty) => {
        /// Runs `ops` on a `ContainerEncoder` that starts on a buffer with `prefix`, with
        /// `fixed_part_len` declared (correctly or not). `None` if it panics.
        fn $f(
            prefix: &[u8],
            fixed_part_len: usize,
            hint: Option<usize>,
            ops: &[Op],
        ) -> Option<Vec<u8>> {
            quiet(|| {
                let mut buf = prefix.to_vec();
                let mut e = match hint {
                    Some(total) => {
                        $m::ContainerEncoder::with_capacity(&mut buf, fixed_part_len, total)
                    }
                    None => $m::ContainerEncoder::new(&mut buf, fixed_part_len),
                };
                for op in ops {
                    match op {
                        Op::U64(x) => e.append_fixed(x),
                        Op::U16(x) => e.append_fixed(x),
                        Op::U128(x) => e.append_fixed(x),
                        Op::Bool(x) => e.append_fixed(x),
                        Op::B4(x) => e.append_fixed(x),
                        Op::Plain(x) => e.append_fixed(x),
                        Op::Cp(epoch, root) => e.append_fixed(&<$cp>::from_parts(*epoch, *root)),
                        Op::Val(b) => {
                            let v = <$val as $m::SszDecode>::from_ssz_bytes(&b[..]).unwrap();
                            e.append_fixed(&v)
                        }
                        Op::VarU8(x) => e.append_variable(x),
                        Op::VarU64(x) => e.append_variable(x),
                        Op::VarPlain(x) => e.append_variable(x),
                    }
                }
                e.finalize();
                buf
            })
        }
    };
}

trait FromParts {
    fn from_parts(epoch: u64, root: [u8; 32]) -> Self;
}
impl FromParts for CheckpointD {
    fn from_parts(epoch: u64, root: [u8; 32]) -> Self {
        CheckpointD { epoch, root }
    }
}
impl FromParts for vx::Checkpoint {
    fn from_parts(epoch: u64, root: [u8; 32]) -> Self {
        vx::Checkpoint { epoch, root }
    }
}
ops_impl!(orig, ops_orig, CheckpointD, ValidatorD);
ops_impl!(verif, ops_verif, vx::Checkpoint, vx::Validator);

// ── The example container ──
//
// `verif::verif_example::Example` uses the derive macro of libssz in this repository. Here it
// is compared with an identical struct that uses the derive macro of `orig`.

#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct ExDerive {
    a: u64,
    b: Vec<u8>,
    c: bool,
    d: Vec<u16>,
}

fn run_ex_orig(b: &[u8]) -> (String, String) {
    quiet(|| match <ExDerive as orig::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_orig(&v);
            (format!("Ok({:?})", (v.a, &v.b, v.c, &v.d)), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

fn run_ex_verif(b: &[u8]) -> (String, String) {
    use verif::verif_example::Example;
    quiet(|| match <Example as verif::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_verif(&v);
            (format!("Ok({:?})", (v.a, &v.b, v.c, &v.d)), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

/// Valid encodings, with a flipped bit, truncated, and random bytes.
fn ex_corpus(r: &mut Rng) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..2000 {
        let x = ExDerive {
            a: Gen::gen(r),
            b: Gen::gen(r),
            c: Gen::gen(r),
            d: Gen::gen(r),
        };
        let e = orig::SszEncode::to_ssz(&x);
        let mut m = e.clone();
        let i = r.below(m.len() as u64) as usize;
        m[i] ^= 1 << r.below(8);
        let cut = r.below(e.len() as u64) as usize;
        let len = r.below(40) as usize;
        out.push(e.clone());
        out.push(m);
        out.push(e[..cut].to_vec());
        out.push(r.bytes(len));
    }
    out
}

// ── Fixed-size consensus-layer containers ──
//
// The same structs as in `verif::verif_example`, with the derive macro of `orig`. They are
// printed as tuples (nested ones too), as in `DiffTest.lean`.

trait Tup {
    fn tup(&self) -> String;
}
impl Tup for u64 {
    fn tup(&self) -> String {
        format!("{self}")
    }
}
impl Tup for bool {
    fn tup(&self) -> String {
        format!("{self}")
    }
}
impl<const N: usize> Tup for [u8; N] {
    fn tup(&self) -> String {
        format!("{self:?}")
    }
}
impl<T: Tup> Tup for Vec<T> {
    fn tup(&self) -> String {
        let v: Vec<String> = self.iter().map(|x| x.tup()).collect();
        format!("[{}]", v.join(", "))
    }
}
macro_rules! tup_impl {
    ($t:ty { $($f:ident),* }) => {
        impl Tup for $t {
            fn tup(&self) -> String {
                let v: Vec<String> = vec![$(self.$f.tup()),*];
                format!("({})", v.join(", "))
            }
        }
    };
}

#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct CheckpointD {
    epoch: u64,
    root: [u8; 32],
}
#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct ForkD {
    previous_version: [u8; 4],
    current_version: [u8; 4],
    epoch: u64,
}
#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct BeaconBlockHeaderD {
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
}
#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct ValidatorD {
    pubkey: [u8; 48],
    withdrawal_credentials: [u8; 32],
    effective_balance: u64,
    slashed: bool,
    activation_eligibility_epoch: u64,
    activation_epoch: u64,
    exit_epoch: u64,
    withdrawable_epoch: u64,
}
#[derive(orig_derive::SszEncode, orig_derive::SszDecode)]
struct AttestationDataD {
    slot: u64,
    index: u64,
    beacon_block_root: [u8; 32],
    source: CheckpointD,
    target: CheckpointD,
}

mod vx {
    pub use verif::verif_example::*;
}
tup_impl!(CheckpointD { epoch, root });
tup_impl!(vx::Checkpoint { epoch, root });
tup_impl!(ForkD {
    previous_version,
    current_version,
    epoch
});
tup_impl!(vx::Fork {
    previous_version,
    current_version,
    epoch
});
tup_impl!(BeaconBlockHeaderD {
    slot,
    proposer_index,
    parent_root,
    state_root,
    body_root
});
tup_impl!(vx::BeaconBlockHeader {
    slot,
    proposer_index,
    parent_root,
    state_root,
    body_root
});
tup_impl!(ValidatorD {
    pubkey,
    withdrawal_credentials,
    effective_balance,
    slashed,
    activation_eligibility_epoch,
    activation_epoch,
    exit_epoch,
    withdrawable_epoch
});
tup_impl!(vx::Validator {
    pubkey,
    withdrawal_credentials,
    effective_balance,
    slashed,
    activation_eligibility_epoch,
    activation_epoch,
    exit_epoch,
    withdrawable_epoch
});
tup_impl!(AttestationDataD {
    slot,
    index,
    beacon_block_root,
    source,
    target
});
tup_impl!(vx::AttestationData {
    slot,
    index,
    beacon_block_root,
    source,
    target
});

fn run_tup_orig<T: orig::SszDecode + orig::SszEncode + Tup>(b: &[u8]) -> (String, String) {
    quiet(|| match <T as orig::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_orig(&v);
            (format!("Ok({})", v.tup()), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

fn run_tup_verif<T: verif::SszDecode + verif::SszEncode + Tup>(b: &[u8]) -> (String, String) {
    quiet(|| match <T as verif::SszDecode>::from_ssz_bytes(b) {
        Ok(v) => {
            let re = reenc_verif(&v);
            (format!("Ok({})", v.tup()), re)
        }
        Err(e) => (format!("Err({e:?})"), "-".into()),
    })
    .unwrap_or(("PANIC".into(), "-".into()))
}

/// Inputs for a fixed-size container of `w` bytes: lengths `w - 1`, `w`, `w + 1` and random.
/// If `bool_at` is a `bool` byte, half of the time it is set to 0 or 1.
fn fixed_corpus(r: &mut Rng, w: usize, bool_at: Option<usize>) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for _ in 0..1000 {
        let mut b = r.bytes(w);
        if let Some(i) = bool_at {
            if r.below(2) == 0 {
                b[i] = r.below(2) as u8;
            }
        }
        out.push(b.clone());
        out.push(b[..w - 1].to_vec());
        let mut longer = b;
        longer.push(r.next() as u8);
        out.push(longer);
        let len = r.below(2 * w as u64) as usize;
        out.push(r.bytes(len));
    }
    out
}

macro_rules! fixed_ty {
    ($name:expr, $o:ty, $v:ty, $w:expr, $bool_at:expr) => {
        Ty {
            name: $name,
            orig: run_tup_orig::<$o>,
            verif: run_tup_verif::<$v>,
            fixed: None,
            corpus: |r| fixed_corpus(r, $w, $bool_at),
            lean_corpus: None,
            lean: true,
            exact_errors: true,
        }
    };
}

/// Lists of fixed-size containers: `Vec<S>`.
macro_rules! fixed_list_ty {
    ($name:expr, $o:ty, $v:ty, $w:expr, $bool_at:expr) => {
        Ty {
            name: $name,
            orig: run_tup_orig::<Vec<$o>>,
            verif: run_tup_verif::<Vec<$v>>,
            fixed: None,
            corpus: |r| fixed_list_corpus(r, $w, $bool_at),
            lean_corpus: None,
            lean: true,
            exact_errors: false,
        }
    };
}

// ── Type table ──

type Runner = fn(&[u8]) -> (String, String);

struct Ty {
    name: &'static str,
    orig: Runner,
    verif: Runner,
    fixed: Option<(fn(&[u8]) -> String, fn(&[u8]) -> String)>,
    corpus: fn(&mut Rng) -> Vec<Vec<u8>>,
    /// Inputs for the Lean model, if they are not those of `corpus`. The executed model is
    /// slow on long lists (its "vectors" are linked lists), so those are shorter there.
    lean_corpus: Option<fn(&mut Rng) -> Vec<Vec<u8>>>,
    /// Whether `DiffTest.lean` supports it, and whether its errors correspond (`ErrMatch`).
    lean: bool,
    exact_errors: bool,
}

macro_rules! ty {
    ($name:expr, $t:ty, fixed, $lean:expr, $exact:expr, $c:expr) => {
        Ty {
            name: $name,
            orig: run_orig::<$t>,
            verif: run_verif::<$t>,
            fixed: Some((fixed_paths_orig::<$t>, fixed_paths_verif::<$t>)),
            corpus: $c,
            lean_corpus: None,
            lean: $lean,
            exact_errors: $exact,
        }
    };
    ($name:expr, $t:ty, var, $lean:expr, $exact:expr, $c:expr) => {
        Ty {
            name: $name,
            orig: run_orig::<$t>,
            verif: run_verif::<$t>,
            fixed: None,
            corpus: $c,
            lean_corpus: None,
            lean: $lean,
            exact_errors: $exact,
        }
    };
    // Long lists of `$t`: decode and encode of `Vec<$t>`, plus the blockwise paths of `$t`
    // called directly on the same bytes. Up to 300 items between the two Rust versions, and
    // up to `$lean_max` in the Lean model.
    ($name:expr, $t:ty, big, $n:expr, $lean_max:expr) => {
        Ty {
            name: $name,
            orig: run_orig::<Vec<$t>>,
            verif: run_verif::<Vec<$t>>,
            fixed: Some((fixed_paths_orig::<$t>, fixed_paths_verif::<$t>)),
            corpus: |r| big_corpus::<$t>(r, $n, 300),
            lean_corpus: Some(|r| big_corpus::<$t>(r, $n, $lean_max)),
            lean: true,
            exact_errors: false,
        }
    };
    // Lists of `$t` larger than 8 KB, with lengths close to a multiple of `$block` items. The
    // Lean model runs only those of lengths `$lean_lens` (see `blk_lean_corpus`).
    ($name:expr, $t:ty, blk, $block:expr, $lean_lens:expr) => {
        Ty {
            name: $name,
            orig: run_orig::<Vec<$t>>,
            verif: run_verif::<Vec<$t>>,
            fixed: Some((fixed_paths_orig::<$t>, fixed_paths_verif::<$t>)),
            corpus: |r| blk_corpus::<$t>(r, $block),
            lean_corpus: Some(|r| blk_lean_corpus::<$t>(r, &$lean_lens)),
            lean: true,
            exact_errors: false,
        }
    };
}

/// The type name for `DiffTest.lean`: long lists use the same codec.
fn lean_name(name: &str) -> &str {
    name.strip_prefix("big-")
        .or(name.strip_prefix("blk-"))
        .unwrap_or(name)
}

fn types() -> Vec<Ty> {
    vec![
        ty!("bool", bool, fixed, true, true, |_| exhaustive2()),
        ty!("u8", u8, fixed, true, true, |_| exhaustive2()),
        ty!("u16", u16, fixed, true, true, |_| exhaustive2()),
        ty!("u32", u32, fixed, true, true, |r| corpus::<u32>(r, 2000)),
        ty!("u64", u64, fixed, true, true, |r| corpus::<u64>(r, 2000)),
        ty!("u128", u128, fixed, true, true, |r| corpus::<u128>(r, 2000)),
        ty!("b4", [u8; 4], fixed, true, true, |r| corpus::<[u8; 4]>(
            r, 2000
        )),
        ty!("b32", [u8; 32], fixed, true, true, |r| corpus::<[u8; 32]>(
            r, 1000
        )),
        ty!(
            "vbool",
            Vec<bool>,
            var,
            true,
            false,
            |r| corpus::<Vec<bool>>(r, 2000)
        ),
        ty!("vu8", Vec<u8>, var, true, false, |r| corpus::<Vec<u8>>(
            r, 2000
        )),
        ty!("vu16", Vec<u16>, var, true, false, |r| corpus::<Vec<u16>>(
            r, 2000
        )),
        ty!("vu64", Vec<u64>, var, true, false, |r| corpus::<Vec<u64>>(
            r, 2000
        )),
        ty!(
            "vu128",
            Vec<u128>,
            var,
            true,
            false,
            |r| corpus::<Vec<u128>>(r, 2000)
        ),
        ty!("vb4", Vec<[u8; 4]>, var, true, false, |r| corpus::<
            Vec<[u8; 4]>,
        >(r, 2000)),
        ty!("vvu8", Vec<Vec<u8>>, var, true, false, |r| corpus::<
            Vec<Vec<u8>>,
        >(
            r, 2000
        )),
        ty!("vvu64", Vec<Vec<u64>>, var, true, false, |r| corpus::<
            Vec<Vec<u64>>,
        >(
            r, 2000
        )),
        ty!("vvvu8", Vec<Vec<Vec<u8>>>, var, true, false, |r| corpus::<
            Vec<Vec<Vec<u8>>>,
        >(
            r, 2000
        )),
        ty!("big-vbool", bool, big, 60, 300),
        ty!("big-vu8", u8, big, 60, 300),
        ty!("big-vu16", u16, big, 60, 200),
        ty!("big-vu32", u32, big, 60, 150),
        ty!("big-vu64", u64, big, 60, 100),
        ty!("big-vu128", u128, big, 60, 64),
        ty!("big-vb4", [u8; 4], big, 60, 150),
        ty!("big-vb32", [u8; 32], big, 40, 48),
        ty!("big-vb48", [u8; 48], big, 40, 32),
        ty!("blk-vbool", bool, blk, 8192, []),
        ty!("blk-vu8", u8, blk, 8192, [8193]),
        ty!("blk-vu16", u16, blk, 4096, [4095, 4097]),
        ty!("blk-vu32", u32, blk, 2048, [2047, 2048, 2049]),
        ty!("blk-vu64", u64, blk, 1024, [1023, 1024, 1025, 2051]),
        ty!("blk-vu128", u128, blk, 512, [511, 512, 513, 1027, 1792]),
        ty!("blk-vb32", [u8; 32], blk, 256, [257]),
        fixed_ty!("cp", CheckpointD, vx::Checkpoint, 40, None),
        fixed_ty!("fork", ForkD, vx::Fork, 16, None),
        fixed_ty!("bbh", BeaconBlockHeaderD, vx::BeaconBlockHeader, 112, None),
        fixed_ty!("val", ValidatorD, vx::Validator, 121, Some(88)),
        fixed_ty!("ad", AttestationDataD, vx::AttestationData, 128, None),
        fixed_list_ty!("vcp", CheckpointD, vx::Checkpoint, 40, None),
        fixed_list_ty!("vval", ValidatorD, vx::Validator, 121, Some(88)),
        fixed_list_ty!("vad", AttestationDataD, vx::AttestationData, 128, None),
        Ty {
            name: "ex",
            orig: run_ex_orig,
            verif: run_ex_verif,
            fixed: None,
            corpus: ex_corpus,
            lean_corpus: None,
            lean: true,
            exact_errors: false,
        },
    ]
}

fn silence_panics() {
    std::panic::set_hook(Box::new(|_| {}));
}

// ── (A) orig vs verif ──

#[test]
fn orig_vs_verif() {
    silence_panics();
    let mut r = Rng(0x55AA);
    let mut total = 0;
    let mut wide_ok: BTreeMap<bool, usize> = BTreeMap::new();
    for t in types().into_iter().filter(|t| selected(t.name)) {
        let inputs = (t.corpus)(&mut r);
        for b in &inputs {
            check_eq!((t.orig)(b), (t.verif)(b), "{} decode {}", t.name, hex(b));
            if let Some((fo, fv)) = t.fixed {
                check_eq!(fo(b), fv(b), "{} fixed-vec {}", t.name, hex(b));
            }
            total += 1;
        }
    }
    // Container: decode of valid, mutated and random encodings; encode of values.
    for _ in 0..if selected("cont") { 5000 } else { 0 } {
        let x: Cont = (
            Gen::gen(&mut r),
            Gen::gen(&mut r),
            Gen::gen(&mut r),
            Gen::gen(&mut r),
        );
        let eo = cont_enc_orig(&x);
        check_eq!(eo, cont_enc_verif(&x), "container encode {x:?}");
        let mut inputs = vec![eo[1..].to_vec()];
        let mut m = eo[1..].to_vec();
        let i = r.below(m.len() as u64) as usize;
        m[i] ^= 1 << r.below(8);
        inputs.push(m);
        let cut = r.below(eo.len() as u64) as usize;
        inputs.push(eo[1..1 + cut.min(eo.len() - 1)].to_vec());
        let len = r.below(40) as usize;
        inputs.push(r.bytes(len));
        for b in &inputs {
            let o = quiet(|| format!("{:?}", cont_dec_orig(b)));
            let v = quiet(|| format!("{:?}", cont_dec_verif(b)));
            check_eq!(o, v, "container decode {}", hex(b));
            total += 1;
        }
    }
    // Container with 7 to 12 variable-size fields: more than eight offsets.
    for _ in 0..if selected("wide") { 3000 } else { 0 } {
        let vars = 7 + r.below(6) as usize;
        let x: Wide = (
            (0..vars).map(|_| Gen::gen(&mut r)).collect(),
            Gen::gen(&mut r),
        );
        let eo = wide_enc_orig(&x);
        check_eq!(eo, wide_enc_verif(&x), "wide encode {x:?}");
        let valid = eo[1..].to_vec();
        let mut inputs = Vec::new();
        mutations(&mut r, valid.clone(), &mut inputs);
        // One offset replaced by another small value: out of order, out of range, etc.
        let mut m = valid;
        let k = r.below(vars as u64) as usize;
        let pos = 4 * k + if k >= 5 { 2 } else { 0 };
        let v = (r.below(m.len() as u64 + 8) as u32).to_le_bytes();
        m[pos..pos + 4].copy_from_slice(&v);
        inputs.push(m);
        for b in &inputs {
            let o = quiet(|| format!("{:?}", wide_dec_orig(b, vars)));
            let v = quiet(|| format!("{:?}", wide_dec_verif(b, vars)));
            check_eq!(o, v, "wide decode ({vars} fields) {}", hex(b));
            if let Some(s) = &o {
                *wide_ok.entry(s.starts_with("Ok")).or_default() += 1;
            }
            total += 1;
        }
    }
    // Sequences of operations on `ContainerEncoder`, with the length of the fixed part
    // declared correctly (lawful use) or not (shorter or longer: both must give the same
    // buffer or both must panic).
    let (mut lawful, mut unlawful, mut panics) = (0, 0, 0);
    for _ in 0..if selected("ops") { 20000 } else { 0 } {
        let n = r.below(9) as usize;
        let ops: Vec<Op> = (0..n).map(|_| Op::gen(&mut r)).collect();
        let exact: usize = ops.iter().map(|o| o.fixed_len()).sum();
        let declared = match r.below(4) {
            0 => r.below(exact as u64 + 1) as usize,
            1 => exact + 1 + r.below(8) as usize,
            _ => exact,
        };
        let plen = r.below(4) as usize;
        let prefix = r.bytes(plen);
        let hint = if r.below(2) == 0 {
            Some(declared + r.below(64) as usize)
        } else {
            None
        };
        let o = ops_orig(&prefix, declared, hint, &ops);
        let v = ops_verif(&prefix, declared, hint, &ops);
        check_eq!(
            o,
            v,
            "ContainerEncoder {prefix:?} {declared} (exact {exact}) {hint:?} {ops:?}"
        );
        if declared == exact {
            assert!(
                o.is_some(),
                "ContainerEncoder: panic in a lawful use {ops:?}"
            );
            lawful += 1;
        } else {
            unlawful += 1;
        }
        if o.is_none() {
            panics += 1;
        }
        total += 1;
    }
    println!(
        "  wide container: {} decodes Ok, {} Err; ContainerEncoder: {lawful} lawful \
         sequences, {unlawful} with a wrongly declared fixed part ({panics} panics, identical)",
        wide_ok.get(&true).copied().unwrap_or(0),
        wide_ok.get(&false).copied().unwrap_or(0),
    );
    // decode_list_with_max with small limits.
    for _ in 0..if selected("list-max") { 5000 } else { 0 } {
        let b = orig::SszEncode::to_ssz(&<Vec<u16>>::gen(&mut r));
        let max = r.below(5) as usize;
        let o = format!("{:?}", orig::decode_list_with_max::<u16>(&b, max));
        let v = format!("{:?}", verif::decode_list_with_max::<u16>(&b, max));
        check_eq!(o, v, "decode_list_with_max {} {max}", hex(&b));
        total += 1;
    }
    println!("orig vs {}: {total} cases, all identical", version());
}

// ── (B) Lean model and EthLib vs Rust ──

fn version() -> &'static str {
    "libssz"
}

/// The Lean executable with the model of libssz and the EthLib spec.
fn lean_exe() -> String {
    std::env::var("LEAN_DIFFTEST").unwrap_or_else(|_| {
        format!(
            "{}/../lean/.lake/build/bin/difftest",
            env!("CARGO_MANIFEST_DIR")
        )
    })
}

fn status(s: &str) -> &str {
    if s.starts_with("Ok(") {
        "Ok"
    } else if s.starts_with("Err(") {
        "Err"
    } else {
        s
    }
}

fn err_kind(s: &str) -> String {
    s.trim_start_matches("Err(")
        .split(|c: char| c == ' ' || c == '(' || c == ')')
        .next()
        .unwrap_or("")
        .to_string()
}

#[test]
fn lean_model_and_spec() {
    silence_panics();
    let mut r = Rng(0xC0FFEE);
    let mut cases: Vec<(usize, Vec<u8>)> = Vec::new();
    let tys = types();
    for (i, t) in tys.iter().enumerate() {
        if t.lean && selected(t.name) {
            for b in (t.lean_corpus.unwrap_or(t.corpus))(&mut r) {
                cases.push((i, b));
            }
        }
    }
    let mut input = String::new();
    for (i, b) in &cases {
        input.push_str(&format!("{} {}\n", lean_name(tys[*i].name), hex(b)));
    }
    let mut child = Command::new(lean_exe())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Lean executable not found: run `lake build difftest` in ../lean");
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()).unwrap());
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    let out = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines.len(),
        cases.len(),
        "the Lean executable did not answer every case"
    );

    let mut model_mismatch = Vec::new();
    let mut spec_mismatch = Vec::new();
    let mut err_pairs: BTreeMap<(String, String, String), usize> = BTreeMap::new();
    for ((i, b), line) in cases.iter().zip(&lines) {
        let t = &tys[*i];
        let f: Vec<&str> = line.split('\t').collect();
        let (md, me, sd, se) = (f[0], f[1], f[2], f[3]);
        let (rd, re) = (t.verif)(b);
        if (md, me) != (rd.as_str(), re.as_str()) {
            model_mismatch.push(format!(
                "{} {}: Rust {} {} / model {} {}",
                t.name,
                clip(&hex(b)),
                clip(&rd),
                clip(&re),
                clip(md),
                clip(me)
            ));
        }
        let same = if t.exact_errors {
            (sd, se) == (rd.as_str(), re.as_str())
        } else if status(&rd) == "Ok" {
            (sd, se) == (rd.as_str(), re.as_str())
        } else {
            status(sd) == status(&rd)
        };
        if !same {
            spec_mismatch.push(format!(
                "{} {}: Rust {} {} / EthLib {} {}",
                t.name,
                clip(&hex(b)),
                clip(&rd),
                clip(&re),
                clip(sd),
                clip(se)
            ));
        } else if status(&rd) == "Err" {
            *err_pairs
                .entry((t.name.to_string(), err_kind(&rd), err_kind(sd)))
                .or_default() += 1;
        }
    }
    println!(
        "Lean model of {} and EthLib vs Rust: {} cases",
        version(),
        cases.len()
    );
    println!("error pairs (type, libssz, EthLib) on inputs both reject:");
    for ((ty, a, b), n) in &err_pairs {
        println!("  {ty:6} {a:40} {b:30} {n}");
    }
    for m in model_mismatch.iter().take(20) {
        println!("MODEL ≠ RUST  {m}");
    }
    for m in spec_mismatch.iter().take(40) {
        println!("ETHLIB ≠ RUST  {m}");
    }
    assert!(
        model_mismatch.is_empty(),
        "{} model/Rust mismatches",
        model_mismatch.len()
    );
    assert!(
        spec_mismatch.is_empty(),
        "{} EthLib/Rust mismatches",
        spec_mismatch.len()
    );
}
