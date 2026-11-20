module
public import Libssz.Merkle.Intrinsics
@[expose] public section

/-!
# Hand-written models of the Arm instructions of the AArch64 SHA-256 kernel

`crates/ssz-merkle/src/neon.rs` computes SHA-256 of two nodes with eight intrinsics from
`core::arch::aarch64`. Aeneas cannot extract them: in `core` they are calls into LLVM, with no
Rust body. This file states what we **assume** each one does. It is part of the trusted
computing base (TCB): the theorems in `MerkleNeon/Proofs/` are about these definitions, not
about the processor.

A `uint32x4_t` is modeled as four 32-bit lanes, just like an `__m128i` in the x86 kernel
(`Merkle/Intrinsics.lean`): lane `l` is bits `32·l` to `32·l + 31`. The kernel is only
compiled for little-endian AArch64, where lane 0 is also the first `u32` in memory.

Sources: the Arm manual (*Arm Architecture Reference Manual for A-profile*, the instructions
`SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1`, `ADD (vector)`, `DUP`, `INS`, `UMOV`, and the
functions `SHA256hash`, `SHAchoose`, `SHAmajority`, `SHAhashSIGMA0`, `SHAhashSIGMA1` of its
pseudocode), the intrinsics specification (ACLE) and Rust's `stdarch`
(`core_arch/src/arm_shared/neon/generated.rs`). We wrote them ourselves; the FIPS 180-4
functions (σ0, σ1, Σ0, Σ1, Ch, Maj) are those of the x86 model.

* The manual's `SHAchoose(x, y, z)` is `((y EOR z) AND x) EOR z` and `SHAmajority(x, y, z)`
  is `(x AND y) OR ((x OR y) AND z)`. Bit by bit they are FIPS 180-4's Ch and Maj, which is
  how they are written here.
* **The operand order of `vsha256h2q_u32`.** ACLE declares it as
  `vsha256h2q_u32(hash_efgh, hash_abcd, wk)`: the first operand is `Qd` (EFGH) and the second
  `Qn` (ABCD), and that is how the `sha2` crate uses it. In `stdarch` the parameters are named
  the other way around (`hash_abcd, hash_efgh`), but they are passed in that order to
  `llvm.aarch64.crypto.sha256h2`, which is the instruction with `Qd`, `Qn`, `Vm`. The model
  follows the operand order.

The immediate arguments (`LANE`, `IMM5`) model the valid range of Rust's const generic (0 to
3: `stdarch` checks it at compile time).
-/

namespace Libssz.MerkleNeon

open Libssz.Merkle.Intrinsics (choose majority bigSigma0 bigSigma1 smallSigma0
  smallSigma1)

/-- `uint32x4_t`: lane `l` holds bits `32·l` to `32·l + 31`. -/
abbrev U32x4 := Vector UInt32 4

/-- `vaddq_u32(a, b)` (`ADD Vd.4S, Vn.4S, Vm.4S`): lane-wise addition, modulo 2³². -/
def vaddq_u32 (a b : U32x4) : U32x4 := .ofFn fun l => a[l] + b[l]

/-- `vdupq_n_u32(x)` (`DUP Vd.4S, Wn`): `x` in all four lanes. -/
def vdupq_n_u32 (x : UInt32) : U32x4 := .ofFn fun _ => x

/-- `vsetq_lane_u32::<LANE>(x, v)` (`INS Vd.S[LANE], Wn`): `v` with `x` in lane `LANE`. -/
def vsetq_lane_u32 (lane : Nat) (x : UInt32) (v : U32x4) : U32x4 :=
  .ofFn fun l => if l.val = lane % 4 then x else v[l]

/-- `vgetq_lane_u32::<IMM5>(v)` (`UMOV Wd, Vn.S[IMM5]`): lane `IMM5`. -/
def vgetq_lane_u32 (lane : Nat) (v : U32x4) : UInt32 :=
  v[(⟨lane % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)]

/-- `vsha256su0q_u32(a, b)` (`SHA256SU0 Vd.4S, Vn.4S`, with `Vd = a`, `Vn = b`): the first
half of computing four new schedule words. The manual builds `T = b<31:0> : a<127:32>` and
leaves in lane `e` the `σ0` of lane `e` of `T` plus lane `e` of `a`. -/
def vsha256su0q_u32 (a b : U32x4) : U32x4 :=
  let t : U32x4 := #v[a[1], a[2], a[3], b[0]]
  .ofFn fun e => smallSigma0 t[e] + a[e]

/-- `vsha256su1q_u32(a, b, c)` (`SHA256SU1 Vd.4S, Vn.4S, Vm.4S`, with `Vd = a`, `Vn = b`,
`Vm = c`): the second half, which adds `σ1`. The manual builds `T0 = c<31:0> : b<127:32>`;
the two low lanes take `σ1` from the two high lanes of `c`, and the two high lanes from the
two low lanes just computed. -/
def vsha256su1q_u32 (a b c : U32x4) : U32x4 :=
  let t0 : U32x4 := #v[b[1], b[2], b[3], c[0]]
  let r0 := smallSigma1 c[2] + a[0] + t0[0]
  let r1 := smallSigma1 c[3] + a[1] + t0[1]
  let r2 := smallSigma1 r0 + a[2] + t0[2]
  let r3 := smallSigma1 r1 + a[3] + t0[3]
  #v[r0, r1, r2, r3]

/-- One iteration of the manual's `SHA256hash` loop: one round. `x` is ABCD and `y` is EFGH
(A and E in lane 0). The manual writes the round into the high lanes and then rotates the 256
bits of `y : x` left by 32 bits: each lane moves up one, the high lane of `x` goes to the low
lane of `y`, and the high lane of `y` to the low lane of `x`. -/
def hashRound (x y : U32x4) (w : UInt32) : U32x4 × U32x4 :=
  let chs := choose y[0] y[1] y[2]
  let maj := majority x[0] x[1] x[2]
  let t := y[3] + bigSigma1 y[0] + chs + w
  let x3 := t + x[3]
  let y3 := t + bigSigma0 x[0] + maj
  (#v[y3, x[0], x[1], x[2]], #v[x3, y[0], y[1], y[2]])

/-- The manual's `SHA256hash(x, y, w)`: four rounds, with `w` the four schedule words already
added to their constants. It returns both values; `SHA256H` keeps the first and `SHA256H2`
the second. -/
def sha256hash (x y w : U32x4) : U32x4 × U32x4 :=
  let r0 := hashRound x y w[0]
  let r1 := hashRound r0.1 r0.2 w[1]
  let r2 := hashRound r1.1 r1.2 w[2]
  hashRound r2.1 r2.2 w[3]

/-- `vsha256hq_u32(hash_abcd, hash_efgh, wk)` (`SHA256H Qd, Qn, Vm.4S`, with `Qd = hash_abcd`,
`Qn = hash_efgh`): ABCD after four rounds. -/
def vsha256hq_u32 (hash_abcd hash_efgh wk : U32x4) : U32x4 :=
  (sha256hash hash_abcd hash_efgh wk).1

/-- `vsha256h2q_u32(hash_efgh, hash_abcd, wk)` (`SHA256H2 Qd, Qn, Vm.4S`, with
`Qd = hash_efgh`, `Qn = hash_abcd`): EFGH after the same four rounds. The manual calls
`SHA256hash(V[n], V[d], …)`: both instructions start from the same ABCD and EFGH. -/
def vsha256h2q_u32 (hash_efgh hash_abcd wk : U32x4) : U32x4 :=
  (sha256hash hash_abcd hash_efgh wk).2

end Libssz.MerkleNeon
