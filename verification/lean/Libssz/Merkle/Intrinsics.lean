module
public import Std
@[expose] public section

/-!
# Hand-written models of the x86 instructions of the SHA-NI kernel

`crates/ssz-merkle/src/shani.rs` computes SHA-256 of two nodes with eight intrinsics from
`core::arch::x86_64`. Aeneas cannot extract them: in `core` they are calls into LLVM, with no
Rust body. This file states what we **assume** each one does. It is part of the trusted
computing base (TCB): the theorems in `Merkle/Proofs/` are about these definitions, not about
the processor.

An `__m128i` is modeled as four 32-bit lanes. Lane `l` is bits `32·l` to `32·l + 31`, so
lane 0 is the least significant.

Sources: the Intel® Intrinsics Guide and the Intel manual (SDM vol. 2B, the sections on
`SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2`, `PSHUFD`, `PALIGNR`, `PEXTRD`, `PADDD`), and Rust's
`stdarch` (`core_arch/src/x86/{sse2,ssse3,sse41,sha}.rs`).

Six of the eight models (`_mm_add_epi32`, `_mm_shuffle_epi32`, `_mm_alignr_epi8` and the
three SHA ones) are taken from `LeanBlsSimd/Model/ShaIntrinsics.lean` in the
gattaca-com/silver repository, which publishes them under CC0. `_mm_set_epi32` and
`_mm_extract_epi32` are ours.

The immediate arguments (`imm`) model the valid range of Rust's const generic.
-/

namespace Libssz.Merkle

/-- `__m128i`: lane `l` holds bits `32·l` to `32·l + 31`. -/
abbrev M128 := Vector UInt32 4

namespace Intrinsics

/-- Byte `i` of the vector (byte 0 is the least significant). Indices are reduced modulo 16;
callers pass indices below 16. -/
def byte (a : M128) (i : Nat) : UInt8 :=
  UInt8.ofNat (a[(⟨i / 4 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)].toNat / 2 ^ (8 * (i % 4)))

/-- Each lane is four little-endian bytes. Only indices 0 to 15 are read. -/
def fromBytes (bytes : Nat → UInt8) : M128 := .ofFn fun l =>
  UInt32.ofNat ((bytes (4*l.val)).toNat + 2^8 * (bytes (4*l.val+1)).toNat +
    2^16 * (bytes (4*l.val+2)).toNat + 2^24 * (bytes (4*l.val+3)).toNat)

/-- ROTR from FIPS 180-4 §3.2. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
/-- σ0 from FIPS 180-4 §4.1.2. -/
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- σ1 from FIPS 180-4 §4.1.2. -/
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
/-- Σ0 from FIPS 180-4 §4.1.2. -/
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- Σ1 from FIPS 180-4 §4.1.2. -/
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- Ch from FIPS 180-4 §4.1.2. -/
def choose (e f g : UInt32) : UInt32 := (e &&& f) ^^^ (~~~e &&& g)
/-- Maj from FIPS 180-4 §4.1.2. -/
def majority (a b c : UInt32) : UInt32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

end Intrinsics

/-- `_mm_set_epi32(e3, e2, e1, e0)` (`MOVD`/`PINSRD`…): the four integers as lanes, the last
argument in lane 0. Each `i32` contributes its 32 bits unchanged. -/
def _mm_set_epi32 (e3 e2 e1 e0 : Int32) : M128 :=
  #v[e0.toUInt32, e1.toUInt32, e2.toUInt32, e3.toUInt32]

/-- `_mm_extract_epi32::<imm>(a)` (`PEXTRD`): the lane selected by the two low bits of the
immediate, as an `i32` with the same 32 bits. -/
def _mm_extract_epi32 (imm : Nat) (a : M128) : Int32 :=
  (a[(⟨imm % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)]).toInt32

/-- `_mm_add_epi32(a, b)` (`PADDD`): lane-wise addition, modulo 2³². -/
def _mm_add_epi32 (a b : M128) : M128 := .ofFn fun l => a[l] + b[l]

/-- `_mm_shuffle_epi32::<imm>(a)` (`PSHUFD`): two bits of the immediate per output lane select
the input lane. -/
def _mm_shuffle_epi32 (imm : Nat) (a : M128) : M128 := .ofFn fun l =>
  a[(⟨(imm / 2^(2*l.val)) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)]

/-- `_mm_alignr_epi8::<imm>(a, b)` (`PALIGNR`): the low 128 bits of `(a : b) >> (8·imm)`,
filling with zeros. -/
def _mm_alignr_epi8 (imm : Nat) (a b : M128) : M128 :=
  Intrinsics.fromBytes fun i =>
    let j := i + imm
    if j < 16 then Intrinsics.byte b j
    else if j < 32 then Intrinsics.byte a (j - 16)
    else 0

/-- `_mm_sha256msg1_epu32(a, b)` (`SHA256MSG1`): the first half of computing four new
schedule words, `W[t] + σ0(W[t+1])`. -/
def _mm_sha256msg1_epu32 (a b : M128) : M128 :=
  #v[a[0] + Intrinsics.smallSigma0 a[1], a[1] + Intrinsics.smallSigma0 a[2],
    a[2] + Intrinsics.smallSigma0 a[3], a[3] + Intrinsics.smallSigma0 b[0]]

/-- `_mm_sha256msg2_epu32(a, b)` (`SHA256MSG2`): the second half, which adds `σ1`. The two
high lanes depend on the two low lanes just computed. -/
def _mm_sha256msg2_epu32 (a b : M128) : M128 :=
  let w16 := a[0] + Intrinsics.smallSigma1 b[2]
  let w17 := a[1] + Intrinsics.smallSigma1 b[3]
  #v[w16, w17, a[2] + Intrinsics.smallSigma1 w16, a[3] + Intrinsics.smallSigma1 w17]

/-- `_mm_sha256rnds2_epu32(cdgh, abef, wk)` (`SHA256RNDS2`): two SHA-256 rounds. The inputs,
from high lane to low, are CDGH and ABEF; the output is ABEF after the two rounds. Only the
two low lanes of `wk` are read: the schedule word plus the constant of each round. All
additions are modulo 2³². -/
def _mm_sha256rnds2_epu32 (cdgh abef wk : M128) : M128 :=
  let a := abef[3]; let b := abef[2]; let c := cdgh[3]; let d := cdgh[2]
  let e := abef[1]; let f := abef[0]; let g := cdgh[1]; let h := cdgh[0]
  let t1 := Intrinsics.choose e f g + Intrinsics.bigSigma1 e + wk[0] + h
  let a1 := t1 + Intrinsics.majority a b c + Intrinsics.bigSigma0 a
  let e1 := t1 + d
  let t2 := Intrinsics.choose e1 e f + Intrinsics.bigSigma1 e1 + wk[1] + g
  let a2 := t2 + Intrinsics.majority a1 a b + Intrinsics.bigSigma0 a1
  let e2 := t2 + c
  #v[e1, e2, a1, a2]

end Libssz.Merkle
