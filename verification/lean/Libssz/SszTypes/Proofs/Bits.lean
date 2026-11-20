module
public import Libssz.SszTypes.Proofs.Payload
import all Aeneas.Data.List.List
@[expose] public section

/-!
# Bitfields: `SszBitvector<N>` and `SszBitlist<N>`

Both store their bits packed eight per byte, bit `i` in bit `i % 8` of byte `i / 8` (in a
`SmallVec`, see `Libssz/SszTypes/SmallVecModel.lean`). `SszBitlist` also stores how many bits
it has.

The EthLib value of a bitfield is the list of its bits: `unpackBits bytes n`, with `n = N`
for `SszBitvector<N>` and `n = len` for `SszBitlist<N>`.

**The invariant.** The bytes are the canonical packing of their first `n` bits
(`Canon bytes n`): there are `⌈n / 8⌉` of them, and the padding bits of the last one are zero.
The `ssz-types` constructors and decoding (which rejects nonzero padding) guarantee it. The
`hash_tree_root` and encode theorems require it.
-/

open Aeneas Aeneas.Std Result
open Libssz.Proofs (byte bytes leValue)
open EthLib.Serialization.Ssz
open Libssz.Merkle

namespace Libssz.SszTypes

/-- The bytes of a bitfield are the canonical packing of its first `n` bits. -/
def Canon (B : Bytes) (n : Nat) : Prop := packBits (unpackBits B n) ((n + 7) / 8) = B

theorem Canon.size {B : Bytes} {n : Nat} (hc : Canon B n) : B.size = (n + 7) / 8 := by
  rw [← hc]; simp [packBits]

/-! ## EthLib: the root of a bitfield -/

/-- **The root of a `Bitvector[n]`** according to EthLib, with the bits of canonical bytes: the
tree of those bytes, with the capacity of `n` bits. -/
theorem hashTreeRoot_bitVector (B : Bytes) (n : Nat) (hc : Canon B n) :
    hashTreeRoot (.bitVector n) (.bits (unpackBits B n)) =
      merkleizeBoundedUnchecked (packBytes B) (some (chunksForBits n)) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.bitVector n).nesting = 1 from rfl,
    hashTreeRootAt_succ]
  have hp : packedBits (unpackBits B n) = packBytes B := by
    simp only [packedBits, unpackBits_size]; rw [hc]
  have hlay : merkleLayout (.bitVector n) (.bits (unpackBits B n)) =
      .ok (MerkleLayout.packing (packBytes B) (some (chunksForBits n)) none) := by
    simp [merkleLayout, hp, Pure.pure, Except.pure]
  simp only [hlay, Bind.bind, Except.bind]
  simp only [layoutChunksAt_eq, MerkleLayout.packing, Leaves.count, Option.getD_none,
    Array.extract_size]
  cases hm : merkleizeBoundedUnchecked (packBytes B) (some (chunksForBits n)) <;>
    simp [hm, Pure.pure, Except.pure]

/-- **The root of a `Bitlist[limit]`** according to EthLib: the tree of the bytes, with the
capacity of `limit` bits, and the number of bits mixed in on the right. -/
theorem hashTreeRoot_bitList (B : Bytes) (n limit : Nat) (hc : Canon B n) (hl : n ≤ limit) :
    hashTreeRoot (.bitList limit) (.bits (unpackBits B n)) =
      (merkleizeBoundedUnchecked (packBytes B) (some (chunksForBits limit))).map
        (fun root => mixIn root (lengthWord n)) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.bitList limit).nesting = 1 from rfl,
    hashTreeRootAt_succ]
  have hp : packedBits (unpackBits B n) = packBytes B := by
    simp only [packedBits, unpackBits_size]; rw [hc]
  have hlay : merkleLayout (.bitList limit) (.bits (unpackBits B n)) =
      .ok (MerkleLayout.packing (packBytes B) (some (chunksForBits limit))
        (some (lengthWord n))) := by
    simp [merkleLayout, hp, Nat.not_lt.mpr hl, Pure.pure, Except.pure]
  simp only [hlay, Bind.bind, Except.bind]
  simp only [layoutChunksAt_eq, MerkleLayout.packing, Leaves.count, Option.getD_none,
    Array.extract_size]
  cases hm : merkleizeBoundedUnchecked (packBytes B) (some (chunksForBits limit)) <;>
    simp [hm, Pure.pure, Except.pure, Except.map]

/-! ## `hash_tree_root` -/

section Roots

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

/-- `pack_bits` of canonical bytes, with their number of bits: `pack` of all the bytes. -/
theorem pack_bits_canon (s : Slice Std.U8) (n : Std.Usize) (hc : Canon (bytes s.val) n.val) :
    libssz_merkle.pack_bits s n ⦃ v => chunksOf v.val = packBytes (bytes s.val) ⦄ := by
  apply WP.spec_mono (pack_bits.spec s n)
  intro v hv
  rw [hv]
  have hs := hc.size
  rw [Libssz.Proofs.bytes_size] at hs
  rw [List.take_of_length_le (by omega)]

/-- The nodes of `⌈n / 8⌉` bytes do not exceed `⌈n / 256⌉`. -/
theorem chunks_bits_le (B : Bytes) (n : Nat) (hB : B.size = (n + 7) / 8) :
    (packBytes B).size ≤ (n + 255) / 256 := by
  rw [packBytes_size, hB]; simp only [bytesPerChunk]; omega

include hl in
/-- **`SszBitvector<N>`** (for example `sync_committee_bits`): the `hash_tree_root` is EthLib's
for `Bitvector[N]`, if the bytes are canonical. -/
theorem SszBitvector.hash_tree_root.spec {N : Std.Usize} (x : libssz_types.bitvector.SszBitvector N)
    (hc : Canon (bytes x.bytes.val) N.val) :
    libssz_types.bitvector.SszBitvector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root inst x h ⦃ r =>
      hashTreeRoot (.bitVector N.val) (.bits (unpackBits (bytes x.bytes.val) N.val)) =
        .ok (bytes r.val) ⦄ := by
  unfold libssz_types.bitvector.SszBitvector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.bitvector.SszBitvector.as_bytes,
    libssz_types.smallvec.SmallVec.Insts.CoreOpsDerefDerefSlice.deref,
    Libssz.SmallVecModel.deref, bind_ok, libssz_types.libssz_merkle.pack_bits,
    libssz_types.libssz_merkle.merkleize_in_place]
  have hd : (alloc.vec.Vec.deref x.bytes).val = x.bytes.val := by simp [alloc.vec.Vec.deref]
  apply WP.spec_bind (pack_bits_canon _ N (by rw [hd]; exact hc))
  intro chunks hch
  rw [hd] at hch
  step as ⟨ cap, hcap ⟩
  have hcap' : cap.val = chunksForBits N.val := by
    rw [hcap, Nat.ceilDiv_eq_add_pred_div]; simp [chunksForBits, bytesPerChunk]
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step with merkleize_in_place.spec inst h hl chunks.slice (some cap) (by
      intro c hc'; simp only [Option.some.injEq] at hc'; subst hc'
      have h1 : (chunksOf chunks.val).size = chunks.val.length := chunksOf_size _
      show chunks.val.length ≤ _
      rw [← h1, hch, hcap']
      have := chunks_bits_le _ N.val hc.size
      simp only [chunksForBits, bytesPerChunk]; omega)
    as ⟨ root, rest, hroot, _ ⟩
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs, hch] at hroot
  simp only [Option.map_some, hcap'] at hroot
  rw [hashTreeRoot_bitVector _ _ hc]
  exact hroot

include hl in
/-- **`SszBitlist<N>`** (for example `aggregation_bits`): the `hash_tree_root` is EthLib's for
`Bitlist[N]`, if the bytes are canonical and there are at most `N` bits. -/
theorem SszBitlist.hash_tree_root.spec {N : Std.Usize} (x : libssz_types.bitlist.SszBitlist N)
    (hc : Canon (bytes x.bytes.val) x.len.val) (hlen : x.len.val ≤ N.val) :
    libssz_types.bitlist.SszBitlist.Insts.Libssz_merkleHashTreeRoot.hash_tree_root inst x h ⦃ r =>
      hashTreeRoot (.bitList N.val) (.bits (unpackBits (bytes x.bytes.val) x.len.val)) =
        .ok (bytes r.val) ⦄ := by
  unfold libssz_types.bitlist.SszBitlist.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.bitlist.SszBitlist.impl.len, libssz_types.bitlist.SszBitlist.as_bytes,
    libssz_types.smallvec.SmallVec.Insts.CoreOpsDerefDerefSlice.deref,
    Libssz.SmallVecModel.deref, bind_ok, libssz_types.libssz_merkle.pack_bits,
    libssz_types.libssz_merkle.merkleize_in_place, libssz_types.libssz_merkle.mix_in_length]
  have hd : (alloc.vec.Vec.deref x.bytes).val = x.bytes.val := by simp [alloc.vec.Vec.deref]
  apply WP.spec_bind (pack_bits_canon _ x.len (by rw [hd]; exact hc))
  intro chunks hch
  rw [hd] at hch
  step as ⟨ cap, hcap ⟩
  have hcap' : cap.val = chunksForBits N.val := by
    rw [hcap, Nat.ceilDiv_eq_add_pred_div]; simp [chunksForBits, bytesPerChunk]
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step with merkleize_in_place.spec inst h hl chunks.slice (some cap) (by
      intro c hc'; simp only [Option.some.injEq] at hc'; subst hc'
      have h1 : (chunksOf chunks.val).size = chunks.val.length := chunksOf_size _
      show chunks.val.length ≤ _
      rw [← h1, hch, hcap']
      have := chunks_bits_le _ x.len.val hc.size
      simp only [chunksForBits, bytesPerChunk]; omega)
    as ⟨ root, rest, hroot, _ ⟩
  step with mix_in_length.spec inst h hl root x.len as ⟨ r, hr ⟩
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs, hch] at hroot
  simp only [Option.map_some, hcap'] at hroot
  rw [hashTreeRoot_bitList _ _ _ hc hlen, hroot]
  simp [Except.map, hr]

end Roots

/-! ## `SszBitvector`: encode and decode -/

/-- Rust's padding check (a mask of the high bits) accepts the same as EthLib's (shifting the
byte). There are seven widths and 256 bytes: the kernel checks them all. -/
theorem mask_nat : ∀ e < 8, 1 ≤ e → ∀ n < 256,
    ((n &&& (255 - (2 ^ e - 1)) ≠ 0) ↔ (n >>> e ≠ 0)) := by
  decide +kernel

/-- **Encode `SszBitvector<N>`**: appends to `buf` exactly the EthLib encoding, if the bytes
are canonical. -/
theorem SszBitvector.ssz_append.spec {N : Std.Usize} (x : libssz_types.bitvector.SszBitvector N)
    (buf : alloc.vec.Vec Std.U8) (hc : Canon (bytes x.bytes.val) N.val)
    (hsz : buf.length + x.bytes.length ≤ Usize.max) :
    libssz_types.bitvector.SszBitvector.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.bitVector N.val) (.bits (unpackBits (bytes x.bytes.val) N.val)) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold libssz_types.bitvector.SszBitvector.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [libssz_types.smallvec.SmallVec.Insts.CoreOpsDerefDerefSlice.deref,
    Libssz.SmallVecModel.deref, bind_ok]
  step with Libssz.Proofs.extend_from_slice_u8_spec buf (alloc.vec.Vec.deref x.bytes)
    (by simpa [alloc.vec.Vec.deref, alloc.vec.Vec.length] using hsz) as ⟨ buf', hbuf' ⟩
  refine ⟨bytes x.bytes.val, ?_, ?_⟩
  · simp only [serialize, unpackBits_size, beq_self_eq_true, ↓reduceIte]
    rw [hc]
  · rw [hbuf', Libssz.Proofs.bytes_append]
    simp [alloc.vec.Vec.deref]

/-- The last byte, as EthLib sees it. -/
theorem last_byte (s : Slice Std.U8) (h : 0 < s.length) :
    (bytes s.val)[(bytes s.val).size - 1]?.getD 0 = byte (s.val[s.length - 1]'(by simp at h ⊢; omega)) := by
  simp [bytes, Slice.length] at h ⊢
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- EthLib's padding, as numbers. -/
theorem shift_ne_zero (b : Std.U8) (e : Nat) (he : e < 8) :
    (byte b >>> UInt8.ofNat e ≠ 0) ↔ (b.val >>> e ≠ 0) := by
  have hb : b.val < 256 := by have := b.hBounds; scalar_tac
  constructor
  · intro h1 h2; apply h1; apply UInt8.toNat_inj.mp
    simp [UInt8.toNat_shiftRight, Nat.mod_eq_of_lt (show e < 256 by omega),
      Nat.mod_eq_of_lt he, h2]
  · intro h1 h2; apply h1
    have := congrArg UInt8.toNat h2
    simpa [UInt8.toNat_shiftRight, Nat.mod_eq_of_lt (show e < 256 by omega),
      Nat.mod_eq_of_lt he] using this

/-- `validate_excess_bits`: rejects exactly what EthLib's padding check rejects. -/
theorem validate_excess_bits.spec (N : Std.Usize) (s : Slice Std.U8)
    (hs : s.length = (N.val + 7) / 8) :
    libssz_types.bitvector.SszBitvector.validate_excess_bits N s ⦃ r =>
      (r = .Ok () ∧ ¬ (N.val % 8 ≠ 0 ∧ (bytes s.val).size > 0 ∧
          (bytes s.val)[(bytes s.val).size - 1]?.getD 0 >>> UInt8.ofNat (N.val % 8) ≠ 0)) ∨
      (r = .Err .ExcessBitsNotZero ∧ N.val % 8 ≠ 0 ∧ (bytes s.val).size > 0 ∧
          (bytes s.val)[(bytes s.val).size - 1]?.getD 0 >>> UInt8.ofNat (N.val % 8) ≠ 0) ⦄ := by
  unfold libssz_types.bitvector.SszBitvector.validate_excess_bits
  split
  · rename_i h0
    rw [WP.spec_ok]
    left; refine ⟨rfl, ?_⟩
    intro ⟨ h1, _ ⟩; apply h1; simp [h0]
  · rename_i h0
    have hN : 0 < N.val := by scalar_tac
    step as ⟨ e, he ⟩
    split
    · rename_i hne
      have hlen : 0 < s.length := by omega
      have he8 : e.val < 8 := by rw [he]; omega
      have he1 : 1 ≤ e.val := by
        have : e ≠ 0#usize := by simpa using hne
        scalar_tac
      step as ⟨ i1, hi1 ⟩
      step as ⟨ last, hlast ⟩
      step as ⟨ i2, hi2, _ ⟩
      have hpow : 2 ^ e.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hi2' : i2.val = 2 ^ e.val := by
        rw [hi2, Nat.one_shiftLeft]; apply Nat.mod_eq_of_lt; scalar_tac
      step as ⟨ i3, hi3 ⟩
      · have : 2 ^ 1 ≤ 2 ^ e.val := Nat.pow_le_pow_right (by norm_num) he1
        scalar_tac
      have hmask : (~~~i3).val = 255 - (2 ^ e.val - 1) := by
        show (~~~i3.bv).toNat = _
        rw [BitVec.toNat_not]
        have : i3.bv.toNat = i3.val := rfl
        rw [this, hi3, hi2']
      have hlv : last = s.val[s.length - 1]'(by simp at hlen ⊢; omega) := by
        rw [hlast]; simp [hi1]
      have hiff := mask_nat e.val he8 he1 last.val (by have := last.hBounds; scalar_tac)
      have hsh := shift_ne_zero last e.val he8
      have hlastE := last_byte s hlen
      rw [← hlv] at hlastE
      have hsize : (bytes s.val).size > 0 := by simp at hlen ⊢; omega
      simp only [lift, bind_ok]
      have hval : (last &&& ~~~i3).val = last.val &&& (255 - (2 ^ e.val - 1)) := by
        rw [UScalar.val_and, hmask]
      split
      · rename_i hz
        rw [WP.spec_ok]
        right
        refine ⟨rfl, by omega, hsize, ?_⟩
        rw [hlastE, ← he, hsh, ← hiff, ← hval]
        intro h
        have : last &&& ~~~i3 = 0#u8 := UScalar.eq_of_val_eq (by rw [h]; rfl)
        simp [this] at hz
      · rename_i hz
        rw [WP.spec_ok]
        left
        refine ⟨rfl, ?_⟩
        intro ⟨ _, _, h3 ⟩
        rw [hlastE, ← he, hsh, ← hiff, ← hval] at h3
        apply hz
        simp only [bne_iff_ne, ne_eq]
        intro h'
        apply h3
        rw [h']; rfl
    · rename_i he0
      rw [WP.spec_ok]
      left; refine ⟨rfl, ?_⟩
      intro ⟨ h1, _ ⟩; apply h1
      have : e.val = 0 := by simpa using he0
      rw [← he]; exact this

/-- If EthLib accepts some bytes as a `Bitvector[n]`, they are canonical. -/
theorem canon_of_bitVector {n : Nat} {data : Bytes}
    (h : deserialize (.bitVector n) data = .ok (.bits (unpackBits data n))) : Canon data n := by
  have := canonical_bitVector h
  simp only [serialize, unpackBits_size, beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at this
  exact this

/-- **Decode `SszBitvector<N>`**: the result is EthLib's for `Bitvector[N]` (both accept with
the same bits, or both reject for the same reason), and what it accepts has canonical
bytes. -/
theorem SszBitvector.from_ssz_bytes.spec {N : Std.Usize} (s : Slice Std.U8) :
    libssz_types.bitvector.SszBitvector.Insts.LibsszDecodeSszDecode.from_ssz_bytes N s ⦃ r =>
      Libssz.Proofs.Agrees
        (fun x : libssz_types.bitvector.SszBitvector N =>
          .bits (unpackBits (bytes x.bytes.val) N.val)) r
        (deserialize (.bitVector N.val) (bytes s.val)) ∧
      ∀ x, r = .Ok x → Canon (bytes x.bytes.val) N.val ⦄ := by
  unfold libssz_types.bitvector.SszBitvector.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [libssz_types.bitvector.SszBitvector.BYTE_LEN]
  step as ⟨ bl, hbl ⟩
  have hbl' : bl.val = (N.val + 7) / 8 := by rw [hbl, Nat.ceilDiv_eq_add_pred_div]; omega
  have hsz : (bytes s.val).size = s.length := by simp
  split
  · rename_i hne
    rw [WP.spec_ok]
    have hne' : s.length ≠ (N.val + 7) / 8 := by
      intro h
      simp only [bne_iff_ne, ne_eq] at hne
      exact hne (UScalar.eq_of_val_eq (by rw [hbl']; simpa using h))
    have hd : deserialize (.bitVector N.val) (bytes s.val) =
        .error (.scope ((N.val + 7) / 8) s.length) := by
      simp [deserialize, hsz, hne', Bind.bind, Except.bind, throw_error]
    refine ⟨?_, fun x hx => by cases hx⟩
    rw [hd, Libssz.Proofs.Agrees]
    have := Libssz.Proofs.ErrMatch.fixedLength bl (Slice.len s)
    rw [hbl'] at this
    simpa using this
  · rename_i heq
    have heq' : s.length = (N.val + 7) / 8 := by
      rw [← hbl']; simpa using heq
    step with validate_excess_bits.spec N s heq' as ⟨ r, hr ⟩
    rcases hr with ⟨ rfl, hok ⟩ | ⟨ rfl, h1, h2, h3 ⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        libssz_types.smallvec.SmallVec.from_slice, Libssz.SmallVecModel.from_slice]
      rw [WP.spec_ok]
      have hd : deserialize (.bitVector N.val) (bytes s.val) =
          .ok (.bits (unpackBits (bytes s.val) N.val)) := by
        have hsz' : (bytes s.val).size = (N.val + 7) / 8 := by rw [hsz, heq']
        simp only [deserialize, hsz', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        simp only [Bind.bind, Except.bind]
        split
        · rename_i hc
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
          split
          · rename_i hc2
            exfalso; apply hok
            refine ⟨hc.1, by rw [hsz']; omega, ?_⟩
            simpa [hsz'] using hc2
          · rfl
        · rfl
      refine ⟨?_, ?_⟩
      · rw [hd, Libssz.Proofs.Agrees]; rfl
      · intro x hx
        simp only [core.result.Result.Ok.injEq] at hx
        subst hx
        exact canon_of_bitVector hd
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      rw [WP.spec_ok]
      have hsz' : (bytes s.val).size = (N.val + 7) / 8 := by rw [hsz, heq']
      have hd : deserialize (.bitVector N.val) (bytes s.val) = .error .paddingBits := by
        simp only [deserialize, hsz', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hc : (N.val % 8 != 0 && decide ((N.val + 7) / 8 > 0)) = true := by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact ⟨h1, by rw [← hsz']; exact h2⟩
        have hc2 : ((bytes s.val)[(N.val + 7) / 8 - 1]?.getD 0 >>> UInt8.ofNat (N.val % 8) != 0)
            = true := by
          simpa [hsz'] using h3
        simp only [Bind.bind, Except.bind]
        simp only [hc, hc2, ↓reduceIte]
        rfl
      refine ⟨?_, fun x hx => by cases hx⟩
      rw [hd, Libssz.Proofs.Agrees]
      exact Libssz.Proofs.ErrMatch.paddingBits

/-! ## Bits of a byte -/

/-- Bit `o` of a byte, as EthLib reads it, is the `testBit` of its number. Checked over all
256 bytes and 8 bits. -/
theorem bit_testBit (b : UInt8) (o : Nat) (h : o < 8) :
    ((b >>> UInt8.ofNat o) &&& 1 == 1) = b.toNat.testBit o := by
  have key : ∀ f : Fin 256, ∀ o, o < 8 →
      ((UInt8.ofBitVec (BitVec.ofFin f) >>> UInt8.ofNat o) &&& 1 == 1) =
        (UInt8.ofBitVec (BitVec.ofFin f)).toNat.testBit o := by decide +kernel
  cases b with
  | ofBitVec bv => cases bv with
    | ofFin f => exact key f o h

/-- A byte is less than 256: its bits from 8 on are zero. -/
theorem testBit_byte_high (b : UInt8) (o : Nat) (h : 8 ≤ o) : b.toNat.testBit o = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by norm_num) h))

/-- Two bytes with the same eight bits are equal. -/
theorem byte_eq_of_testBit {a b : UInt8} (h : ∀ o, o < 8 → a.toNat.testBit o = b.toNat.testBit o) :
    a = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro o
  by_cases ho : o < 8
  · exact h o ho
  · rw [testBit_byte_high a o (by omega), testBit_byte_high b o (by omega)]

/-- A bit of `unpackBits`: bit `p % 8` of byte `p / 8`. -/
theorem unpackBits_get (B : Bytes) (n p : Nat) (hp : p < n) :
    (unpackBits B n)[p]'(by simpa using hp) = (B[p / 8]?.getD 0).toNat.testBit (p % 8) := by
  simp only [unpackBits, Array.getElem_map, Array.getElem_range]
  exact bit_testBit _ _ (Nat.mod_lt _ (by norm_num))

/-- A bit of a byte of `packBits`: the list's bit at that position (or `false`). -/
theorem packBits_testBit (bits : Array Bool) (k i o : Nat) (hi : i < k) (ho : o < 8) :
    ((packBits bits k)[i]'(by simpa [packBits] using hi)).toNat.testBit o =
      bits[i * 8 + o]?.getD false := by
  rw [← bit_testBit _ _ ho]
  simp only [packBits, Array.getElem_ofFn]
  exact packByte_bit bits i o ho

/-- In canonical bytes, the bits from `n` on are zero. -/
theorem Canon.high {B : Bytes} {n : Nat} (hc : Canon B n) (i o : Nat) (hi : i < B.size) (ho : o < 8)
    (hp : n ≤ i * 8 + o) : (B[i]'hi).toNat.testBit o = false := by
  have hs := hc.size
  have e := congrArg (fun C : Bytes => (C[i]?.getD 0).toNat.testBit o) hc
  have hk : i < (packBits (unpackBits B n) ((n + 7) / 8)).size := by simp [packBits]; omega
  simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hk, Option.getD_some] at e
  rw [← e, packBits_testBit _ _ _ _ (by omega) ho, Array.getElem?_eq_none (by simp; omega)]
  rfl

/-- **The encoding of a bitlist, in bytes.** If the bits of `D` are those of the canonical bytes
`B` of `L` bits, plus bit `L` set, `D` is EthLib's `packBitsDelimited`. -/
theorem packBitsDelimited_eq (B : Bytes) (L : Nat) (hc : Canon B L) (D : Bytes)
    (hD : D.size = (L + 8) / 8)
    (hbyte : ∀ i (hi : i < D.size) o, o < 8 →
      (D[i]'hi).toNat.testBit o = ((B[i]?.getD 0).toNat.testBit o || (i * 8 + o == L))) :
    packBitsDelimited (unpackBits B L) = D := by
  have hs := hc.size
  apply Array.ext
  · simp [packBitsDelimited, packBits, hD]
  · intro i h1 h2
    apply byte_eq_of_testBit
    intro o ho
    simp only [packBitsDelimited, unpackBits_size] at h1 ⊢
    rw [packBits_testBit _ _ _ _ (by simpa [packBits] using h1) ho, hbyte i h2 o ho]
    rcases Nat.lt_trichotomy (i * 8 + o) L with hlt | heq | hgt
    · rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt (by simpa using hlt),
        unpackBits_get _ _ _ hlt]
      have e1 : (i * 8 + o) / 8 = i := by omega
      have e2 : (i * 8 + o) % 8 = o := by omega
      rw [e1, e2]
      simp [show (i * 8 + o == L) = false by simpa using Nat.ne_of_lt hlt]
    · rw [Array.getElem?_eq_getElem (by simp; omega)]
      simp [heq, Array.getElem_push]
    · rw [Array.getElem?_eq_none (by simp; omega)]
      simp only [Option.getD_none, show (i * 8 + o == L) = false by simpa using Nat.ne_of_gt hgt,
        Bool.or_false]
      by_cases hi : i < B.size
      · rw [Array.getElem?_eq_getElem hi, Option.getD_some, hc.high i o hi ho (by omega)]
      · rw [Array.getElem?_eq_none (by omega)]; simp

theorem one_shl_u8 (k : Nat) (hk : k < 8) : 1 <<< k % U8.size = 2 ^ k := by
  rw [Nat.one_shiftLeft]; apply Nat.mod_eq_of_lt
  have : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  scalar_tac

theorem getElem_eq_of {α : Type} {l l' : List α} (h : l = l') (i j : Nat) (hij : i = j)
    (hi : i < l.length) : l[i] = l'[j]'(by subst h hij; exact hi) := by
  subst h hij; rfl

theorem bytes_getElem (l : List Std.U8) (j : Nat) (h : j < (bytes l).size) :
    (bytes l)[j]'h = byte (l[j]'(by simpa using h)) := by
  simp [bytes]

/-- The Rust bytes, padded with zeros, as EthLib bytes read with `getD 0`. -/
theorem pad_get (Bl : List Std.U8) (k j : Nat) (hj : j < Bl.length + k) :
    ((Bl ++ List.replicate k 0#u8)[j]'(by simpa using hj)).val =
      ((bytes Bl)[j]?.getD 0).toNat := by
  by_cases h : j < Bl.length
  · rw [List.getElem_append_left h, Array.getElem?_eq_getElem (by simpa using h)]
    simp [bytes]
  · rw [List.getElem_append_right (by omega)]
    rw [Array.getElem?_eq_none (by simp; omega)]
    simp

/-- **Encode `SszBitlist<N>`**: appends to `buf` exactly the EthLib encoding (the bits and the
delimiter), if the bytes are canonical and there are at most `N` bits. -/
theorem SszBitlist.ssz_append.spec {N : Std.Usize} (x : libssz_types.bitlist.SszBitlist N)
    (buf : alloc.vec.Vec Std.U8) (hc : Canon (bytes x.bytes.val) x.len.val)
    (hlen : x.len.val ≤ N.val) (hsz : buf.length + x.len.val + 1 ≤ Usize.max) :
    libssz_types.bitlist.SszBitlist.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.bitList N.val) (.bits (unpackBits (bytes x.bytes.val) x.len.val)) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  have hser : serialize (.bitList N.val) (.bits (unpackBits (bytes x.bytes.val) x.len.val)) =
      .ok (packBitsDelimited (unpackBits (bytes x.bytes.val) x.len.val)) := by
    simp [serialize, hlen]
  have hs := hc.size
  rw [Libssz.Proofs.bytes_size] at hs
  unfold libssz_types.bitlist.SszBitlist.Insts.LibsszEncodeSszEncode.ssz_append
  split
  · rename_i h0
    step with alloc.vec.Vec.push_spec buf 1#u8 (by simp [alloc.vec.Vec.length] at hsz; omega)
      as ⟨ buf', hbuf' ⟩
    refine ⟨_, hser, ?_⟩
    have h0' : x.len.val = 0 := by simp [h0]
    rw [hbuf', Libssz.Proofs.bytes_append, h0']
    have he : unpackBits (bytes x.bytes.val) 0 = #[] := by simp [unpackBits]
    rw [he]
    congr 1
  · rename_i h0
    have hL : 0 < x.len.val := by
      have : x.len ≠ 0#usize := h0
      scalar_tac
    simp only [libssz_types.bitlist.SszBitlist.Insts.LibsszEncodeSszEncode.encoded_len,
      libssz_types.smallvec.SmallVec.Insts.CoreOpsDerefDerefSlice.deref,
      Libssz.SmallVecModel.deref, bind_ok]
    step as ⟨ l1, hl1 ⟩
    step as ⟨ E, hE ⟩
    have hE' : E.val = (x.len.val + 8) / 8 := by
      rw [hE, Nat.ceilDiv_eq_add_pred_div, hl1]; omega
    step with Libssz.Proofs.extend_from_slice_u8_spec buf (alloc.vec.Vec.deref x.bytes)
      (by simp [alloc.vec.Vec.deref, alloc.vec.Vec.length] at hsz ⊢; omega) as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i, hi ⟩
    step with alloc.vec.Vec.resize_spec core.clone.CloneU8 buf1 i 0#u8 rfl as ⟨ buf2, hbuf2 ⟩
    step as ⟨ dbi, hdbi ⟩
    step as ⟨ dbit, hdbit ⟩
    step as ⟨ i1, hi1bv, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    -- What remains in `buf2`: `buf`, the bytes, and zeros up to `E` bytes.
    set Bl := x.bytes.val with hBl
    have hEB : Bl.length ≤ E.val := by rw [hs, hE']; omega
    set Y := Bl ++ List.replicate (E.val - Bl.length) 0#u8 with hY
    have hYl : Y.length = E.val := by simp [hY]; omega
    have hbl : buf.val.length = buf.len.val := by simp [alloc.vec.Vec.len]
    have hbuf2' : buf2.val = buf.val ++ Y := by
      rw [hbuf2, hbuf1, hi]
      unfold List.resize
      simp only [alloc.vec.Vec.deref, Slice.from_val, ge_iff_le, Nat.zero_le, ↓reduceIte, ← hBl]
      have hl : (buf.val ++ Bl).length ≤ buf.len.val + E.val := by
        simp [alloc.vec.Vec.len]; omega
      rw [List.take_of_length_le hl, List.append_assoc, hY]
      congr 2
      simp [alloc.vec.Vec.len]; omega
    have hdl : x.len.val / 8 < E.val := by rw [hE']; omega
    have hi2l : i2.val < buf2.length := by
      rw [show buf2.length = buf2.val.length from rfl, hbuf2', List.length_append, hYl, hi2, hdbi,
        hbl]
      omega
    step with alloc.vec.Vec.index_mut_usize_spec buf2 i2 hi2l as ⟨ i3, back, hi3, hback ⟩
    simp only [lift, bind_ok, WP.spec_ok]
    refine ⟨_, hser, ?_⟩
    have hi3' : i3 = Y[x.len.val / 8]'(by omega) := by
      rw [hi3, getElem_eq_of hbuf2' _ (buf.val.length + x.len.val / 8) (by rw [hi2, hdbi, hbl])
        (by omega), List.getElem_append_right (by omega)]
      simp
    have hk : dbit.val < 8 := by rw [hdbit]; omega
    have hi1' : i1.val = 2 ^ (x.len.val % 8) := by
      rw [hi1bv, hdbit]; exact one_shl_u8 _ (by omega)
    rw [hback]
    have hset : (buf2.set i2 (i3 ||| i1)).val = buf.val ++ Y.set (x.len.val / 8) (i3 ||| i1) := by
      rw [alloc.vec.Vec.set_val_eq, hbuf2', hi2, hdbi, List.set_append_right _ _ (by omega)]
      congr 2; omega
    rw [hset, Libssz.Proofs.bytes_append]
    congr 1
    symm
    apply packBitsDelimited_eq _ _ hc
    · simp [hYl, hE']
    · intro j hj o ho
      have hjE : j < E.val := by simpa [hYl] using hj
      rw [bytes_getElem, Libssz.Proofs.byte_toNat]
      by_cases hjd : j = x.len.val / 8
      · subst hjd
        rw [List.getElem_set_self, UScalar.val_or, Nat.testBit_lor, hi1', Nat.testBit_two_pow,
          hi3', pad_get Bl _ _ (by omega)]
        congr 1
        rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
        omega
      · rw [List.getElem_set_ne (Ne.symm hjd), pad_get Bl _ _ (by omega)]
        have : (j * 8 + o == x.len.val) = false := by simp; omega
        rw [this, Bool.or_false]

/-! ## `SszBitlist`: decode -/

/-- The highest set bit of a nonzero number is `Nat.log 2`. -/
theorem testBit_log (n : Nat) (h : n ≠ 0) : n.testBit (Nat.log 2 n) = true := by
  have h1 := Nat.pow_log_le_self 2 h
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  generalize Nat.log 2 n = k at h1 h2 ⊢
  obtain ⟨ r, hr ⟩ : ∃ r, n = 2 ^ k + r := ⟨n - 2 ^ k, by omega⟩
  have hr2 : r < 2 ^ k := by rw [Nat.pow_succ] at h2; omega
  rw [hr, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr2]; rfl

theorem testBit_above_log (n : Nat) (o : Nat) (ho : Nat.log 2 n < o) : n.testBit o = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)
    (Nat.pow_le_pow_right (by norm_num) ho)

theorem log_lt_8 (n : Nat) (h : n < 256) : Nat.log 2 n < 8 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr (by simpa using h)

/-- EthLib's `highestBit` is `Nat.log 2`. -/
theorem highestBit_log (b : UInt8) (h : b ≠ 0) : highestBit b = Nat.log 2 b.toNat := by
  have hb : b.toNat ≠ 0 := by intro e; apply h; exact UInt8.toNat_inj.mp (by simpa using e)
  have hl := log_lt_8 b.toNat b.toNat_lt
  apply highestBit_eq b _ hl
  · have := bit_testBit b _ hl
    rw [testBit_log _ hb] at this
    simpa using this
  · intro j hj hj8 heq
    have := bit_testBit b _ hj8
    rw [testBit_above_log _ _ hj] at this
    simp [heq] at this

/-- Rust's mask over the bits above the delimiter never rejects. -/
theorem mask_above_zero : ∀ k < 8, ∀ n < 256, n < 2 ^ (k + 1) →
    n &&& (255 - (2 ^ (k + 1) - 1)) = 0 := by
  decide +kernel

/-- Clearing a bit (`&= !(1 << k)`). -/
theorem clear_bit_testBit : ∀ k < 8, ∀ o < 8, (255 - 2 ^ k).testBit o = (o != k) := by
  decide +kernel

/-- If two bytes have the same bits in the first `n` positions, `unpackBits` of `n` gives the
same result. -/
theorem unpackBits_congr (B C : Bytes) (n : Nat)
    (h : ∀ p, p < n → (B[p / 8]?.getD 0).toNat.testBit (p % 8) =
      (C[p / 8]?.getD 0).toNat.testBit (p % 8)) :
    unpackBits B n = unpackBits C n := by
  apply Array.ext
  · simp
  · intro p h1 h2
    have hp : p < n := by simpa using h1
    rw [unpackBits_get _ _ _ hp, unpackBits_get _ _ _ hp]
    exact h p hp

theorem bytes_getD (l : List Std.U8) (j : Nat) :
    ((bytes l)[j]?.getD 0).toNat = (l[j]?.getD 0#u8).val := by
  by_cases h : j < l.length
  · simp [bytes, h]
  · simp [bytes, h]

/-- `deserialize` of a bitlist, in two parts. -/
theorem deserialize_bitList (N : Nat) (D : Bytes) :
    deserialize (.bitList N) D =
      match unpackDelimited (some N) D with
      | .ok bits => .ok (.bits bits)
      | .error e => .error e := by
  simp only [deserialize, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases unpackDelimited (some N) D <;> rfl

/-- **Decode `SszBitlist<N>`**: the result is EthLib's for `Bitlist[N]`, and what it accepts has
canonical bytes and at most `N` bits. It requires that `8 · length` fits in a `usize` (the Rust
code computes the number of bits). -/
theorem SszBitlist.from_ssz_bytes.spec {N : Std.Usize} (s : Slice Std.U8)
    (hs8 : 8 * s.length ≤ Usize.max) :
    libssz_types.bitlist.SszBitlist.Insts.LibsszDecodeSszDecode.from_ssz_bytes N s ⦃ r =>
      Libssz.Proofs.Agrees
        (fun x : libssz_types.bitlist.SszBitlist N =>
          .bits (unpackBits (bytes x.bytes.val) x.len.val)) r
        (deserialize (.bitList N.val) (bytes s.val)) ∧
      ∀ x, r = .Ok x → Canon (bytes x.bytes.val) x.len.val ∧ x.len.val ≤ N.val ⦄ := by
  unfold libssz_types.bitlist.SszBitlist.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  have hsz : (bytes s.val).size = s.length := by simp
  rw [deserialize_bitList]
  step as ⟨ b, hb ⟩
  split
  · rename_i hbt
    have h0 : s.length = 0 := by rw [← hb]; exact hbt
    rw [WP.spec_ok]
    have hu : unpackDelimited (some N.val) (bytes s.val) = .error .emptyEncoding := by
      simp [unpackDelimited, hsz, h0, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    rw [hu]
    exact ⟨Libssz.Proofs.ErrMatch.noDelimiter _ (Or.inl rfl), fun x hx => by cases hx⟩
  · rename_i hbf
    have hlen : 0 < s.length := by
      have : ¬ s.length = 0 := by rw [← hb]; exact hbf
      omega
    step as ⟨ i1, hi1 ⟩
    step as ⟨ last, hlast ⟩
    have hlastv : last = s.val[s.length - 1]'(by simp at hlen ⊢; omega) := by
      rw [hlast]; simp [hi1]
    have hfinal := last_byte s hlen
    rw [← hlastv] at hfinal
    have hsz0 : (bytes s.val).size ≠ 0 := by omega
    have hne : s.val ≠ [] := by intro e; simp [e] at hlen
    have hfin : (bytes s.val)[s.val.length - 1]?.getD 0 = byte last := by
      rw [← hfinal, hsz]
    split
    · rename_i hz
      rw [WP.spec_ok]
      have hz' : byte last = 0 := by rw [hz]; rfl
      refine ⟨?_, fun x hx => by cases hx⟩
      cases hall : Array.all (bytes s.val) (fun a => a == 0) 0 s.val.length
      · have hu : unpackDelimited (some N.val) (bytes s.val) = .error .trailingZeros := by
          simp [unpackDelimited, hne, hfin, hz', hall, throw, throwThe, MonadExceptOf.throw,
            Bind.bind, Except.bind]
        rw [hu]
        exact Libssz.Proofs.ErrMatch.noDelimiter _ (Or.inr (Or.inr rfl))
      · have hu : unpackDelimited (some N.val) (bytes s.val) = .error .noDelimiter := by
          simp [unpackDelimited, hne, hfin, hz', hall, throw, throwThe, MonadExceptOf.throw,
            Bind.bind, Except.bind]
        rw [hu]
        exact Libssz.Proofs.ErrMatch.noDelimiter _ (Or.inr (Or.inl rfl))
    · rename_i hnz
      have hlnz : last.val ≠ 0 := by
        intro e; apply hnz; exact UScalar.eq_of_val_eq (by rw [e]; rfl)
      have hl256 : last.val < 256 := by have := last.hBounds; scalar_tac
      have hk8 : Nat.log 2 last.val < 8 := log_lt_8 _ hl256
      have hlz : (core.num.U8.leading_zeros last).val = 7 - Nat.log 2 last.val := by
        have hbv : last.bv ≠ 0 := by
          intro e; apply hlnz; show last.bv.toNat = 0; rw [e]; rfl
        simp only [core.num.U8.leading_zeros, Aeneas.Std.BitVec.leadingZeros, hbv, ↓reduceIte]
        show (BitVec.ofNat 32 (8 - Nat.log 2 last.bv.toNat - 1)).toNat = _
        rw [BitVec.toNat_ofNat, show last.bv.toNat = last.val from rfl]
        omega
      simp only [lift, bind_ok]
      have hcast : (UScalar.cast UScalarTy.Usize (core.num.U8.leading_zeros last)).val =
          7 - Nat.log 2 last.val := by
        rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by
          rw [hlz]
          have : (32 : Nat) ≤ UScalarTy.Usize.numBits := by
            simp [UScalarTy.numBits]
          have h2 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num) this
          omega), hlz]
      step as ⟨ hb, hhb ⟩
      have hhb' : hb.val = Nat.log 2 last.val := by rw [hhb, hcast]; omega
      step as ⟨ i5, hi5 ⟩
      step as ⟨ i6, hi6 ⟩
      step as ⟨ bit_len, hbl ⟩
      have hbl' : bit_len.val = 8 * (s.length - 1) + Nat.log 2 last.val := by
        rw [hbl, hi6, hi5, hhb']; simp; ring
      have hhB : highestBit (byte last) = Nat.log 2 last.val := by
        rw [highestBit_log _ (by intro e; apply hlnz; simpa using congrArg UInt8.toNat e),
          Libssz.Proofs.byte_toNat]
      have hbz : (byte last == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e; apply hlnz; simpa using congrArg UInt8.toNat e
      have hbl'' : bit_len.val = 8 * (s.val.length - 1) + Nat.log 2 last.val := by
        rw [hbl']
      split
      · rename_i hgt
        rw [WP.spec_ok]
        have hgt' : N.val < bit_len.val := by simpa using hgt
        have hu : unpackDelimited (some N.val) (bytes s.val) =
            .error (.overLimit N.val bit_len.val) := by
          simp [unpackDelimited, hne, hfin, hbz, hhB, ← hbl'', hgt', throw, throwThe,
            MonadExceptOf.throw, Bind.bind, Except.bind]
        rw [hu]
        exact ⟨Libssz.Proofs.ErrMatch.overLimit N bit_len, fun x hx => by cases hx⟩
      · rename_i hle
        have hle' : bit_len.val ≤ N.val := by simpa using hle
        have hu : unpackDelimited (some N.val) (bytes s.val) =
            .ok (unpackBits (bytes s.val) bit_len.val) := by
          simp [unpackDelimited, hne, hfin, hbz, hhB, ← hbl'', Nat.not_lt.mpr hle', Pure.pure,
            Except.pure]
        rw [hu]
        split
        on_goal 1 =>
          rename_i hk7
          have hk7' : Nat.log 2 last.val < 7 := by rw [← hhb']; scalar_tac
          step as ⟨ i7, hi7 ⟩
          step as ⟨ i8, hi8bv, hi8 ⟩
          have hi8' : i8.val = 2 ^ (Nat.log 2 last.val + 1) := by
            rw [hi8bv, hi7, hhb']; exact one_shl_u8 _ (by omega)
          step as ⟨ i9, hi9 ⟩
          · rw [hi8']; have := Nat.one_le_two_pow (n := Nat.log 2 last.val + 1); scalar_tac
          have hm : (last &&& ~~~i9) = 0#u8 := by
            apply UScalar.eq_of_val_eq
            rw [UScalar.val_and]
            show last.val &&& (~~~i9.bv).toNat = 0
            rw [BitVec.toNat_not, show i9.bv.toNat = i9.val from rfl, hi9, hi8']
            exact mask_above_zero _ (by omega) _ hl256
              (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _)
          simp only [hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        all_goals
          simp only [libssz_types.smallvec.SmallVec.from_slice,
            Libssz.SmallVecModel.from_slice,
            libssz_types.smallvec.SmallVec.Insts.CoreOpsIndexIndexMut.index_mut,
            alloc.vec.Vec.index_mut_slice_index, libssz_types.smallvec.SmallVec.truncate,
            Libssz.SmallVecModel.truncate, bind_ok]
          step as ⟨ i11, hi11a, hi11b ⟩
          step as ⟨ i14, hi14 ⟩
          have hi14v : i14.val = s.val.length - 1 := by rw [hi14]; simp
          have hi14l : i14.val < ({ slice := s } : alloc.vec.Vec Std.U8).length := by
            simp [alloc.vec.Vec.length, alloc.vec.Vec.val, hi14v]; simp at hlen; omega
          step with alloc.vec.Vec.index_mut_usize_spec _ i14 hi14l as ⟨ i15, back, hi15, hback ⟩
          step as ⟨ needed, hneeded ⟩
          have hk := hk8
          have hlen' : 0 < s.val.length := by simpa using hlen
          have hi11' : i11.val = 2 ^ Nat.log 2 last.val := by
            rw [hi11a, hhb']; exact one_shl_u8 _ hk8
          have hi15' : i15 = last := by
            rw [hi15, hlastv]; simp [alloc.vec.Vec.val, hi14v, Slice.length]
          have hcv : (i15 &&& ~~~i11).val = last.val &&& (255 - 2 ^ Nat.log 2 last.val) := by
            rw [UScalar.val_and, hi15']
            show last.val &&& (~~~i11.bv).toNat = _
            rw [BitVec.toNat_not, show i11.bv.toNat = i11.val from rfl, hi11']
          have hneeded' : needed.val = (bit_len.val + 7) / 8 := by
            rw [hneeded, Nat.ceilDiv_eq_add_pred_div]; omega
          have hback' : (back (i15 &&& ~~~i11)).val = s.val.set (s.val.length - 1) (i15 &&& ~~~i11) := by
            rw [hback, alloc.vec.Vec.set_val_eq, hi14v]; rfl
          obtain ⟨ R, hR0 ⟩ : ∃ R, R = (back (i15 &&& ~~~i11)).val.take needed.val := ⟨_, rfl⟩
          set c := i15 &&& ~~~i11 with hc
          have hR : R = (s.val.set (s.val.length - 1) c).take needed.val := by rw [hR0, hback']
          have hcb : ∀ o, o < 8 → c.val.testBit o = (last.val.testBit o && (o != Nat.log 2 last.val)) := by
            intro o ho
            rw [hcv, Nat.testBit_land, clear_bit_testBit _ hk8 _ ho]
          -- Each byte of `R`, as EthLib reads it.
          have hRget : ∀ j, j < needed.val → j < s.val.length →
              ((bytes R)[j]?.getD 0).toNat = (if j = s.val.length - 1 then c else s.val[j]?.getD 0#u8).val := by
            intro j hj1 hj2
            rw [bytes_getD, hR, List.getElem?_take_of_lt hj1, List.getElem?_set]
            split
            · rename_i he; subst he; simp [hj2]
            · rename_i he; simp [Ne.symm he]
          refine ⟨?_, ?_⟩
          · show Value.bits _ = Value.bits _
            dsimp only
            simp only [alloc.vec.Vec.from_val]
            rw [← hR0]
            congr 1
            apply unpackBits_congr
            intro p hp
            have hj1 : p / 8 < needed.val := by rw [hneeded']; omega
            have hj2 : p / 8 < s.val.length := by
              rw [hbl''] at hp
              have := hk8
              have : 0 < s.val.length := by simpa using hlen
              omega
            rw [hRget _ hj1 hj2, bytes_getD]
            split
            · rename_i he
              have hpo : p % 8 < Nat.log 2 last.val := by rw [hbl''] at hp; omega
              rw [hcb _ (Nat.mod_lt _ (by norm_num)), List.getElem?_eq_getElem hj2, Option.getD_some,
                show s.val[p / 8] = last by rw [hlastv]; simp [he, Slice.length]]
              simp [show p % 8 ≠ Nat.log 2 last.val by omega]
            · rfl
          · intro x hx
            simp only [core.result.Result.Ok.injEq] at hx
            subst hx
            refine ⟨?_, hle'⟩
            dsimp only
            simp only [alloc.vec.Vec.from_val]
            rw [← hR0]
            have hRs : (bytes R).size = (bit_len.val + 7) / 8 := by
              simp [hR, hneeded']; rw [hbl'']; omega
            unfold Canon
            rw [← hRs]
            apply packBits_unpackBits
            intro idx hidx o ho habove
            rw [bit_testBit _ _ ho]
            have hidx' : idx < needed.val := by rw [hRs, ← hneeded'] at hidx; exact hidx
            have hidl : idx = s.val.length - 1 := by rw [hbl''] at habove; omega
            have hidx2 : idx < s.val.length := by omega
            have := hRget idx hidx' hidx2
            have hif : (if idx = s.val.length - 1 then c else s.val[idx]?.getD 0#u8) = c := by
              split
              · rfl
              · contradiction
            rw [hif] at this
            rw [this, hcb o ho]
            have hol : Nat.log 2 last.val ≤ o := by rw [hbl''] at habove; omega
            rcases Nat.eq_or_lt_of_le hol with he | hlt
            · simp [← he]
            · rw [testBit_above_log _ _ hlt]; rfl

/-! ## Containers with bitfields -/

/-- A bitlist as an EthLib value. -/
def blV {N : Std.Usize} (x : libssz_types.bitlist.SszBitlist N) : Value :=
  .bits (unpackBits (bytes x.bytes.val) x.len.val)

/-- A bitvector as an EthLib value. -/
def bvV {N : Std.Usize} (x : libssz_types.bitvector.SszBitvector N) : Value :=
  .bits (unpackBits (bytes x.bytes.val) N.val)

def attNames : List String := ["aggregation_bits", "data", "signature"]
def attFields : List Desc := [.bitList 2048, .container Proofs.adNames Proofs.adFields, .byteVector 96]
def attV (x : libssz_types.verif_example.Attestation) : Value :=
  .seq [blV x.aggregation_bits, adV x.data, .bytes (bytes x.signature.val)]

def paNames : List String := ["aggregation_bits", "data", "inclusion_delay", "proposer_index"]
def paFields : List Desc :=
  [.bitList 2048, .container Proofs.adNames Proofs.adFields, Desc.uint64, Desc.uint64]
def paV (x : libssz_types.verif_example.PendingAttestation) : Value :=
  .seq [blV x.aggregation_bits, adV x.data, .uint x.inclusion_delay.val, .uint x.proposer_index.val]

def saNames : List String := ["sync_committee_bits", "sync_committee_signature"]
def saFields : List Desc := [.bitVector 512, .byteVector 96]
def saV (x : libssz_types.verif_example.SyncAggregate) : Value :=
  .seq [bvV x.sync_committee_bits, .bytes (bytes x.sync_committee_signature.val)]

/-- The invariant of a bitlist: canonical bytes and at most `N` bits. -/
def BlInv {N : Std.Usize} (x : libssz_types.bitlist.SszBitlist N) : Prop :=
  Canon (bytes x.bytes.val) x.len.val ∧ x.len.val ≤ N.val

section Containers

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **`Attestation`** (phase0): the `hash_tree_root` that the macro generates is EthLib's. -/
theorem Attestation.hash_tree_root.spec (x : libssz_types.verif_example.Attestation)
    (hb : BlInv x.aggregation_bits) :
    libssz_types.verif_example.Attestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container attNames attFields) (attV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.Attestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.verif_example.AttestationData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with SszBitlist.hash_tree_root.spec inst h hl x.aggregation_bits hb.1 hb.2 as ⟨ a0, h0 ⟩
  step with AttestationData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.signature as ⟨ a2, h2 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold attV blV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val] rfl
    (by simp only [attFields] at *; simp [h0, h1, h2, Pure.pure, Except.pure, Bind.bind,
      Except.bind])]
  have hc : chunksOf (Array.make 3#usize [a0, a1, a2] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show attFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val]).size from rfl,
    merkleizeBounded_some_self, ← hr]

include hl in
/-- **The rows of `Attestation`** (requires `BlInv` of its bits): the roots of its 3 fields,
plus 1 zero root, the bottom level of its tree. -/
theorem Attestation.rows :
    Rows inst h libssz_types.verif_example.Attestation.Insts.Libssz_merkleHashTreeRoot (.container attNames attFields) attV
      (fun x => BlInv x.aggregation_bits) 2 where
  small := by omega
  width := ⟨ 4#usize, rfl, rfl ⟩
  row x row hgood hlen := by
    simp only [libssz_types.verif_example.Attestation.Insts.Libssz_merkleHashTreeRoot]
    unfold libssz_types.verif_example.Attestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root_row
    simp only [libssz_types.libssz_merkle.verif_example.AttestationData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
      libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root]
    have hb : BlInv x.aggregation_bits := hgood
    have hlen' : row.val.length = 4 := hlen
    obtain ⟨ b0, b1, b2, b3, hrowv ⟩ := list_len4 row.val hlen'
    step with SszBitlist.hash_tree_root.spec inst h hl x.aggregation_bits hb.1 hb.2 as ⟨ a0, h0 ⟩
    step as ⟨ row1, hrow1 ⟩
    have hl1 : row1.length = 4 := by
      rw [hrow1]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    step with AttestationData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
    step as ⟨ row2, hrow2 ⟩
    have hl2 : row2.length = 4 := by
      rw [hrow2]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    step with ArrayU8N.hash_tree_root.spec inst h hl x.signature as ⟨ a2, h2 ⟩
    step as ⟨ row3, hrow3 ⟩
    have hl3 : row3.length = 4 := by
      rw [hrow3]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl2
    step as ⟨ row4, hrow4 ⟩
    have hl4 : row4.length = 4 := by
      rw [hrow4]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl3
    have hrv : row4.val = [a0, a1, a2, zeroNode] := by
      rw [hrow4, hrow3, hrow2, hrow1]
      simp only [Slice.set_val_eq, hrowv]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    unfold RowRoot attV blV
    rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val] rfl
      (by simp only [attFields] at *; simp [h0, h1, h2, Pure.pure, Except.pure, Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [a0, a1, a2] 2 (by simp [depthFor])

include hl in
/-- **`PendingAttestation`** (phase0): the `hash_tree_root` that the macro generates is
EthLib's. -/
theorem PendingAttestation.hash_tree_root.spec (x : libssz_types.verif_example.PendingAttestation)
    (hb : BlInv x.aggregation_bits) :
    libssz_types.verif_example.PendingAttestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container paNames paFields) (paV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.PendingAttestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.verif_example.AttestationData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with SszBitlist.hash_tree_root.spec inst h hl x.aggregation_bits hb.1 hb.2 as ⟨ a0, h0 ⟩
  step with AttestationData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
  step with U64.hash_tree_root.spec inst h x.inclusion_delay as ⟨ a2, h2 ⟩
  step with U64.hash_tree_root.spec inst h x.proposer_index as ⟨ a3, h3 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold paV blV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
    (by simp only [paFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind,
      Except.bind])]
  have hc : chunksOf (Array.make 4#usize [a0, a1, a2, a3] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] := by
    simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show paFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val]).size
    from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **The rows of `PendingAttestation`** (requires `BlInv` of its bits): the roots of its 4
fields, the bottom level of its tree. -/
theorem PendingAttestation.rows :
    Rows inst h libssz_types.verif_example.PendingAttestation.Insts.Libssz_merkleHashTreeRoot (.container paNames paFields) paV
      (fun x => BlInv x.aggregation_bits) 2 where
  small := by omega
  width := ⟨ 4#usize, rfl, rfl ⟩
  row x row hgood hlen := by
    simp only [libssz_types.verif_example.PendingAttestation.Insts.Libssz_merkleHashTreeRoot]
    unfold libssz_types.verif_example.PendingAttestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root_row
    simp only [libssz_types.libssz_merkle.verif_example.AttestationData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
      libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root]
    have hb : BlInv x.aggregation_bits := hgood
    have hlen' : row.val.length = 4 := hlen
    obtain ⟨ b0, b1, b2, b3, hrowv ⟩ := list_len4 row.val hlen'
    step with SszBitlist.hash_tree_root.spec inst h hl x.aggregation_bits hb.1 hb.2 as ⟨ a0, h0 ⟩
    step as ⟨ row1, hrow1 ⟩
    have hl1 : row1.length = 4 := by
      rw [hrow1]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    step with AttestationData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
    step as ⟨ row2, hrow2 ⟩
    have hl2 : row2.length = 4 := by
      rw [hrow2]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    step with U64.hash_tree_root.spec inst h x.inclusion_delay as ⟨ a2, h2 ⟩
    step as ⟨ row3, hrow3 ⟩
    have hl3 : row3.length = 4 := by
      rw [hrow3]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl2
    step with U64.hash_tree_root.spec inst h x.proposer_index as ⟨ a3, h3 ⟩
    step as ⟨ row4, hrow4 ⟩
    have hl4 : row4.length = 4 := by
      rw [hrow4]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl3
    have hrv : row4.val = [a0, a1, a2, a3] := by
      rw [hrow4, hrow3, hrow2, hrow1]
      simp only [Slice.set_val_eq, hrowv]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    unfold RowRoot paV blV
    rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
      (by simp only [paFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [a0, a1, a2, a3] 2 (by simp [depthFor])

include hl in
/-- **`SyncAggregate`** (altair): the `hash_tree_root` that the macro generates is EthLib's. -/
theorem SyncAggregate.hash_tree_root.spec (x : libssz_types.verif_example.SyncAggregate)
    (hb : Canon (bytes x.sync_committee_bits.bytes.val) 512) :
    libssz_types.verif_example.SyncAggregate.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container saNames saFields) (saV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.SyncAggregate.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with SszBitvector.hash_tree_root.spec inst h hl x.sync_committee_bits hb as ⟨ a0, h0 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.sync_committee_signature as ⟨ a1, h1 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold saV bvV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val] rfl
    (by simp only [saFields] at *; simp [h0, h1, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 2#usize [a0, a1] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show saFields.length = (#[bytes a0.val, bytes a1.val]).size from rfl,
    merkleizeBounded_some_self, ← hr]

end Containers

end Libssz.SszTypes
