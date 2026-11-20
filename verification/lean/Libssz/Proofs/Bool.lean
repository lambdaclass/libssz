module
public import Libssz.Proofs.Bridge
@[expose] public section

/-!
# `bool`: libssz ≡ EthLib

* `Bool.ssz_append.spec`: `bool::ssz_append` appends to `buf` exactly the bytes of
  `Ssz.serialize .bool`.
* `Bool.ssz_write_fixed.spec`: `bool::ssz_write_fixed` writes those same bytes into a one-byte
  slice (the path used by fixed-size containers).
* `Bool.from_ssz_bytes.spec`: `bool::from_ssz_bytes` accepts exactly what
  `Ssz.deserialize .bool` accepts, with the same value, and rejects with the corresponding error.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz_codec
open Libssz.Proofs

namespace Libssz.Proofs

/-- **Encode.** `bool::ssz_append` appends to `buf` exactly the EthLib encoding. -/
theorem Bool.ssz_append.spec (b : Bool) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length < Usize.max) :
    Bool.Insts.LibsszEncodeSszEncode.ssz_append b buf ⦃ buf' =>
      ∃ enc, serialize .bool (.bool b) = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold Bool.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [lift, bind_ok]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨#[if b then 1 else 0], by simp [serialize], ?_⟩
  rw [hbuf', bytes_append]
  cases b <;> rfl

/-- **In-place encode.** `bool::ssz_write_fixed` overwrites `out`, of length 1, with the
EthLib encoding. -/
theorem Bool.ssz_write_fixed.spec (b : Bool) (out : Slice Std.U8) (h : out.length = 1) :
    Bool.Insts.LibsszEncodeSszEncode.ssz_write_fixed b out ⦃ out' =>
      ∃ enc, serialize .bool (.bool b) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold Bool.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize .bool (.bool b) = .ok #[if b then 1 else 0] := by simp [serialize]
  rw [hs, hout', Slice.from_val]
  cases b <;> rfl

/-- **Decode.** `bool::from_ssz_bytes` and `Ssz.deserialize .bool` accept the same inputs,
with the same value, and reject the same ones with corresponding errors. -/
theorem Bool.from_ssz_bytes.spec (s : Slice Std.U8) :
    Bool.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees Value.bool r (deserialize .bool (bytes s.val)) ⦄ := by
  unfold Bool.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [step_simps]
  have hlen := Slice.len_val s
  spec_split
  · -- length ≠ 1: both reject
    rename_i hne
    have h1 : s.length ≠ 1 := by simp at hne; scalar_tac
    have hd : deserialize .bool (bytes s.val) = .error (.scope 1 s.length) := by
      simp [deserialize, h1]; rfl
    rw [WP.spec_ok, hd, Agrees, ← hlen]
    exact ErrMatch.fixedLength 1#usize s.len
  · -- length = 1: look at the single byte
    rename_i heq
    have h1 : s.length = 1 := by simp at heq; scalar_tac
    step as ⟨ x, hx ⟩
    have hd : deserialize .bool (bytes s.val) =
        match byte x with
        | 0 => .ok (.bool false)
        | 1 => .ok (.bool true)
        | b => .error (.notABit b.toNat) := by
      obtain ⟨y, hy⟩ : ∃ y, s.val = [y] := List.length_eq_one_iff.mp h1
      simp only [hy, List.getElem_cons_zero] at hx
      subst hx
      simp [deserialize, hy, bytes]
      rfl
    rw [hd]
    split
    · rw [WP.spec_ok]; rfl
    · rw [WP.spec_ok]; rfl
    · rename_i _ hn0 hn1
      have hx0 : x.val ≠ 0 := fun e => hn0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      have hx1 : x.val ≠ 1 := fun e => hn1 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      rw [WP.spec_ok]
      split
      · rename_i e; have := congrArg UInt8.toNat e; rw [byte_toNat] at this; exact absurd this hx0
      · rename_i e; have := congrArg UInt8.toNat e; rw [byte_toNat] at this; exact absurd this hx1
      · exact ErrMatch.booleanByte x

end Libssz.Proofs
