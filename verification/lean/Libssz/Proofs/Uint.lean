module
public import Libssz.Proofs.Bridge
@[expose] public section

/-!
# `u8` … `u128`: libssz ≡ EthLib

The statements are the same as for libssz before the verification rewrite. What changes is
the code: in libssz, `uN::from_ssz_bytes` is

```rust
let arr = decode_uint::<N>(bytes)?;
Ok(Self::from_le_bytes(arr))
```

without passing `from_le_bytes` as a closure. Aeneas translates it entirely (the `?` becomes
`Try::branch` and `from_residual`), so nothing is written by hand.

The work is in three generic lemmas: `decode_uint.spec`, `uint_err_agrees` and
`uint_ok_agrees`. The proof for each width chains them over the generated function.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## Generic lemmas -/

/-- `decode_uint::<N>(bytes)`: rejects if the length is not `N`; otherwise, returns the same
bytes. -/
theorem decode_uint.spec (N : Std.Usize) (s : Slice Std.U8) :
    decode.decode_uint N s ⦃ r =>
      (s.length ≠ N.val ∧ r = .Err (.InvalidFixedLength N s.len)) ∨
      (s.length = N.val ∧ ∃ arr : Array Std.U8 N, arr.val = s.val ∧ r = .Ok arr) ⦄ := by
  unfold decode.decode_uint
  simp only [step_simps]
  spec_split
  · rename_i hne
    have h1 : s.length ≠ N.val := by simp at hne; scalar_tac
    rw [WP.spec_ok]
    exact Or.inl ⟨h1, rfl⟩
  · rename_i heq
    have h1 : s.length = N.val := by simp at heq; scalar_tac
    step as ⟨ sl, back, hsl, hback ⟩
    step as ⟨ s1, hs1 ⟩
    subst hs1 hback
    exact Or.inr ⟨h1, _, Array.from_slice_val _ _ (by simp [h1]), rfl⟩

/-- If the length is not `N`, the Rust error is the EthLib one. -/
theorem uint_err_agrees {α : Type} (toV : α → Value) (N : Std.Usize) (s : Slice Std.U8)
    (h1 : s.length ≠ N.val) :
    Agrees toV (.Err (.InvalidFixedLength N s.len)) (deserialize (.uint N.val) (bytes s.val)) := by
  have hd : deserialize (.uint N.val) (bytes s.val) = .error (.scope N.val s.length) := by
    simp [deserialize, h1]; rfl
  rw [hd, Agrees, ← Slice.len_val s]
  exact ErrMatch.fixedLength N s.len

/-- If the length is `N` and `x` is the little-endian reading of those bytes, Rust and
EthLib give the same value. -/
theorem uint_ok_agrees {T : Type} {N : Std.Usize} (toN : T → Nat) (x : T) (arr : Array Std.U8 N)
    (s : Slice Std.U8) (h1 : s.length = N.val) (harr : arr.val = s.val)
    (hx : toN x = leValue UScalar.val arr.val) :
    Agrees (fun x => .uint (toN x)) (.Ok x) (deserialize (.uint N.val) (bytes s.val)) := by
  have hd : deserialize (.uint N.val) (bytes s.val) =
      .ok (.uint (readUint (bytes s.val) 0 N.val)) := by
    simp [deserialize, h1]; rfl
  rw [hd, Agrees, hx, harr, ← h1, readUint_bytes]

/-! ## `u8` -/

/-- **Decode `u8`.** -/
theorem U8.from_ssz_bytes.spec (s : Slice Std.U8) :
    U8.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U8 => .uint x.val) r (deserialize Desc.uint8 (bytes s.val)) ⦄ := by
  unfold U8.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec 1#usize s as ⟨ r, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, arr, harr, rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok]
    exact uint_err_agrees _ 1#usize s h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok]
    refine uint_ok_agrees UScalar.val _ arr s h1 harr ?_
    simp only [core.num.U8.from_le_bytes, UScalar.val, BitVec.toNat_cast, toNat_fromLEBytes,
      leValue_map]
    rfl

/-- **Encode `u8`.** -/
theorem U8.ssz_append.spec (x : Std.U8) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 1 ≤ Usize.max) :
    U8.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize Desc.uint8 (.uint x.val) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold U8.Insts.LibsszEncodeSszEncode.ssz_append
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨uintBytes 1 x.val, ?_, ?_⟩
  · have := x.hBounds
    simp [serialize, Desc.uint8]
    scalar_tac
  · rw [hbuf', bytes_append, Slice.from_val, ha, bytes_toLEBytes 1 x.bv (by rfl)]
    rfl

/-! ## `u16` -/

/-- **Decode `u16`.** -/
theorem U16.from_ssz_bytes.spec (s : Slice Std.U8) :
    U16.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U16 => .uint x.val) r (deserialize Desc.uint16 (bytes s.val)) ⦄ := by
  unfold U16.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec 2#usize s as ⟨ r, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, arr, harr, rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok]
    exact uint_err_agrees _ 2#usize s h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok]
    refine uint_ok_agrees UScalar.val _ arr s h1 harr ?_
    simp only [core.num.U16.from_le_bytes, UScalar.val, BitVec.toNat_cast, toNat_fromLEBytes,
      leValue_map]
    rfl

/-- **Encode `u16`.** -/
theorem U16.ssz_append.spec (x : Std.U16) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 2 ≤ Usize.max) :
    U16.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize Desc.uint16 (.uint x.val) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_append
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨uintBytes 2 x.val, ?_, ?_⟩
  · have := x.hBounds
    simp [serialize, Desc.uint16]
    scalar_tac
  · rw [hbuf', bytes_append, Slice.from_val, ha, bytes_toLEBytes 2 x.bv (by rfl)]
    rfl

/-! ## `u32` -/

/-- **Decode `u32`.** -/
theorem U32.from_ssz_bytes.spec (s : Slice Std.U8) :
    U32.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U32 => .uint x.val) r (deserialize Desc.uint32 (bytes s.val)) ⦄ := by
  unfold U32.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec 4#usize s as ⟨ r, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, arr, harr, rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok]
    exact uint_err_agrees _ 4#usize s h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok]
    refine uint_ok_agrees UScalar.val _ arr s h1 harr ?_
    simp only [core.num.U32.from_le_bytes, UScalar.val, BitVec.toNat_cast, toNat_fromLEBytes,
      leValue_map]
    rfl

/-- **Encode `u32`.** -/
theorem U32.ssz_append.spec (x : Std.U32) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 4 ≤ Usize.max) :
    U32.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize Desc.uint32 (.uint x.val) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_append
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨uintBytes 4 x.val, ?_, ?_⟩
  · have := x.hBounds
    simp [serialize, Desc.uint32]
    scalar_tac
  · rw [hbuf', bytes_append, Slice.from_val, ha, bytes_toLEBytes 4 x.bv (by rfl)]
    rfl

/-! ## `u64` -/

/-- **Decode `u64`.** -/
theorem U64.from_ssz_bytes.spec (s : Slice Std.U8) :
    U64.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U64 => .uint x.val) r (deserialize Desc.uint64 (bytes s.val)) ⦄ := by
  unfold U64.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec 8#usize s as ⟨ r, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, arr, harr, rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok]
    exact uint_err_agrees _ 8#usize s h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok]
    refine uint_ok_agrees UScalar.val _ arr s h1 harr ?_
    simp only [core.num.U64.from_le_bytes, UScalar.val, BitVec.toNat_cast, toNat_fromLEBytes,
      leValue_map]
    rfl

/-- **Encode `u64`.** -/
theorem U64.ssz_append.spec (x : Std.U64) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 8 ≤ Usize.max) :
    U64.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize Desc.uint64 (.uint x.val) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_append
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨uintBytes 8 x.val, ?_, ?_⟩
  · have := x.hBounds
    simp [serialize, Desc.uint64]
    scalar_tac
  · rw [hbuf', bytes_append, Slice.from_val, ha, bytes_toLEBytes 8 x.bv (by rfl)]
    rfl

/-! ## `u128` -/

/-- **Decode `u128`.** -/
theorem U128.from_ssz_bytes.spec (s : Slice Std.U8) :
    U128.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U128 => .uint x.val) r (deserialize Desc.uint128 (bytes s.val)) ⦄ := by
  unfold U128.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec 16#usize s as ⟨ r, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, arr, harr, rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok]
    exact uint_err_agrees _ 16#usize s h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, WP.spec_ok]
    refine uint_ok_agrees UScalar.val _ arr s h1 harr ?_
    simp only [core.num.U128.from_le_bytes, UScalar.val, BitVec.toNat_cast, toNat_fromLEBytes,
      leValue_map]
    rfl

/-- **Encode `u128`.** -/
theorem U128.ssz_append.spec (x : Std.U128) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 16 ≤ Usize.max) :
    U128.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize Desc.uint128 (.uint x.val) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_append
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨uintBytes 16 x.val, ?_, ?_⟩
  · have := x.hBounds
    simp [serialize, Desc.uint128]
    scalar_tac
  · rw [hbuf', bytes_append, Slice.from_val, ha, bytes_toLEBytes 16 x.bv (by rfl)]
    rfl

end Libssz.Proofs
