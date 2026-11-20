module
public import Libssz.Proofs.Bridge
@[expose] public section

/-!
# `u8` … `u128`: libssz ≡ EthLib

In libssz, `uN::from_ssz_bytes` is

```rust
let mut arr = [0u8; N];
decode_uint(bytes, &mut arr)?;
Ok(Self::from_le_bytes(arr))
```

`decode_uint` writes into an array owned by the caller instead of returning
`Result<[u8; N], _>` (for `u128`, that `Result` travels through memory with the array
misaligned, and reading it back as a 16-byte integer is expensive). Aeneas translates it in
full: the `&mut arr` becomes one array going in and another coming out, and the `?` becomes
`Try::branch` and `from_residual`.

The work is in three generic lemmas: `decode_uint.spec`, `uint_err_agrees` and
`uint_ok_agrees`. The proof for each width chains them over the generated function.

Each type also has a second encode, `ssz_write_fixed`, which writes the encoding into a slice
that already has exactly the right size instead of appending it to a `Vec`
(`uN.ssz_write_fixed.spec`). It is used by `ContainerEncoder::append_fixed` and by fixed-size
containers.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz_codec
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## Generic lemmas -/

/-- `decode_uint(bytes, &mut arr)`: rejects if the length is not `N`; otherwise, leaves the
same bytes in `arr`. -/
theorem decode_uint.spec {N : Std.Usize} (s : Slice Std.U8) (arr0 : Array Std.U8 N) :
    decode.decode_uint s arr0 ⦃ r arr =>
      (s.length ≠ N.val ∧ r = .Err (.InvalidFixedLength N s.len)) ∨
      (s.length = N.val ∧ arr.val = s.val ∧ r = .Ok ()) ⦄ := by
  unfold decode.decode_uint
  simp only [step_simps]
  spec_split
  · rename_i hne
    have h1 : s.length ≠ N.val := by simp at hne; scalar_tac
    simp only [WP.spec_ok, WP.uncurry']
    exact Or.inl ⟨h1, trivial⟩
  · rename_i heq
    have h1 : s.length = N.val := by simp at heq; scalar_tac
    step as ⟨ sl, back, hsl, hback ⟩
    step as ⟨ s1, hs1 ⟩
    subst hs1 hback
    exact Or.inr ⟨h1, Array.from_slice_val _ _ (by simp [h1])⟩

/-- If the length is not `N`, the Rust error is the EthLib one. -/
theorem uint_err_agrees {α : Type} (toV : α → Value) (N : Std.Usize) (s : Slice Std.U8)
    (h1 : s.length ≠ N.val) :
    Agrees toV (.Err (.InvalidFixedLength N s.len)) (deserialize (.uint N.val) (bytes s.val)) := by
  have hd : deserialize (.uint N.val) (bytes s.val) = .error (.scope N.val s.length) := by
    simp [deserialize, h1]; rfl
  rw [hd, Agrees, ← Slice.len_val s]
  exact ErrMatch.fixedLength N s.len

/-- If the length is `N` and `x` is the little-endian reading of those bytes, Rust and EthLib
give the same value. -/
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
  step with decode_uint.spec s (Array.repeat 1#usize 0#u8) as ⟨ r, arr, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, harr, rfl⟩
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

/-- **In-place encode `u8`** (`ssz_write_fixed`): overwrites `out`, of length 1, with the
encoding. -/
theorem U8.ssz_write_fixed.spec (x : Std.U8) (out : Slice Std.U8) (h : out.length = 1) :
    U8.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      ∃ enc, serialize Desc.uint8 (.uint x.val) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold U8.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize Desc.uint8 (.uint x.val) = .ok (uintBytes 1 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint8]
    scalar_tac
  rw [hs, hout', Slice.from_val, ha, bytes_toLEBytes 1 x.bv (by rfl)]
  rfl

/-! ## `u16` -/

/-- **Decode `u16`.** -/
theorem U16.from_ssz_bytes.spec (s : Slice Std.U8) :
    U16.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U16 => .uint x.val) r (deserialize Desc.uint16 (bytes s.val)) ⦄ := by
  unfold U16.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec s (Array.repeat 2#usize 0#u8) as ⟨ r, arr, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, harr, rfl⟩
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

/-- **In-place encode `u16`** (`ssz_write_fixed`): overwrites `out`, of length 2, with the
encoding. -/
theorem U16.ssz_write_fixed.spec (x : Std.U16) (out : Slice Std.U8) (h : out.length = 2) :
    U16.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      ∃ enc, serialize Desc.uint16 (.uint x.val) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize Desc.uint16 (.uint x.val) = .ok (uintBytes 2 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint16]
    scalar_tac
  rw [hs, hout', Slice.from_val, ha, bytes_toLEBytes 2 x.bv (by rfl)]
  rfl

/-! ## `u32` -/

/-- **Decode `u32`.** -/
theorem U32.from_ssz_bytes.spec (s : Slice Std.U8) :
    U32.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U32 => .uint x.val) r (deserialize Desc.uint32 (bytes s.val)) ⦄ := by
  unfold U32.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec s (Array.repeat 4#usize 0#u8) as ⟨ r, arr, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, harr, rfl⟩
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

/-- **In-place encode `u32`** (`ssz_write_fixed`): overwrites `out`, of length 4, with the
encoding. -/
theorem U32.ssz_write_fixed.spec (x : Std.U32) (out : Slice Std.U8) (h : out.length = 4) :
    U32.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      ∃ enc, serialize Desc.uint32 (.uint x.val) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize Desc.uint32 (.uint x.val) = .ok (uintBytes 4 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint32]
    scalar_tac
  rw [hs, hout', Slice.from_val, ha, bytes_toLEBytes 4 x.bv (by rfl)]
  rfl

/-! ## `u64` -/

/-- **Decode `u64`.** -/
theorem U64.from_ssz_bytes.spec (s : Slice Std.U8) :
    U64.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U64 => .uint x.val) r (deserialize Desc.uint64 (bytes s.val)) ⦄ := by
  unfold U64.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec s (Array.repeat 8#usize 0#u8) as ⟨ r, arr, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, harr, rfl⟩
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

/-- **In-place encode `u64`** (`ssz_write_fixed`): overwrites `out`, of length 8, with the
encoding. -/
theorem U64.ssz_write_fixed.spec (x : Std.U64) (out : Slice Std.U8) (h : out.length = 8) :
    U64.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      ∃ enc, serialize Desc.uint64 (.uint x.val) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize Desc.uint64 (.uint x.val) = .ok (uintBytes 8 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint64]
    scalar_tac
  rw [hs, hout', Slice.from_val, ha, bytes_toLEBytes 8 x.bv (by rfl)]
  rfl

/-! ## `u128` -/

/-- **Decode `u128`.** -/
theorem U128.from_ssz_bytes.spec (s : Slice Std.U8) :
    U128.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U128 => .uint x.val) r (deserialize Desc.uint128 (bytes s.val)) ⦄ := by
  unfold U128.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  step with decode_uint.spec s (Array.repeat 16#usize 0#u8) as ⟨ r, arr, hr ⟩
  rcases hr with ⟨h1, rfl⟩ | ⟨h1, harr, rfl⟩
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

/-- **In-place encode `u128`** (`ssz_write_fixed`): overwrites `out`, of length 16, with the
encoding. -/
theorem U128.ssz_write_fixed.spec (x : Std.U128) (out : Slice Std.U8) (h : out.length = 16) :
    U128.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      ∃ enc, serialize Desc.uint128 (.uint x.val) = .ok enc ∧ bytes out'.val = enc ⦄ := by
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  step as ⟨ a, ha ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  have hs : serialize Desc.uint128 (.uint x.val) = .ok (uintBytes 16 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint128]
    scalar_tac
  rw [hs, hout', Slice.from_val, ha, bytes_toLEBytes 16 x.bv (by rfl)]
  rfl

end Libssz.Proofs
