module
public import Libssz.Proofs.Bridge
public import Libssz.Proofs.ListSpec
public import Libssz.Proofs.Bool
@[expose] public section

/-!
# Lists of integers, libssz ≡ EthLib

For each width `uN` (`N ∈ {1, 2, 4, 8, 16}` bytes):

* `UN.decode_list.spec`: `decode_list_with_max::<uN>(bytes, max)` and
  `Ssz.deserialize (.list (.uint N) max)` accept exactly the same inputs, with the same
  values, and reject the same ones with corresponding errors (`ErrMatch`), for every input
  **shorter than 2³² bytes**.
* `UN.vec_from_ssz_bytes.spec`: the same for `Vec<uN>::from_ssz_bytes` (limit `usize::MAX`).
* `UN.encode_list.spec`: `Vec<uN>::ssz_append` appends to `buf` exactly the bytes of
  `Ssz.serialize (.list (.uint N) limit)`, if the list fits within the limit and takes fewer
  than 2³² bytes.

And the same for:
* `[u8; N]` against `byteVector N`: `ArrayU8N.from_ssz_bytes.spec` and
  `ArrayU8N.ssz_append.spec`;
* `Vec<[u8; N]>` against lists of `byteVector N`, with `N > 0`: `ArrayU8N.decode_list.spec`,
  `ArrayU8N.vec_from_ssz_bytes.spec` and `ArrayU8N.encode_list.spec`;
* `Vec<bool>` against lists of `bool`: `Bool.decode_list.spec`, `Bool.vec_from_ssz_bytes.spec`
  and `Bool.encode_list.spec`. Here each element can fail, and libssz and EthLib fail at the
  same byte with the same error.

Underneath are the invariants of the two loops that, in libssz before the verification
rewrite, were `unsafe` `memcpy`s: `UN.decode_loop.spec` (`ssz_decode_fixed_vec`) and
`UN.encode_loop.spec` (`ssz_append_fixed_slice`).

**Why the `< 2³²` hypothesis.** EthLib rejects any input of 2³² bytes or more
(`offsetOverflow`), also for lists of fixed-size elements; libssz has no such check. On a
64-bit machine they diverge there, and `U64.decode_list_diverges` (at the end) proves it.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## `u16` -/

theorem U16.decode_loop.spec (bytes : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Std.U16) (i : Std.Usize)
    (hc : count.val * 2 ≤ bytes.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (·.val) = (List.range i.val).map (chunkVal 2 bytes.val)) :
    U16.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop bytes count result i ⦃ r =>
      r.val.map (·.val) = (List.range count.val).map (chunkVal 2 bytes.val) ⦄ := by
  unfold U16.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ s2, hs2 ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ result1, hr1 ⟩
    step as ⟨ i4, hi4 ⟩
    -- The value read is chunk `i`.
    have hlen8 : s1.val.length = 2 := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen8)
    have hxv : x.val = chunkVal 2 bytes.val i.val := by
      have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
        simp [UScalar.val, hx]
      rw [this, toNat_fromLEBytes, leValue_map, hback8, hs1, chunkVal, List.slice, hi2, hi1,
        Nat.add_sub_cancel_left]
      rfl
    apply U16.decode_loop.spec bytes count result1 i4 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi4, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac


theorem U16.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (h : s.length % 2 = 0) :
    U16.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 2)).map (chunkVal 2 s.val)
      | .Err _ => False ⦄ := by
  unfold U16.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  have hlen := Slice.len_val s
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (s.len.val % (2#usize).val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step as ⟨ count, hcount ⟩
  step with U16.decode_loop.spec s count (alloc.vec.Vec.with_capacity Std.U16 count) 0#usize
    (by rw [hcount]; exact Nat.div_mul_le_self _ _) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hcount]
  rfl

theorem U16.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max U16.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Std.U16 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint16 max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [U16.Insts.LibsszDecodeSszDecode, U16.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U16.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_uint 2 max.val s.val (by norm_num) (by simpa using hs)
  rw [show Desc.uint16 = .uint 2 from rfl, hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (2#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % 2 = 0
  · have hm' : (s.len.val % (2#usize).val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % 2 ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / 2 := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / 2 > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / 2 > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      step with U16.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.uint) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of 2
    have hm' : (s.len.val % (2#usize).val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % 2 ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % 2 = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided 2#usize s.len
    rw [hlen] at this
    exact this

theorem U16.encode_loop.spec (items : Slice Std.U16) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + 2 * (items.length - i.val) ≤ Usize.max) :
    U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun x => uintBytes 2 x.val) ⦄ := by
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · step as ⟨ x, hx ⟩
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlt : i.val < items.length := by scalar_tac
    apply WP.spec_mono (U16.encode_loop.spec items buf1 i3 (by scalar_tac)
      (by simp [hbuf1] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, ha, bytes_toLEBytes 2 x.bv (by rfl), hi3,
      Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
    rfl
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

theorem U16.encode_list.spec (v : alloc.vec.Vec Std.U16) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 2 * v.length < 2 ^ 32)
    (hb : buf.length + 2 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U16.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint16 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U16.Insts.LibsszEncodeSszEncode, U16.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref]; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with U16.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 2) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 2 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint16 = .uint 2 from rfl]
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<U16>::from_ssz_bytes`**: it is `decode_list_with_max` with no limit (`usize::MAX`). -/
theorem U16.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U16.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U16 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint16 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U16.decode_list.spec s _ hs

/-! ## `u32` -/

theorem U32.decode_loop.spec (bytes : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hc : count.val * 4 ≤ bytes.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (·.val) = (List.range i.val).map (chunkVal 4 bytes.val)) :
    U32.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop bytes count result i ⦃ r =>
      r.val.map (·.val) = (List.range count.val).map (chunkVal 4 bytes.val) ⦄ := by
  unfold U32.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ s2, hs2 ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ result1, hr1 ⟩
    step as ⟨ i4, hi4 ⟩
    -- The value read is chunk `i`.
    have hlen8 : s1.val.length = 4 := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen8)
    have hxv : x.val = chunkVal 4 bytes.val i.val := by
      have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
        simp [UScalar.val, hx]
      rw [this, toNat_fromLEBytes, leValue_map, hback8, hs1, chunkVal, List.slice, hi2, hi1,
        Nat.add_sub_cancel_left]
      rfl
    apply U32.decode_loop.spec bytes count result1 i4 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi4, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac


theorem U32.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (h : s.length % 4 = 0) :
    U32.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 4)).map (chunkVal 4 s.val)
      | .Err _ => False ⦄ := by
  unfold U32.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  have hlen := Slice.len_val s
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (s.len.val % (4#usize).val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step as ⟨ count, hcount ⟩
  step with U32.decode_loop.spec s count (alloc.vec.Vec.with_capacity Std.U32 count) 0#usize
    (by rw [hcount]; exact Nat.div_mul_le_self _ _) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hcount]
  rfl

theorem U32.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max U32.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Std.U32 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint32 max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [U32.Insts.LibsszDecodeSszDecode, U32.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U32.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_uint 4 max.val s.val (by norm_num) (by simpa using hs)
  rw [show Desc.uint32 = .uint 4 from rfl, hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (4#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % 4 = 0
  · have hm' : (s.len.val % (4#usize).val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % 4 ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / 4 := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / 4 > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / 4 > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      step with U32.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.uint) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of 4
    have hm' : (s.len.val % (4#usize).val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % 4 ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % 4 = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided 4#usize s.len
    rw [hlen] at this
    exact this

theorem U32.encode_loop.spec (items : Slice Std.U32) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + 4 * (items.length - i.val) ≤ Usize.max) :
    U32.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun x => uintBytes 4 x.val) ⦄ := by
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · step as ⟨ x, hx ⟩
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlt : i.val < items.length := by scalar_tac
    apply WP.spec_mono (U32.encode_loop.spec items buf1 i3 (by scalar_tac)
      (by simp [hbuf1] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, ha, bytes_toLEBytes 4 x.bv (by rfl), hi3,
      Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
    rfl
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

theorem U32.encode_list.spec (v : alloc.vec.Vec Std.U32) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 4 * v.length < 2 ^ 32)
    (hb : buf.length + 4 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U32.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint32 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U32.Insts.LibsszEncodeSszEncode, U32.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref]; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with U32.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 4) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 4 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint32 = .uint 4 from rfl]
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<U32>::from_ssz_bytes`**: it is `decode_list_with_max` with no limit (`usize::MAX`). -/
theorem U32.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U32.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U32 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint32 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U32.decode_list.spec s _ hs

/-! ## `u64` -/

theorem U64.decode_loop.spec (bytes : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Std.U64) (i : Std.Usize)
    (hc : count.val * 8 ≤ bytes.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (·.val) = (List.range i.val).map (chunkVal 8 bytes.val)) :
    U64.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop bytes count result i ⦃ r =>
      r.val.map (·.val) = (List.range count.val).map (chunkVal 8 bytes.val) ⦄ := by
  unfold U64.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ s2, hs2 ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ result1, hr1 ⟩
    step as ⟨ i4, hi4 ⟩
    -- The value read is chunk `i`.
    have hlen8 : s1.val.length = 8 := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen8)
    have hxv : x.val = chunkVal 8 bytes.val i.val := by
      have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
        simp [UScalar.val, hx]
      rw [this, toNat_fromLEBytes, leValue_map, hback8, hs1, chunkVal, List.slice, hi2, hi1,
        Nat.add_sub_cancel_left]
      rfl
    apply U64.decode_loop.spec bytes count result1 i4 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi4, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac


theorem U64.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (h : s.length % 8 = 0) :
    U64.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 8)).map (chunkVal 8 s.val)
      | .Err _ => False ⦄ := by
  unfold U64.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  have hlen := Slice.len_val s
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (s.len.val % (8#usize).val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step as ⟨ count, hcount ⟩
  step with U64.decode_loop.spec s count (alloc.vec.Vec.with_capacity Std.U64 count) 0#usize
    (by rw [hcount]; exact Nat.div_mul_le_self _ _) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hcount]
  rfl

theorem U64.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max U64.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Std.U64 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint64 max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [U64.Insts.LibsszDecodeSszDecode, U64.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_uint 8 max.val s.val (by norm_num) (by simpa using hs)
  rw [show Desc.uint64 = .uint 8 from rfl, hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (8#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % 8 = 0
  · have hm' : (s.len.val % (8#usize).val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % 8 ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / 8 := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / 8 > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / 8 > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      step with U64.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.uint) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of 8
    have hm' : (s.len.val % (8#usize).val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % 8 ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % 8 = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided 8#usize s.len
    rw [hlen] at this
    exact this

theorem U64.encode_loop.spec (items : Slice Std.U64) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + 8 * (items.length - i.val) ≤ Usize.max) :
    U64.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun x => uintBytes 8 x.val) ⦄ := by
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · step as ⟨ x, hx ⟩
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlt : i.val < items.length := by scalar_tac
    apply WP.spec_mono (U64.encode_loop.spec items buf1 i3 (by scalar_tac)
      (by simp [hbuf1] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, ha, bytes_toLEBytes 8 x.bv (by rfl), hi3,
      Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
    rfl
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

theorem U64.encode_list.spec (v : alloc.vec.Vec Std.U64) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 8 * v.length < 2 ^ 32)
    (hb : buf.length + 8 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U64.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint64 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U64.Insts.LibsszEncodeSszEncode, U64.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref]; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with U64.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 8) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 8 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint64 = .uint 8 from rfl]
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<U64>::from_ssz_bytes`**: it is `decode_list_with_max` with no limit (`usize::MAX`). -/
theorem U64.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U64.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U64 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint64 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U64.decode_list.spec s _ hs

/-! ## `u128` -/

theorem U128.decode_loop.spec (bytes : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Std.U128) (i : Std.Usize)
    (hc : count.val * 16 ≤ bytes.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (·.val) = (List.range i.val).map (chunkVal 16 bytes.val)) :
    U128.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop bytes count result i ⦃ r =>
      r.val.map (·.val) = (List.range count.val).map (chunkVal 16 bytes.val) ⦄ := by
  unfold U128.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ s2, hs2 ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ result1, hr1 ⟩
    step as ⟨ i4, hi4 ⟩
    -- The value read is chunk `i`.
    have hlen8 : s1.val.length = 16 := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen8)
    have hxv : x.val = chunkVal 16 bytes.val i.val := by
      have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
        simp [UScalar.val, hx]
      rw [this, toNat_fromLEBytes, leValue_map, hback8, hs1, chunkVal, List.slice, hi2, hi1,
        Nat.add_sub_cancel_left]
      rfl
    apply U128.decode_loop.spec bytes count result1 i4 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi4, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac


theorem U128.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (h : s.length % 16 = 0) :
    U128.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 16)).map (chunkVal 16 s.val)
      | .Err _ => False ⦄ := by
  unfold U128.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  have hlen := Slice.len_val s
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (s.len.val % (16#usize).val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step as ⟨ count, hcount ⟩
  step with U128.decode_loop.spec s count (alloc.vec.Vec.with_capacity Std.U128 count) 0#usize
    (by rw [hcount]; exact Nat.div_mul_le_self _ _) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hcount]
  rfl

theorem U128.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max U128.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Std.U128 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint128 max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [U128.Insts.LibsszDecodeSszDecode, U128.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U128.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_uint 16 max.val s.val (by norm_num) (by simpa using hs)
  rw [show Desc.uint128 = .uint 16 from rfl, hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (16#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % 16 = 0
  · have hm' : (s.len.val % (16#usize).val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % 16 ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / 16 := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / 16 > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / 16 > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      step with U128.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.uint) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of 16
    have hm' : (s.len.val % (16#usize).val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % 16 ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % 16 = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided 16#usize s.len
    rw [hlen] at this
    exact this

theorem U128.encode_loop.spec (items : Slice Std.U128) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + 16 * (items.length - i.val) ≤ Usize.max) :
    U128.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun x => uintBytes 16 x.val) ⦄ := by
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · step as ⟨ x, hx ⟩
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlt : i.val < items.length := by scalar_tac
    apply WP.spec_mono (U128.encode_loop.spec items buf1 i3 (by scalar_tac)
      (by simp [hbuf1] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, ha, bytes_toLEBytes 16 x.bv (by rfl), hi3,
      Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
    rfl
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

theorem U128.encode_list.spec (v : alloc.vec.Vec Std.U128) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 16 * v.length < 2 ^ 32)
    (hb : buf.length + 16 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U128.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint128 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U128.Insts.LibsszEncodeSszEncode, U128.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref]; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with U128.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 16) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 16 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint128 = .uint 16 from rfl]
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<U128>::from_ssz_bytes`**: it is `decode_list_with_max` with no limit (`usize::MAX`). -/
theorem U128.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U128.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U128 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint128 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U128.decode_list.spec s _ hs

/-! ## `u8` -/

theorem U8.decode_loop.spec (bytes : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hc : count.val * 1 ≤ bytes.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (·.val) = (List.range i.val).map (chunkVal 1 bytes.val)) :
    U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop bytes count result i ⦃ r =>
      r.val.map (·.val) = (List.range count.val).map (chunkVal 1 bytes.val) ⦄ := by
  unfold U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ s2, hs2 ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ result1, hr1 ⟩
    -- The value read is chunk `i`.
    have hlen8 : s1.val.length = 1 := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen8)
    have hxv : x.val = chunkVal 1 bytes.val i.val := by
      have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
        simp [UScalar.val, hx]
      rw [this, toNat_fromLEBytes, leValue_map, hback8, hs1, chunkVal, List.slice, hi1,
        Nat.add_sub_cancel_left, Nat.mul_one]
      rfl
    apply U8.decode_loop.spec bytes count result1 i1 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi1, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac


theorem U8.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (h : s.length % 1 = 0) :
    U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 1)).map (chunkVal 1 s.val)
      | .Err _ => False ⦄ := by
  unfold U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  have hlen := Slice.len_val s
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (s.len.val % (1#usize).val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step with U8.decode_loop.spec s s.len (alloc.vec.Vec.with_capacity Std.U8 s.len) 0#usize
    (by rw [hlen]; simp) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hlen, Nat.div_one]

theorem U8.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max U8.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Std.U8 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint8 max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [U8.Insts.LibsszDecodeSszDecode, U8.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U8.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_uint 1 max.val s.val (by norm_num) (by simpa using hs)
  rw [show Desc.uint8 = .uint 1 from rfl, hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (1#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % 1 = 0
  · have hm' : (s.len.val % (1#usize).val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % 1 ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / 1 := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / 1 > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / 1 > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      step with U8.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.uint) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of 1 (impossible: this case is contradictory)
    have hm' : (s.len.val % (1#usize).val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % 1 ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % 1 = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided 1#usize s.len
    rw [hlen] at this
    exact this

theorem U8.encode_loop.spec (items : Slice Std.U8) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + 1 * (items.length - i.val) ≤ Usize.max) :
    U8.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun x => uintBytes 1 x.val) ⦄ := by
  unfold U8.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · step as ⟨ x, hx ⟩
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlt : i.val < items.length := by scalar_tac
    apply WP.spec_mono (U8.encode_loop.spec items buf1 i3 (by scalar_tac)
      (by simp [hbuf1] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, ha, bytes_toLEBytes 1 x.bv (by rfl), hi3,
      Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
    rfl
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

theorem U8.encode_list.spec (v : alloc.vec.Vec Std.U8) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 1 * v.length < 2 ^ 32)
    (hb : buf.length + 1 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U8.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint8 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U8.Insts.LibsszEncodeSszEncode, U8.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U8.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with U8.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 1) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 1 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint8 = .uint 1 from rfl]
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<U8>::from_ssz_bytes`**: it is `decode_list_with_max` with no limit (`usize::MAX`). -/
theorem U8.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U8.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U8 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint8 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U8.decode_list.spec s _ hs

/-! ## `[u8; N]` -/

/-- **Decode `[u8; N]`** against `byteVector N`. -/
theorem ArrayU8N.from_ssz_bytes.spec (N : Std.Usize) (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    ArrayU8N.Insts.LibsszDecodeSszDecode.from_ssz_bytes N s ⦃ r =>
      Agrees (fun a : Array Std.U8 N => .bytes (bytes a.val)) r
        (deserialize (.byteVector N.val) (bytes s.val)) ⦄ := by
  unfold ArrayU8N.Insts.LibsszDecodeSszDecode.from_ssz_bytes decode.decode_byte_array
  simp only [step_simps]
  have hlen := Slice.len_val s
  have hlt : ¬ (2 ^ (8 * bytesPerOffset) ≤ (↑s : List Std.U8).length) := by
    norm_num [bytesPerOffset]; exact hs
  spec_split
  · rename_i hne
    have h1 : s.length ≠ N.val := by simp at hne; scalar_tac
    have hd : deserialize (.byteVector N.val) (bytes s.val) = .error (.scope N.val s.length) := by
      simp only [deserialize, bytes_size]
      simp [h1, hlt]; rfl
    rw [WP.spec_ok, hd, Agrees, ← hlen]
    exact ErrMatch.fixedLength N s.len
  · rename_i heq
    have h1 : s.length = N.val := by simp at heq; scalar_tac
    step as ⟨ r, hr ⟩
    cases r with
    | Ok a =>
      simp only [core.result.Result.expect, bind_ok, WP.spec_ok]
      have hd : deserialize (.byteVector N.val) (bytes s.val) = .ok (.bytes (bytes s.val)) := by
        simp only [deserialize, bytes_size]
        have hltN : ¬ (2 ^ (8 * bytesPerOffset) ≤ N.val) := by rw [← h1]; exact hlt
        simp [h1, hltN]; rfl
      rw [hd, Agrees, hr.1]
    | Err e => exact absurd h1 hr

/-- **Encode `[u8; N]`** against `byteVector N`. -/
theorem ArrayU8N.ssz_append.spec (N : Std.Usize) (a : Array Std.U8 N) (buf : alloc.vec.Vec Std.U8)
    (hN : N.val < 2 ^ 32) (hb : buf.length + N.val ≤ Usize.max) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append a buf ⦃ buf' =>
      ∃ enc, serialize (.byteVector N.val) (.bytes (bytes a.val)) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  refine ⟨bytes a.val, ?_, by rw [hbuf', bytes_append, Slice.from_val]⟩
  have ha : (bytes a.val).size = N.val := by simp
  have h32 : ¬ ((bytes a.val).size ≥ 2 ^ (8 * bytesPerOffset)) := by
    rw [ha, bytesPerOffset]; norm_num; exact hN
  simp only [serialize, ha, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hltN : ¬ (2 ^ (8 * bytesPerOffset) ≤ N.val) := by rw [← ha]; omega
  simp only [hltN, ↓reduceIte]; rfl

/-! ## `Vec<[u8; N]>` -/

/-- The `k`-th `n`-byte chunk of `l`, as EthLib bytes. -/
def chunkBytes (n : Nat) (l : List Std.U8) (k : Nat) : Bytes := bytes ((l.drop (k * n)).take n)

theorem decode_byte_array_vec_loop.spec {N : Std.Usize} (src : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec (Array Std.U8 N)) (i : Std.Usize)
    (hc : count.val * N.val ≤ src.length) (hi : i.val ≤ count.val)
    (hr : result.val.map (fun a => bytes a.val) = (List.range i.val).map (chunkBytes N.val src.val)) :
    decode.decode_byte_array_vec_loop src count result i ⦃ r =>
      r.val.map (fun a => bytes a.val) = (List.range count.val).map (chunkBytes N.val src.val) ⦄ := by
  unfold decode.decode_byte_array_vec_loop
  have hrl : result.length = i.val := by
    have := congrArg List.length hr; simp at this; simpa using this
  spec_split
  · step as ⟨ s, back, hs, hback ⟩
    step as ⟨ i1, hi1 ⟩
    · have : i.val * N.val ≤ count.val * N.val := Nat.mul_le_mul_right _ hi
      scalar_tac
    step as ⟨ i2, hi2 ⟩
    · have : (i.val + 1) * N.val ≤ count.val * N.val := Nat.mul_le_mul_right _ (by scalar_tac)
      rw [Nat.add_mul, Nat.one_mul] at this; scalar_tac
    step as ⟨ s1, hs1, hs1l ⟩
    · have : (i.val + 1) * N.val ≤ count.val * N.val := Nat.mul_le_mul_right _ (by scalar_tac)
      rw [Nat.add_mul, Nat.one_mul] at this
      scalar_tac
    step as ⟨ s2, hs2 ⟩
    · simp [Slice.length, hs, Array.repeat_val] at hs1l ⊢; scalar_tac
    step as ⟨ result1, hr1 ⟩
    step as ⟨ i3, hi3 ⟩
    have hlenN : s1.val.length = N.val := by simp [Slice.length] at hs1l; scalar_tac
    have hback8 : (back s2).val = s1.val := by
      rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlenN)
    have hxv : bytes (back s2).val = chunkBytes N.val src.val i.val := by
      rw [hback8, hs1, chunkBytes, List.slice, hi2, hi1, Nat.add_sub_cancel_left]
    apply decode_byte_array_vec_loop.spec src count result1 i3 hc (by scalar_tac)
    rw [hr1, List.map_append, hr, hi3, List.range_succ, List.map_append]
    simp [hxv]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [← this]; exact hr
termination_by count.val - i.val
decreasing_by scalar_decr_tac

theorem decode_byte_array_vec.spec (N : Std.Usize) (src : Slice Std.U8) (hN : 0 < N.val)
    (h : src.length % N.val = 0) :
    decode.decode_byte_array_vec N src ⦃ r =>
      match r with
      | .Ok v => v.val.map (fun a => bytes a.val) =
          (List.range (src.length / N.val)).map (chunkBytes N.val src.val)
      | .Err _ => False ⦄ := by
  unfold decode.decode_byte_array_vec
  have hlen := Slice.len_val src
  simp only [step_simps, core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_ok]
  have hm : (src.len.val % N.val == 0) = true := by simp [hlen, h]
  simp only [hm, ↓reduceIte]
  step as ⟨ count, hcount ⟩
  step with decode_byte_array_vec_loop.spec src count
    (alloc.vec.Vec.with_capacity (Array Std.U8 N) count) 0#usize
    (by rw [hcount, hlen]; exact Nat.div_mul_le_self _ _) (by simp)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨ r, hr ⟩
  rw [hr, hcount, hlen]

theorem ArrayU8N.encode_loop.spec {N : Std.Usize} (items : Slice (Array Std.U8 N))
    (buf : alloc.vec.Vec Std.U8) (i : Std.Usize) (hi : i.val ≤ items.length)
    (hb : buf.length + N.val * (items.length - i.val) ≤ Usize.max) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts ((items.val.drop i.val).map fun a => bytes a.val) ⦄ := by
  unfold ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · have hlt : i.val < items.length := by scalar_tac
    have hsplit : N.val * (items.length - i.val) = N.val * (items.length - (i.val + 1)) + N.val := by
      rw [show items.length - i.val = (items.length - (i.val + 1)) + 1 by omega, Nat.mul_succ]
    step as ⟨ a, ha ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    apply WP.spec_mono (ArrayU8N.encode_loop.spec items buf1 i2 (by scalar_tac)
      (by simp [hbuf1, Slice.from_val] at *; scalar_tac))
    intro buf' h
    rw [h, hbuf1, bytes_append, Slice.from_val, hi2, Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← ha]
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac
/-- **Decode `Vec<[u8; N]>`** (with `N > 0`). -/
theorem ArrayU8N.decode_list.spec (N : Std.Usize) (s : Slice Std.U8) (max : Std.Usize) (hN : 0 < N.val)
    (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max (ArrayU8N.Insts.LibsszDecodeSszDecode N) s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec (Array Std.U8 N) => .seq (v.val.map fun a => .bytes (bytes a.val))) r
        (deserialize (.list (.byteVector N.val) max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [ArrayU8N.Insts.LibsszDecodeSszDecode, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size,
    ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  have hd := deserialize_list_byteVector N.val max.val s.val hN (by simpa using hs)
  rw [hd]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · -- empty: both give the empty list
    have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h8 : ¬ (N = 0#usize) := by intro h; rw [h] at hN; simp at hN
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  by_cases hm : s.length % N.val = 0
  · have hm' : (s.len.val % N.val == 0) = true := by simp [hlen, hm]
    have hm'' : ¬ ((↑s : List Std.U8).length % N.val ≠ 0) := by simpa using hm
    simp only [hm', hm'', ↓reduceIte]
    step as ⟨ len, hl ⟩
    have hlv : len.val = (↑s : List Std.U8).length / N.val := by rw [hl, hlen]
    split
    · -- more elements than the limit
      rename_i hgt
      have hgt' : (↑s : List Std.U8).length / N.val > max.val := by rw [← hlv]; scalar_tac
      simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
      rw [← hlv]
      exact ErrMatch.overLimit max len
    · rename_i hle
      have hle' : ¬ ((↑s : List Std.U8).length / N.val > max.val) := by rw [← hlv]; scalar_tac
      simp only [hle', ↓reduceIte]
      unfold ArrayU8N.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
      step with decode_byte_array_vec.spec N s hN hm as ⟨ r, hr ⟩
      cases r with
      | Ok v =>
        simp only [Agrees]
        have := congrArg (List.map Value.bytes) hr
        simp only [List.map_map] at this
        congr 1
      | Err e => exact hr.elim
  · -- the length is not a multiple of N
    have hm' : (s.len.val % N.val == 0) = false := by simp [hlen, hm]
    have hm'' : (↑s : List Std.U8).length % N.val ≠ 0 := hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp only [ne_eq, show ((↑s : List Std.U8).length % N.val = 0) = False from eq_false hm'',
      not_false_eq_true, ↓reduceIte]
    simp only [Agrees]
    have := ErrMatch.undivided N s.len
    rw [hlen] at this
    exact this


/-- **Encode `Vec<[u8; N]>`.** -/
theorem ArrayU8N.encode_list.spec (N : Std.Usize) (v : alloc.vec.Vec (Array Std.U8 N))
    (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit) (hN32 : N.val < 2 ^ 32)
    (hsz : N.val * v.length < 2 ^ 32) (hb : buf.length + N.val * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append (ArrayU8N.Insts.LibsszEncodeSszEncode N) v buf
      ⦃ buf' => ∃ enc, serialize (.list (.byteVector N.val) limit)
          (.seq (v.val.map fun a => .bytes (bytes a.val))) = .ok enc ∧
          bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [ArrayU8N.Insts.LibsszEncodeSszEncode, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref]; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with ArrayU8N.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, ?_, hbuf'⟩
  have hd : ∀ d ∈ v.val.map (fun a => bytes a.val), d.size = N.val := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨a, _, rfl⟩ := hd
    simp
  have := serialize_list_byteVector N.val limit (v.val.map (fun a => bytes a.val)) hd hN32
    (by simpa using hl) (by simpa using hsz)
  simp only [List.map_map] at this
  convert this using 2 <;> simp [Function.comp_def, alloc.vec.Vec.deref]

/-- **`Vec<[u8; N]>::from_ssz_bytes`**: `decode_list_with_max` with no limit. -/
theorem ArrayU8N.vec_from_ssz_bytes.spec (N : Std.Usize) (s : Slice Std.U8) (hN : 0 < N.val)
    (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes (ArrayU8N.Insts.LibsszDecodeSszDecode N) s
      ⦃ r => Agrees (fun v : alloc.vec.Vec (Array Std.U8 N) => .seq (v.val.map fun a => .bytes (bytes a.val))) r
        (deserialize (.list (.byteVector N.val) core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact ArrayU8N.decode_list.spec N s _ hN hs

/-! ## `Vec<bool>`

Each element can fail: the loop invariant carries what has been decoded up to `i` and compares
the rest with EthLib's `deserializeEach .bool`. -/

theorem Bool.decode_loop.spec (src : Slice Std.U8) (count : Std.Usize)
    (result : alloc.vec.Vec Bool) (i : Std.Usize)
    (hc : count.val = src.length) (hi : i.val ≤ count.val) (hrl : result.length = i.val) :
    Bool.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop src count result i ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Bool => .seq (v.val.map .bool)) r
        ((fun vs => .seq (result.val.map .bool ++ vs)) <$>
          deserializeEach .bool ((src.val.drop i.val).map fun b => bytes [b])) ⦄ := by
  unfold Bool.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec_loop
  spec_split
  · have hlt : i.val < src.length := by scalar_tac
    step as ⟨ i1, hi1 ⟩
    step as ⟨ s, hs, hsl ⟩
    have hsv : s.val = [src.val[i.val]] := by
      rw [hs, List.slice, hi1, Nat.add_sub_cancel_left, List.take_one,
        List.drop_eq_getElem_cons hlt]
      rfl
    step with Libssz.Proofs.Bool.from_ssz_bytes.spec s as ⟨ r, hr ⟩
    rw [hsv] at hr
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, deserializeEach_cons]
    generalize hd : deserialize Desc.bool (bytes [src.val[i.val]]) = d at hr ⊢
    cases r with
    | Ok b =>
      cases d with
      | error e => exact hr.elim
      | ok v =>
        simp only [Agrees] at hr
        subst hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨ result1, hr1 ⟩
        apply WP.spec_mono (Bool.decode_loop.spec src count result1 i1 hc (by scalar_tac)
          (by simp [hr1, hrl]; scalar_tac))
        intro r' h'
        rw [hi1] at h'
        generalize deserializeEach Desc.bool
          (List.map (fun b => bytes [b]) (List.drop (i.val + 1) src.val)) = d2 at h' ⊢
        cases d2 with
        | error e => exact h'
        | ok ts =>
          simp only [hr1, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h'
          exact h'
    | Err e =>
      cases d with
      | ok v => exact hr.elim
      | error e' =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [bind_tc_ok, WP.spec_ok]
        exact hr
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [this, hc, List.drop_eq_nil_of_le (by simp), List.map_nil, deserializeEach_nil]
    simp [Agrees]
termination_by count.val - i.val
decreasing_by scalar_decr_tac

/-- **Decode `Vec<bool>`**: libssz and EthLib fail at the same byte, the first one that is
neither `0` nor `1`, with the same error. -/
theorem Bool.decode_list.spec (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max Bool.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec Bool => .seq (v.val.map .bool)) r
        (deserialize (.list .bool max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  simp only [Bool.Insts.LibsszDecodeSszDecode, Bool.Insts.LibsszDecodeSszDecode.is_fixed_size,
    Bool.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  rw [deserialize_list_bool max.val s.val (by simpa using hs)]
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · have hb' : b = true := by simpa [h0] using hb
    have h0' : (↑s : List Std.U8).length = 0 := h0
    simp only [hb', ↓reduceIte, WP.spec_ok, h0', Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  have h0' : (↑s : List Std.U8).length ≠ 0 := h0
  have h1 : ¬ (1#usize = 0#usize) := by decide
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h1, h0', core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok]
  have hm' : (s.len.val % (1#usize).val == 0) = true := by simp [Nat.mod_one]
  simp only [hm', ↓reduceIte]
  step as ⟨ len, hl ⟩
  have hlv : len.val = (↑s : List Std.U8).length := by rw [hl, hlen]; simp
  split
  · rename_i hgt
    have hgt' : (↑s : List Std.U8).length > max.val := by rw [← hlv]; scalar_tac
    simp only [WP.spec_ok, hgt', ↓reduceIte, Agrees]
    rw [← hlv]
    exact ErrMatch.overLimit max len
  · rename_i hle
    have hle' : ¬ ((↑s : List Std.U8).length > max.val) := by rw [← hlv]; scalar_tac
    simp only [hle', ↓reduceIte]
    unfold Bool.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
    simp only [step_simps]
    apply WP.spec_mono (Bool.decode_loop.spec s s.len (alloc.vec.Vec.with_capacity Bool s.len)
      0#usize hlen (by simp) (by simp [alloc.vec.Vec.with_capacity]))
    intro r h
    simpa [alloc.vec.Vec.with_capacity] using h

theorem Bool.ssz_append.bytes_spec (b : Bool) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length < Usize.max) :
    Bool.Insts.LibsszEncodeSszEncode.ssz_append b buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ boolByte b ⦄ := by
  unfold Bool.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [lift, bind_ok]
  step as ⟨ buf', hbuf' ⟩
  rw [hbuf', bytes_append]
  cases b <;> rfl

theorem Bool.encode_loop.spec (items : Slice Bool) (buf : alloc.vec.Vec Std.U8) (i : Std.Usize)
    (hi : i.val ≤ items.length) (hb : buf.length + (items.length - i.val) ≤ Usize.max) :
    Bool.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop items buf i ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ concatParts ((items.val.drop i.val).map boolByte) ⦄ := by
  unfold Bool.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice_loop
  simp only [step_simps]
  spec_split
  · have hlt : i.val < items.length := by scalar_tac
    step as ⟨ x, hx ⟩
    step with Bool.ssz_append.bytes_spec x buf (by scalar_tac) as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hl1 : buf1.length = buf.length + 1 := by
      have := congrArg Array.size hbuf1
      simp [boolByte] at this; simpa using this
    apply WP.spec_mono (Bool.encode_loop.spec items buf1 i2 (by scalar_tac) (by scalar_tac))
    intro buf' h
    rw [h, hbuf1, hi2, Array.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, concatParts, ← hx]
  · simp only [WP.spec_ok]
    have : i.val = items.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by items.length - i.val
decreasing_by scalar_decr_tac

/-- **Encode `Vec<bool>`.** -/
theorem Bool.encode_list.spec (v : alloc.vec.Vec Bool) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : v.length < 2 ^ 32)
    (hb : buf.length + v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append Bool.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list .bool limit) (.seq (v.val.map .bool)) = .ok enc ∧
          bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Bool.Insts.LibsszEncodeSszEncode, Bool.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold Bool.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps, alloc.vec.Vec.reserve, bind_ok]
  step with Bool.encode_loop.spec (alloc.vec.Vec.deref v) buf 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ buf', hbuf' ⟩
  refine ⟨_, serialize_list_bool limit v.val (by simpa using hl) (by simpa using hsz), ?_⟩
  rw [hbuf']
  simp [alloc.vec.Vec.deref]

/-- **`Vec<bool>::from_ssz_bytes`**: `decode_list_with_max` with no limit. -/
theorem Bool.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes Bool.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Bool => .seq (v.val.map .bool)) r
        (deserialize (.list .bool core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact Bool.decode_list.spec s _ hs

/-! ## Where libssz and EthLib diverge

EthLib rejects every input of 2³² bytes or more (`offsetOverflow`), even for a list of
fixed-size elements, where there are no offsets. libssz has no such check: for any slice of
2³² bytes or more, a multiple of 8 and within the limit, `decode_list_with_max::<u64>` decodes
the list and EthLib rejects it.

With a 32-bit `usize` no such long slice exists and the theorem holds trivially; with 64 bits
(the machines where an Ethereum client runs) it describes a real difference. That is why the
theorems above require `s.length < 2 ^ 32`. -/

/-- **Divergence.** See the section. -/
theorem U64.decode_list_diverges (s : Slice Std.U8) (max : Std.Usize) (hs : 2 ^ 32 ≤ s.length)
    (hm : s.length % 8 = 0) (hmax : s.length / 8 ≤ max.val) :
    decode.decode_list_with_max U64.Insts.LibsszDecodeSszDecode s max ⦃ r =>
      (∃ v, r = .Ok v) ∧
      deserialize (.list Desc.uint64 max.val) (bytes s.val) = .error (.offsetOverflow s.length) ⦄ := by
  have hd : deserialize (.list Desc.uint64 max.val) (bytes s.val) = .error (.offsetOverflow s.length) := by
    rw [deserialize]
    simp only [listSlices_eq, bytes_size]
    have : (↑s : List Std.U8).length ≥ 2 ^ (8 * bytesPerOffset) := by norm_num [bytesPerOffset]; exact hs
    simp only [this, ↓reduceIte]
    rfl
  unfold decode.decode_list_with_max
  simp only [U64.Insts.LibsszDecodeSszDecode, U64.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, step_simps]
  have hlen := Slice.len_val s
  step as ⟨ b, hb ⟩
  have h0 : ¬ s.length = 0 := by omega
  have hb' : b = false := by simpa [h0] using hb
  have h8 : ¬ (8#usize = 0#usize) := by decide
  have hm' : (s.len.val % (8#usize).val == 0) = true := by simp [hlen, hm]
  simp only [hb', Bool.false_eq_true, ↓reduceIte, h8, core.num.Usize.is_multiple_of,
    UScalar.is_multiple_of, bind_ok, hm']
  step as ⟨ len, hl ⟩
  have hle : ¬ (len > max) := by
    have : len.val = s.length / 8 := by rw [hl, hlen]
    scalar_tac
  simp only [hle, ↓reduceIte]
  step with U64.ssz_decode_fixed_vec.spec s hm as ⟨ r, hr ⟩
  cases r with
  | Ok v => exact ⟨⟨v, rfl⟩, hd⟩
  | Err e => exact hr.elim

end Libssz.Proofs
