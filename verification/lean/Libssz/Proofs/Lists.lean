module
public import Libssz.Proofs.Bridge
public import Libssz.Proofs.ListSpec
public import Libssz.Proofs.Bool
public import Libssz.Proofs.StdSpecs
import all Aeneas.Data.List.List
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
  `Ssz.serialize (.list (.uint N) limit)`, if the list is within the limit and takes fewer
  than 2³² bytes.
* `UN.vec_to_ssz.spec`: `Vec<uN>::to_ssz`, which does not go through `ssz_append`, returns
  those same bytes. For `u16`…`u128` it is different code (`UN.fixed_slice_to_vec.spec`); for
  `u8` it is the default `ssz_fixed_slice_to_vec`, which is `ssz_append` on an empty buffer
  (`vec_to_ssz_default`).

And the same for:
* `[u8; N]` against `byteVector N`: `ArrayU8N.from_ssz_bytes.spec`, `ArrayU8N.ssz_append.spec`
  and `ArrayU8N.ssz_write_fixed.spec`;
* `Vec<[u8; N]>` against lists of `byteVector N`, with `N > 0`: `ArrayU8N.decode_list.spec`,
  `ArrayU8N.vec_from_ssz_bytes.spec`, `ArrayU8N.encode_list.spec` and
  `ArrayU8N.vec_to_ssz.spec`;
* `Vec<bool>` against lists of `bool`: `Bool.decode_list.spec`, `Bool.vec_from_ssz_bytes.spec`,
  `Bool.encode_list.spec` and `Bool.vec_to_ssz.spec`. When decoding, each element can fail,
  and libssz and EthLib fail at the same byte with the same error.

Underneath, what in the pre-rewrite libssz was an `unsafe` `memcpy` is here:

* for `u16`…`u128`, when decoding: `as_chunks::<N>()` and a `map(uN::from_le_bytes)` over the
  chunks (`UN.from_le_chunks.spec`). There is no hand-written loop: the `map`/`collect` is
  reasoned about once, in `Iter.lean`;
* for `u16`…`u128`, when encoding: the `to_le_bytes` of each element go into a local block of
  `[[u8; N]]` of at most 8 KB, and from there into the buffer with a single
  `extend_from_slice` per block. There are two paths, depending on whether the list fits in
  one block (`UN.append_le_short.spec`, `UN.append_le_blocks.spec`); each loop has its
  invariant (`UN.short_loop.spec`, `UN.blocks_inner.spec`, `UN.blocks_outer.spec`,
  `UN.blocks_rest.spec`). `to_ssz` instead uses `map(to_le_bytes).collect().into_flattened()`
  (`UN.fixed_slice_to_vec.spec`);
* for `u8`, no loop at all: `to_vec` and `extend_from_slice`;
* for `[u8; N]`, none either: `as_chunks` and `as_flattened`.

The `core`/`alloc` functions we model by hand are in `StdModel.lean`, and what these proofs
use from those models, in `StdSpecs.lean`.

**Why the `< 2³²` hypothesis.** EthLib rejects any input of 2³² bytes or more
(`offsetOverflow`), also in lists of fixed-size elements; libssz has no such check. On a
64-bit machine they diverge there, and `U64.decode_list_diverges` (at the end) proves it.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz_codec
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## `u16` -/

/-- `u16::from_le_bytes`, as a number. -/
theorem U16.from_le_val (a : Array Std.U8 2#usize) :
    (core.num.U16.from_le_bytes a).val = leValue UScalar.val a.val := by
  have hx := core.num.U16.from_le_bytes.step_spec a
  simp only [lift, WP.spec_ok] at hx
  have : (core.num.U16.from_le_bytes a).val =
      (BitVec.fromLEBytes (List.map U8.bv a.val)).toNat := by
    simp [UScalar.val, hx]
  rw [this, toNat_fromLEBytes, leValue_map]
  rfl

/-- `u16::to_le_bytes`, as EthLib bytes. -/
theorem U16.bytes_to_le (x : Std.U16) :
    bytes (core.num.U16.to_le_bytes x).val = uintBytes 2 x.val := by
  have h := core.num.U16.to_le_bytes.step_spec x
  simp only [lift, WP.spec_ok] at h
  rw [h, bytes_toLEBytes 2 x.bv (by rfl)]
  rfl

/-- `chunks.iter().map(|c| u16::from_le_bytes(*c)).collect()`: a `map`. -/
theorem U16.from_le_chunks.spec (chunks : Slice (Array Std.U8 2#usize)) :
    decode.u16s_from_le_chunks chunks ⦃ r =>
      r.val = chunks.val.map core.num.U16.from_le_bytes ⦄ := by
  unfold decode.u16s_from_le_chunks
  simp only [core.slice.Slice.is_empty, bind_ok]
  by_cases h0 : chunks.length = 0
  · have hnil : chunks.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [h0, decide_true, ↓reduceIte, alloc.vec.Vec.into_boxed_slice,
      StdModel.into_boxed_slice, WP.spec_ok, hnil]
    rfl
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.map.default, StdModel.iter_map, bind_ok]
    step with collect_map_slice
      decode.u16s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU82U16
      core.num.U16.from_le_bytes ()
      (fun _ => by
        simp only [decode.u16s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU82U16.call_mut,
          lift, bind_ok])
      chunks as ⟨ items, hitems ⟩
    simp only [alloc.vec.Vec.into_boxed_slice, StdModel.into_boxed_slice, WP.spec_ok]
    exact hitems

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
  step with as_chunks_spec 2#usize s (by simp) as ⟨ chunks, remainder, hchunks, hremainder ⟩
  step with U16.from_le_chunks.spec chunks as ⟨ r, hr ⟩
  have hv : (alloc.slice.Slice.into_vec r).val = r.val := rfl
  have hf : ((fun x : Std.U16 => x.val) ∘ core.num.U16.from_le_bytes) =
      (leValue UScalar.val) ∘ (fun a : Array Std.U8 2#usize => a.val) := by
    funext a; exact U16.from_le_val a
  rw [hv, hr, List.map_map, hf, ← List.map_map, hchunks, List.map_map]
  rfl

/-- **Decode `Vec<u16>`** with a limit. -/
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

/-- **`Vec<U16>::from_ssz_bytes`**: it is `decode_list_with_max` without a limit (`usize::MAX`). -/
theorem U16.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U16.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U16 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint16 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U16.decode_list.spec s _ hs

/-- The loop that fills the output block: the first `k` are already the `to_le_bytes` of the
first `k` elements. -/
theorem U16.short_loop.spec (items : Slice Std.U16) (m : Std.Usize)
    (out : Slice (Array Std.U8 2#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U16.to_le_bytes) :
    encode.u16s_append_le_short_loop items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U16.to_le_bytes ⦄ := by
  unfold encode.u16s_append_le_short_loop
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U16.short_loop.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The short path** (up to one 8 KB block): everything is built in a local array and
appended with a single `extend_from_slice`. -/
theorem U16.append_le_short.spec (items : Slice Std.U16) (buf : alloc.vec.Vec Std.U8)
    (hn : items.length ≤ 4096) (hb : buf.length + 2 * items.length ≤ Usize.max) :
    encode.u16s_append_le_short items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 2 x.val) ⦄ := by
  unfold encode.u16s_append_le_short
  simp only [step_simps]
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U16.short_loop.spec items items.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = items.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append, hs, hout1, bytes_flatten, List.map_map]
    congr 3
    funext x; exact U16.bytes_to_le x
  · rename_i h0
    have hnil : items.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    simp [hnil, concatParts]

/-- The block size, in elements. -/
theorem U16.blocks_B : encode.u16s_append_le_blocks.B = ok 4096#usize := by
  unfold encode.u16s_append_le_blocks.B encode.BLOCK_BYTES
  rfl

/-- The inner loop: moves a whole block of 4096 elements into the local array. -/
theorem U16.blocks_inner.spec (tmp : Array (Array Std.U8 2#usize) 4096#usize)
    (block : Array Std.U16 4096#usize) (k : Std.Usize) (hk : k.val ≤ 4096)
    (hpre : tmp.val.take k.val = (block.val.take k.val).map core.num.U16.to_le_bytes) :
    encode.u16s_append_le_blocks_loop0_loop0 tmp block k ⦃ tmp' =>
      tmp'.val = block.val.map core.num.U16.to_le_bytes ⦄ := by
  unfold encode.u16s_append_le_blocks_loop0_loop0
  simp only [U16.blocks_B, bind_ok]
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ tmp1, htmp1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U16.blocks_inner.spec tmp1 block k1 (by scalar_tac)
    have hlt : k.val < block.val.length := by scalar_tac
    rw [htmp1, Array.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = 4096 := by scalar_tac
    have h1 : tmp.val.take k.val = tmp.val := by
      apply List.take_of_length_le; simp [hkm]
    have h2 : block.val.take k.val = block.val := by
      apply List.take_of_length_le; simp [hkm]
    rw [h1, h2] at hpre
    exact hpre
termination_by 4096 - k.val
decreasing_by scalar_decr_tac

/-- The outer loop: one 8 KB `extend_from_slice` per block. -/
theorem U16.blocks_outer.spec (buf : alloc.vec.Vec Std.U8)
    (blocks : Slice (Array Std.U16 4096#usize)) (tmp : Array (Array Std.U8 2#usize) 4096#usize)
    (i : Std.Usize) (hi : i.val ≤ blocks.length)
    (hb : buf.length + 8192 * (blocks.length - i.val) ≤ Usize.max) :
    encode.u16s_append_le_blocks_loop0 buf blocks tmp i ⦃ buf' _tmp' =>
      bytes buf'.val = bytes buf.val ++ concatParts
        ((((blocks.val.drop i.val).map (·.val)).flatten).map fun x => uintBytes 2 x.val) ∧
      buf'.length = buf.length + 8192 * (blocks.length - i.val) ⦄ := by
  unfold encode.u16s_append_le_blocks_loop0
  simp only [step_simps]
  spec_split
  · have hlt : i.val < blocks.length := by scalar_tac
    step as ⟨ block, hblock ⟩
    step with U16.blocks_inner.spec tmp block 0#usize (by simp) (by simp) as ⟨ tmp1, htmp1 ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hs1b : bytes s1.val = concatParts (block.val.map fun x => uintBytes 2 x.val) := by
      rw [hs1, Slice.from_val, htmp1, bytes_flatten, List.map_map]
      congr 2
      funext x; exact U16.bytes_to_le x
    have hs1l' : s1.val.length = 8192 := by
      have : s1.length = 2 * 4096 := by rw [hs1l]; simp [Slice.length]
      simpa [Slice.length] using this
    have hb1 : buf1.length + 8192 * (blocks.length - i2.val) ≤ Usize.max := by
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      simp only [alloc.vec.Vec.length] at hb
      omega
    apply WP.spec_mono (U16.blocks_outer.spec buf1 blocks tmp1 i2 (by scalar_tac) hb1)
    intro ⟨buf', tmp'⟩ h
    simp only [WP.uncurry'_pair] at h ⊢
    obtain ⟨h, hl'⟩ := h
    constructor
    · rw [h, hbuf1, bytes_append, hs1b, hi2, Array.append_assoc, ← concatParts_append,
        ← List.map_append]
      congr 3
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.flatten_cons, hblock]
    · rw [hl']
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      omega
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    have him : i.val = blocks.length := by scalar_tac
    rw [him, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by blocks.length - i.val
decreasing_by scalar_decr_tac

/-- The remainder loop (what does not fill a whole block): same as the short path's. -/
theorem U16.blocks_rest.spec (items : Slice Std.U16) (m : Std.Usize)
    (out : Slice (Array Std.U8 2#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U16.to_le_bytes) :
    encode.u16s_append_le_blocks_loop1 items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U16.to_le_bytes ⦄ := by
  unfold encode.u16s_append_le_blocks_loop1
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U16.blocks_rest.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The long path**: whole 8 KB blocks, and then the remainder. -/
theorem U16.append_le_blocks.spec (items : Slice Std.U16) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 2 * items.length ≤ Usize.max) :
    encode.u16s_append_le_blocks items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 2 x.val) ⦄ := by
  unfold encode.u16s_append_le_blocks
  simp only [step_simps]
  step as ⟨ n8, hn8 ⟩
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with as_chunks_spec 4096#usize items (by simp) as ⟨ blocks, rest, hblocks, hrest ⟩
  have hbl : blocks.length = items.length / 4096 := by
    have := congrArg List.length hblocks
    simpa [Slice.length] using this
  have hflat : (blocks.val.map (·.val)).flatten = items.val.take (items.length / 4096 * 4096) := by
    rw [hblocks]; exact flatten_chunks 4096 items.val _
  have hsplit : items.val = (blocks.val.map (·.val)).flatten ++ rest.val := by
    rw [hflat, hrest, List.take_append_drop]
  have hrl : rest.length = items.length % 4096 := by
    have := congrArg List.length hrest
    simp only [List.length_drop] at this
    simp only [Slice.length] at this ⊢
    omega
  step with U16.blocks_outer.spec buf blocks _ 0#usize (by simp)
    (by have h0 : (0#usize).val = 0 := rfl
        rw [hbl, h0]; simp only [alloc.vec.Vec.length, Slice.length] at hb ⊢; omega)
    as ⟨ buf2, tmp1, hbuf2, hbuf2l ⟩
  rw [List.drop_zero] at hbuf2
  clear hrest hflat hblocks
  have hfin : ∀ tail : Bytes,
      tail = concatParts (rest.val.map fun x => uintBytes 2 x.val) →
      bytes buf2.val ++ tail = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 2 x.val) := by
    intro tail ht
    rw [hbuf2, ht, Array.append_assoc, ← concatParts_append, ← List.map_append, ← hsplit]
  have hrlt : rest.length < 4096 := by rw [hrl]; exact Nat.mod_lt _ (by norm_num)
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U16.blocks_rest.spec rest rest.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = rest.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append]
    apply hfin
    rw [hs, hout1, bytes_flatten, List.map_map]
    congr 2
    funext x; exact U16.bytes_to_le x
  · have hnil : rest.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      clear hfin hsplit hbuf2 hbuf2l
      scalar_tac
    simp only [WP.spec_ok]
    have := hfin #[] (by rw [hnil]; rfl)
    rw [Array.append_empty] at this
    exact this

/-- `<u16 as SszEncode>::ssz_append_fixed_slice`: chooses the path according to the length. -/
theorem U16.append_fixed_slice.spec (items : Slice Std.U16) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 2 * items.length ≤ Usize.max) :
    U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 2 x.val) ⦄ := by
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  have hB : encode.BLOCK_BYTES / 2#usize = ok 4096#usize := by
    unfold encode.BLOCK_BYTES; rfl
  simp only [step_simps, hB, bind_ok]
  spec_split
  · exact U16.append_le_short.spec items buf (by scalar_tac) hb
  · exact U16.append_le_blocks.spec items buf hb

/-- What `Ssz.serialize` gives on a list of `u16`. -/
theorem U16.serialize_list (l : List Std.U16) (limit : Nat) (hl : l.length ≤ limit)
    (hsz : 2 * l.length < 2 ^ 32) :
    serialize (.list Desc.uint16 limit) (.seq (l.map fun x => .uint x.val)) =
      .ok (concatParts (l.map fun x => uintBytes 2 x.val)) := by
  have hfit : ∀ n ∈ l.map (·.val), n < 2 ^ (8 * 2) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 2 limit (l.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint16 = .uint 2 from rfl]
  convert this using 2 <;> rfl

theorem U16.encode_list.spec (v : alloc.vec.Vec Std.U16) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 2 * v.length < 2 ^ 32)
    (hb : buf.length + 2 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U16.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint16 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U16.Insts.LibsszEncodeSszEncode, U16.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U16.append_fixed_slice.spec (alloc.vec.Vec.deref v) buf
    (by simpa [alloc.vec.Vec.deref] using hb) as ⟨ buf', hbuf' ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hbuf'
  exact ⟨_, U16.serialize_list v.val limit hl hsz, hbuf'⟩

/-- `<u16 as SszEncode>::ssz_fixed_slice_to_vec`:
`items.iter().map(|x| x.to_le_bytes()).collect::<Vec<_>>().into_flattened()`. -/
theorem U16.fixed_slice_to_vec.spec (items : Slice Std.U16)
    (hsz : 2 * items.length ≤ Usize.max) :
    U16.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun x => uintBytes 2 x.val) ⦄ := by
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.map.default,
    StdModel.iter_map, bind_ok]
  step with collect_map_slice
    encode.SszEncodeU16.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U16ArrayU82
    core.num.U16.to_le_bytes ()
    (fun _ => by
      simp only [encode.SszEncodeU16.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U16ArrayU82.call_mut,
        lift, bind_ok])
    items as ⟨ v, hv ⟩
  have hvl : v.length = items.length := by simp [hv]
  step as ⟨ out, hout ⟩
  rw [hout, hv, bytes_flatten, List.map_map]
  congr 2
  funext x; exact U16.bytes_to_le x

/-- **`Vec<u16>::to_ssz`**: does not go through `ssz_append`; it builds the output `Vec`
directly. It gives the same bytes. -/
theorem U16.vec_to_ssz.spec (v : alloc.vec.Vec Std.U16) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : 2 * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz U16.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list Desc.uint16 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes out.val = enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz
  simp only [U16.Insts.LibsszEncodeSszEncode, U16.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U16.fixed_slice_to_vec.spec (alloc.vec.Vec.deref v)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ out, hout ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hout
  rw [hout]
  exact U16.serialize_list v.val limit hl hsz

/-! ## `u32` -/

/-- `u32::from_le_bytes`, as a number. -/
theorem U32.from_le_val (a : Array Std.U8 4#usize) :
    (core.num.U32.from_le_bytes a).val = leValue UScalar.val a.val := by
  have hx := core.num.U32.from_le_bytes.step_spec a
  simp only [lift, WP.spec_ok] at hx
  have : (core.num.U32.from_le_bytes a).val =
      (BitVec.fromLEBytes (List.map U8.bv a.val)).toNat := by
    simp [UScalar.val, hx]
  rw [this, toNat_fromLEBytes, leValue_map]
  rfl

/-- `u32::to_le_bytes`, as EthLib bytes. -/
theorem U32.bytes_to_le (x : Std.U32) :
    bytes (core.num.U32.to_le_bytes x).val = uintBytes 4 x.val := by
  have h := core.num.U32.to_le_bytes.step_spec x
  simp only [lift, WP.spec_ok] at h
  rw [h, bytes_toLEBytes 4 x.bv (by rfl)]
  rfl

/-- `chunks.iter().map(|c| u32::from_le_bytes(*c)).collect()`: a `map`. -/
theorem U32.from_le_chunks.spec (chunks : Slice (Array Std.U8 4#usize)) :
    decode.u32s_from_le_chunks chunks ⦃ r =>
      r.val = chunks.val.map core.num.U32.from_le_bytes ⦄ := by
  unfold decode.u32s_from_le_chunks
  simp only [core.slice.Slice.is_empty, bind_ok]
  by_cases h0 : chunks.length = 0
  · have hnil : chunks.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [h0, decide_true, ↓reduceIte, alloc.vec.Vec.into_boxed_slice,
      StdModel.into_boxed_slice, WP.spec_ok, hnil]
    rfl
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.map.default, StdModel.iter_map, bind_ok]
    step with collect_map_slice
      decode.u32s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU84U32
      core.num.U32.from_le_bytes ()
      (fun _ => by
        simp only [decode.u32s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU84U32.call_mut,
          lift, bind_ok])
      chunks as ⟨ items, hitems ⟩
    simp only [alloc.vec.Vec.into_boxed_slice, StdModel.into_boxed_slice, WP.spec_ok]
    exact hitems

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
  step with as_chunks_spec 4#usize s (by simp) as ⟨ chunks, remainder, hchunks, hremainder ⟩
  step with U32.from_le_chunks.spec chunks as ⟨ r, hr ⟩
  have hv : (alloc.slice.Slice.into_vec r).val = r.val := rfl
  have hf : ((fun x : Std.U32 => x.val) ∘ core.num.U32.from_le_bytes) =
      (leValue UScalar.val) ∘ (fun a : Array Std.U8 4#usize => a.val) := by
    funext a; exact U32.from_le_val a
  rw [hv, hr, List.map_map, hf, ← List.map_map, hchunks, List.map_map]
  rfl

/-- **Decode `Vec<u32>`** with a limit. -/
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

/-- **`Vec<U32>::from_ssz_bytes`**: it is `decode_list_with_max` without a limit (`usize::MAX`). -/
theorem U32.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U32.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U32 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint32 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U32.decode_list.spec s _ hs

/-- The loop that fills the output block: the first `k` are already the `to_le_bytes` of the
first `k` elements. -/
theorem U32.short_loop.spec (items : Slice Std.U32) (m : Std.Usize)
    (out : Slice (Array Std.U8 4#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U32.to_le_bytes) :
    encode.u32s_append_le_short_loop items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U32.to_le_bytes ⦄ := by
  unfold encode.u32s_append_le_short_loop
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U32.short_loop.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The short path** (up to one 8 KB block): everything is built in a local array and
appended with a single `extend_from_slice`. -/
theorem U32.append_le_short.spec (items : Slice Std.U32) (buf : alloc.vec.Vec Std.U8)
    (hn : items.length ≤ 2048) (hb : buf.length + 4 * items.length ≤ Usize.max) :
    encode.u32s_append_le_short items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 4 x.val) ⦄ := by
  unfold encode.u32s_append_le_short
  simp only [step_simps]
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U32.short_loop.spec items items.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = items.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append, hs, hout1, bytes_flatten, List.map_map]
    congr 3
    funext x; exact U32.bytes_to_le x
  · rename_i h0
    have hnil : items.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    simp [hnil, concatParts]

/-- The block size, in elements. -/
theorem U32.blocks_B : encode.u32s_append_le_blocks.B = ok 2048#usize := by
  unfold encode.u32s_append_le_blocks.B encode.BLOCK_BYTES
  rfl

/-- The inner loop: moves a whole block of 2048 elements into the local array. -/
theorem U32.blocks_inner.spec (tmp : Array (Array Std.U8 4#usize) 2048#usize)
    (block : Array Std.U32 2048#usize) (k : Std.Usize) (hk : k.val ≤ 2048)
    (hpre : tmp.val.take k.val = (block.val.take k.val).map core.num.U32.to_le_bytes) :
    encode.u32s_append_le_blocks_loop0_loop0 tmp block k ⦃ tmp' =>
      tmp'.val = block.val.map core.num.U32.to_le_bytes ⦄ := by
  unfold encode.u32s_append_le_blocks_loop0_loop0
  simp only [U32.blocks_B, bind_ok]
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ tmp1, htmp1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U32.blocks_inner.spec tmp1 block k1 (by scalar_tac)
    have hlt : k.val < block.val.length := by scalar_tac
    rw [htmp1, Array.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = 2048 := by scalar_tac
    have h1 : tmp.val.take k.val = tmp.val := by
      apply List.take_of_length_le; simp [hkm]
    have h2 : block.val.take k.val = block.val := by
      apply List.take_of_length_le; simp [hkm]
    rw [h1, h2] at hpre
    exact hpre
termination_by 2048 - k.val
decreasing_by scalar_decr_tac

/-- The outer loop: one 8 KB `extend_from_slice` per block. -/
theorem U32.blocks_outer.spec (buf : alloc.vec.Vec Std.U8)
    (blocks : Slice (Array Std.U32 2048#usize)) (tmp : Array (Array Std.U8 4#usize) 2048#usize)
    (i : Std.Usize) (hi : i.val ≤ blocks.length)
    (hb : buf.length + 8192 * (blocks.length - i.val) ≤ Usize.max) :
    encode.u32s_append_le_blocks_loop0 buf blocks tmp i ⦃ buf' _tmp' =>
      bytes buf'.val = bytes buf.val ++ concatParts
        ((((blocks.val.drop i.val).map (·.val)).flatten).map fun x => uintBytes 4 x.val) ∧
      buf'.length = buf.length + 8192 * (blocks.length - i.val) ⦄ := by
  unfold encode.u32s_append_le_blocks_loop0
  simp only [step_simps]
  spec_split
  · have hlt : i.val < blocks.length := by scalar_tac
    step as ⟨ block, hblock ⟩
    step with U32.blocks_inner.spec tmp block 0#usize (by simp) (by simp) as ⟨ tmp1, htmp1 ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hs1b : bytes s1.val = concatParts (block.val.map fun x => uintBytes 4 x.val) := by
      rw [hs1, Slice.from_val, htmp1, bytes_flatten, List.map_map]
      congr 2
      funext x; exact U32.bytes_to_le x
    have hs1l' : s1.val.length = 8192 := by
      have : s1.length = 4 * 2048 := by rw [hs1l]; simp [Slice.length]
      simpa [Slice.length] using this
    have hb1 : buf1.length + 8192 * (blocks.length - i2.val) ≤ Usize.max := by
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      simp only [alloc.vec.Vec.length] at hb
      omega
    apply WP.spec_mono (U32.blocks_outer.spec buf1 blocks tmp1 i2 (by scalar_tac) hb1)
    intro ⟨buf', tmp'⟩ h
    simp only [WP.uncurry'_pair] at h ⊢
    obtain ⟨h, hl'⟩ := h
    constructor
    · rw [h, hbuf1, bytes_append, hs1b, hi2, Array.append_assoc, ← concatParts_append,
        ← List.map_append]
      congr 3
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.flatten_cons, hblock]
    · rw [hl']
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      omega
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    have him : i.val = blocks.length := by scalar_tac
    rw [him, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by blocks.length - i.val
decreasing_by scalar_decr_tac

/-- The remainder loop (what does not fill a whole block): same as the short path's. -/
theorem U32.blocks_rest.spec (items : Slice Std.U32) (m : Std.Usize)
    (out : Slice (Array Std.U8 4#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U32.to_le_bytes) :
    encode.u32s_append_le_blocks_loop1 items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U32.to_le_bytes ⦄ := by
  unfold encode.u32s_append_le_blocks_loop1
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U32.blocks_rest.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The long path**: whole 8 KB blocks, and then the remainder. -/
theorem U32.append_le_blocks.spec (items : Slice Std.U32) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 4 * items.length ≤ Usize.max) :
    encode.u32s_append_le_blocks items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 4 x.val) ⦄ := by
  unfold encode.u32s_append_le_blocks
  simp only [step_simps]
  step as ⟨ n8, hn8 ⟩
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with as_chunks_spec 2048#usize items (by simp) as ⟨ blocks, rest, hblocks, hrest ⟩
  have hbl : blocks.length = items.length / 2048 := by
    have := congrArg List.length hblocks
    simpa [Slice.length] using this
  have hflat : (blocks.val.map (·.val)).flatten = items.val.take (items.length / 2048 * 2048) := by
    rw [hblocks]; exact flatten_chunks 2048 items.val _
  have hsplit : items.val = (blocks.val.map (·.val)).flatten ++ rest.val := by
    rw [hflat, hrest, List.take_append_drop]
  have hrl : rest.length = items.length % 2048 := by
    have := congrArg List.length hrest
    simp only [List.length_drop] at this
    simp only [Slice.length] at this ⊢
    omega
  step with U32.blocks_outer.spec buf blocks _ 0#usize (by simp)
    (by have h0 : (0#usize).val = 0 := rfl
        rw [hbl, h0]; simp only [alloc.vec.Vec.length, Slice.length] at hb ⊢; omega)
    as ⟨ buf2, tmp1, hbuf2, hbuf2l ⟩
  rw [List.drop_zero] at hbuf2
  clear hrest hflat hblocks
  have hfin : ∀ tail : Bytes,
      tail = concatParts (rest.val.map fun x => uintBytes 4 x.val) →
      bytes buf2.val ++ tail = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 4 x.val) := by
    intro tail ht
    rw [hbuf2, ht, Array.append_assoc, ← concatParts_append, ← List.map_append, ← hsplit]
  have hrlt : rest.length < 2048 := by rw [hrl]; exact Nat.mod_lt _ (by norm_num)
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U32.blocks_rest.spec rest rest.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = rest.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append]
    apply hfin
    rw [hs, hout1, bytes_flatten, List.map_map]
    congr 2
    funext x; exact U32.bytes_to_le x
  · have hnil : rest.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      clear hfin hsplit hbuf2 hbuf2l
      scalar_tac
    simp only [WP.spec_ok]
    have := hfin #[] (by rw [hnil]; rfl)
    rw [Array.append_empty] at this
    exact this

/-- `<u32 as SszEncode>::ssz_append_fixed_slice`: chooses the path according to the length. -/
theorem U32.append_fixed_slice.spec (items : Slice Std.U32) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 4 * items.length ≤ Usize.max) :
    U32.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 4 x.val) ⦄ := by
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  have hB : encode.BLOCK_BYTES / 4#usize = ok 2048#usize := by
    unfold encode.BLOCK_BYTES; rfl
  simp only [step_simps, hB, bind_ok]
  spec_split
  · exact U32.append_le_short.spec items buf (by scalar_tac) hb
  · exact U32.append_le_blocks.spec items buf hb

/-- What `Ssz.serialize` gives on a list of `u32`. -/
theorem U32.serialize_list (l : List Std.U32) (limit : Nat) (hl : l.length ≤ limit)
    (hsz : 4 * l.length < 2 ^ 32) :
    serialize (.list Desc.uint32 limit) (.seq (l.map fun x => .uint x.val)) =
      .ok (concatParts (l.map fun x => uintBytes 4 x.val)) := by
  have hfit : ∀ n ∈ l.map (·.val), n < 2 ^ (8 * 4) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 4 limit (l.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint32 = .uint 4 from rfl]
  convert this using 2 <;> rfl

theorem U32.encode_list.spec (v : alloc.vec.Vec Std.U32) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 4 * v.length < 2 ^ 32)
    (hb : buf.length + 4 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U32.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint32 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U32.Insts.LibsszEncodeSszEncode, U32.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U32.append_fixed_slice.spec (alloc.vec.Vec.deref v) buf
    (by simpa [alloc.vec.Vec.deref] using hb) as ⟨ buf', hbuf' ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hbuf'
  exact ⟨_, U32.serialize_list v.val limit hl hsz, hbuf'⟩

/-- `<u32 as SszEncode>::ssz_fixed_slice_to_vec`:
`items.iter().map(|x| x.to_le_bytes()).collect::<Vec<_>>().into_flattened()`. -/
theorem U32.fixed_slice_to_vec.spec (items : Slice Std.U32)
    (hsz : 4 * items.length ≤ Usize.max) :
    U32.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun x => uintBytes 4 x.val) ⦄ := by
  unfold U32.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.map.default,
    StdModel.iter_map, bind_ok]
  step with collect_map_slice
    encode.SszEncodeU32.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U32ArrayU84
    core.num.U32.to_le_bytes ()
    (fun _ => by
      simp only [encode.SszEncodeU32.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U32ArrayU84.call_mut,
        lift, bind_ok])
    items as ⟨ v, hv ⟩
  have hvl : v.length = items.length := by simp [hv]
  step as ⟨ out, hout ⟩
  rw [hout, hv, bytes_flatten, List.map_map]
  congr 2
  funext x; exact U32.bytes_to_le x

/-- **`Vec<u32>::to_ssz`**: does not go through `ssz_append`; it builds the output `Vec`
directly. It gives the same bytes. -/
theorem U32.vec_to_ssz.spec (v : alloc.vec.Vec Std.U32) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : 4 * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz U32.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list Desc.uint32 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes out.val = enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz
  simp only [U32.Insts.LibsszEncodeSszEncode, U32.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U32.fixed_slice_to_vec.spec (alloc.vec.Vec.deref v)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ out, hout ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hout
  rw [hout]
  exact U32.serialize_list v.val limit hl hsz

/-! ## `u64` -/

/-- `u64::from_le_bytes`, as a number. -/
theorem U64.from_le_val (a : Array Std.U8 8#usize) :
    (core.num.U64.from_le_bytes a).val = leValue UScalar.val a.val := by
  have hx := core.num.U64.from_le_bytes.step_spec a
  simp only [lift, WP.spec_ok] at hx
  have : (core.num.U64.from_le_bytes a).val =
      (BitVec.fromLEBytes (List.map U8.bv a.val)).toNat := by
    simp [UScalar.val, hx]
  rw [this, toNat_fromLEBytes, leValue_map]
  rfl

/-- `u64::to_le_bytes`, as EthLib bytes. -/
theorem U64.bytes_to_le (x : Std.U64) :
    bytes (core.num.U64.to_le_bytes x).val = uintBytes 8 x.val := by
  have h := core.num.U64.to_le_bytes.step_spec x
  simp only [lift, WP.spec_ok] at h
  rw [h, bytes_toLEBytes 8 x.bv (by rfl)]
  rfl

/-- `chunks.iter().map(|c| u64::from_le_bytes(*c)).collect()`: a `map`. -/
theorem U64.from_le_chunks.spec (chunks : Slice (Array Std.U8 8#usize)) :
    decode.u64s_from_le_chunks chunks ⦃ r =>
      r.val = chunks.val.map core.num.U64.from_le_bytes ⦄ := by
  unfold decode.u64s_from_le_chunks
  simp only [core.slice.Slice.is_empty, bind_ok]
  by_cases h0 : chunks.length = 0
  · have hnil : chunks.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [h0, decide_true, ↓reduceIte, alloc.vec.Vec.into_boxed_slice,
      StdModel.into_boxed_slice, WP.spec_ok, hnil]
    rfl
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.map.default, StdModel.iter_map, bind_ok]
    step with collect_map_slice
      decode.u64s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU88U64
      core.num.U64.from_le_bytes ()
      (fun _ => by
        simp only [decode.u64s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU88U64.call_mut,
          lift, bind_ok])
      chunks as ⟨ items, hitems ⟩
    simp only [alloc.vec.Vec.into_boxed_slice, StdModel.into_boxed_slice, WP.spec_ok]
    exact hitems

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
  step with as_chunks_spec 8#usize s (by simp) as ⟨ chunks, remainder, hchunks, hremainder ⟩
  step with U64.from_le_chunks.spec chunks as ⟨ r, hr ⟩
  have hv : (alloc.slice.Slice.into_vec r).val = r.val := rfl
  have hf : ((fun x : Std.U64 => x.val) ∘ core.num.U64.from_le_bytes) =
      (leValue UScalar.val) ∘ (fun a : Array Std.U8 8#usize => a.val) := by
    funext a; exact U64.from_le_val a
  rw [hv, hr, List.map_map, hf, ← List.map_map, hchunks, List.map_map]
  rfl

/-- **Decode `Vec<u64>`** with a limit. -/
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

/-- **`Vec<U64>::from_ssz_bytes`**: it is `decode_list_with_max` without a limit (`usize::MAX`). -/
theorem U64.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U64.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U64 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint64 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U64.decode_list.spec s _ hs

/-- The loop that fills the output block: the first `k` are already the `to_le_bytes` of the
first `k` elements. -/
theorem U64.short_loop.spec (items : Slice Std.U64) (m : Std.Usize)
    (out : Slice (Array Std.U8 8#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U64.to_le_bytes) :
    encode.u64s_append_le_short_loop items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U64.to_le_bytes ⦄ := by
  unfold encode.u64s_append_le_short_loop
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U64.short_loop.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The short path** (up to one 8 KB block): everything is built in a local array and
appended with a single `extend_from_slice`. -/
theorem U64.append_le_short.spec (items : Slice Std.U64) (buf : alloc.vec.Vec Std.U8)
    (hn : items.length ≤ 1024) (hb : buf.length + 8 * items.length ≤ Usize.max) :
    encode.u64s_append_le_short items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 8 x.val) ⦄ := by
  unfold encode.u64s_append_le_short
  simp only [step_simps]
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U64.short_loop.spec items items.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = items.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append, hs, hout1, bytes_flatten, List.map_map]
    congr 3
    funext x; exact U64.bytes_to_le x
  · rename_i h0
    have hnil : items.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    simp [hnil, concatParts]

/-- The block size, in elements. -/
theorem U64.blocks_B : encode.u64s_append_le_blocks.B = ok 1024#usize := by
  unfold encode.u64s_append_le_blocks.B encode.BLOCK_BYTES
  rfl

/-- The inner loop: moves a whole block of 1024 elements into the local array. -/
theorem U64.blocks_inner.spec (tmp : Array (Array Std.U8 8#usize) 1024#usize)
    (block : Array Std.U64 1024#usize) (k : Std.Usize) (hk : k.val ≤ 1024)
    (hpre : tmp.val.take k.val = (block.val.take k.val).map core.num.U64.to_le_bytes) :
    encode.u64s_append_le_blocks_loop0_loop0 tmp block k ⦃ tmp' =>
      tmp'.val = block.val.map core.num.U64.to_le_bytes ⦄ := by
  unfold encode.u64s_append_le_blocks_loop0_loop0
  simp only [U64.blocks_B, bind_ok]
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ tmp1, htmp1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U64.blocks_inner.spec tmp1 block k1 (by scalar_tac)
    have hlt : k.val < block.val.length := by scalar_tac
    rw [htmp1, Array.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = 1024 := by scalar_tac
    have h1 : tmp.val.take k.val = tmp.val := by
      apply List.take_of_length_le; simp [hkm]
    have h2 : block.val.take k.val = block.val := by
      apply List.take_of_length_le; simp [hkm]
    rw [h1, h2] at hpre
    exact hpre
termination_by 1024 - k.val
decreasing_by scalar_decr_tac

/-- The outer loop: one 8 KB `extend_from_slice` per block. -/
theorem U64.blocks_outer.spec (buf : alloc.vec.Vec Std.U8)
    (blocks : Slice (Array Std.U64 1024#usize)) (tmp : Array (Array Std.U8 8#usize) 1024#usize)
    (i : Std.Usize) (hi : i.val ≤ blocks.length)
    (hb : buf.length + 8192 * (blocks.length - i.val) ≤ Usize.max) :
    encode.u64s_append_le_blocks_loop0 buf blocks tmp i ⦃ buf' _tmp' =>
      bytes buf'.val = bytes buf.val ++ concatParts
        ((((blocks.val.drop i.val).map (·.val)).flatten).map fun x => uintBytes 8 x.val) ∧
      buf'.length = buf.length + 8192 * (blocks.length - i.val) ⦄ := by
  unfold encode.u64s_append_le_blocks_loop0
  simp only [step_simps]
  spec_split
  · have hlt : i.val < blocks.length := by scalar_tac
    step as ⟨ block, hblock ⟩
    step with U64.blocks_inner.spec tmp block 0#usize (by simp) (by simp) as ⟨ tmp1, htmp1 ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hs1b : bytes s1.val = concatParts (block.val.map fun x => uintBytes 8 x.val) := by
      rw [hs1, Slice.from_val, htmp1, bytes_flatten, List.map_map]
      congr 2
      funext x; exact U64.bytes_to_le x
    have hs1l' : s1.val.length = 8192 := by
      have : s1.length = 8 * 1024 := by rw [hs1l]; simp [Slice.length]
      simpa [Slice.length] using this
    have hb1 : buf1.length + 8192 * (blocks.length - i2.val) ≤ Usize.max := by
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      simp only [alloc.vec.Vec.length] at hb
      omega
    apply WP.spec_mono (U64.blocks_outer.spec buf1 blocks tmp1 i2 (by scalar_tac) hb1)
    intro ⟨buf', tmp'⟩ h
    simp only [WP.uncurry'_pair] at h ⊢
    obtain ⟨h, hl'⟩ := h
    constructor
    · rw [h, hbuf1, bytes_append, hs1b, hi2, Array.append_assoc, ← concatParts_append,
        ← List.map_append]
      congr 3
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.flatten_cons, hblock]
    · rw [hl']
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      omega
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    have him : i.val = blocks.length := by scalar_tac
    rw [him, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by blocks.length - i.val
decreasing_by scalar_decr_tac

/-- The remainder loop (what does not fill a whole block): same as the short path's. -/
theorem U64.blocks_rest.spec (items : Slice Std.U64) (m : Std.Usize)
    (out : Slice (Array Std.U8 8#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U64.to_le_bytes) :
    encode.u64s_append_le_blocks_loop1 items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U64.to_le_bytes ⦄ := by
  unfold encode.u64s_append_le_blocks_loop1
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U64.blocks_rest.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The long path**: whole 8 KB blocks, and then the remainder. -/
theorem U64.append_le_blocks.spec (items : Slice Std.U64) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 8 * items.length ≤ Usize.max) :
    encode.u64s_append_le_blocks items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 8 x.val) ⦄ := by
  unfold encode.u64s_append_le_blocks
  simp only [step_simps]
  step as ⟨ n8, hn8 ⟩
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with as_chunks_spec 1024#usize items (by simp) as ⟨ blocks, rest, hblocks, hrest ⟩
  have hbl : blocks.length = items.length / 1024 := by
    have := congrArg List.length hblocks
    simpa [Slice.length] using this
  have hflat : (blocks.val.map (·.val)).flatten = items.val.take (items.length / 1024 * 1024) := by
    rw [hblocks]; exact flatten_chunks 1024 items.val _
  have hsplit : items.val = (blocks.val.map (·.val)).flatten ++ rest.val := by
    rw [hflat, hrest, List.take_append_drop]
  have hrl : rest.length = items.length % 1024 := by
    have := congrArg List.length hrest
    simp only [List.length_drop] at this
    simp only [Slice.length] at this ⊢
    omega
  step with U64.blocks_outer.spec buf blocks _ 0#usize (by simp)
    (by have h0 : (0#usize).val = 0 := rfl
        rw [hbl, h0]; simp only [alloc.vec.Vec.length, Slice.length] at hb ⊢; omega)
    as ⟨ buf2, tmp1, hbuf2, hbuf2l ⟩
  rw [List.drop_zero] at hbuf2
  clear hrest hflat hblocks
  have hfin : ∀ tail : Bytes,
      tail = concatParts (rest.val.map fun x => uintBytes 8 x.val) →
      bytes buf2.val ++ tail = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 8 x.val) := by
    intro tail ht
    rw [hbuf2, ht, Array.append_assoc, ← concatParts_append, ← List.map_append, ← hsplit]
  have hrlt : rest.length < 1024 := by rw [hrl]; exact Nat.mod_lt _ (by norm_num)
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U64.blocks_rest.spec rest rest.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = rest.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append]
    apply hfin
    rw [hs, hout1, bytes_flatten, List.map_map]
    congr 2
    funext x; exact U64.bytes_to_le x
  · have hnil : rest.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      clear hfin hsplit hbuf2 hbuf2l
      scalar_tac
    simp only [WP.spec_ok]
    have := hfin #[] (by rw [hnil]; rfl)
    rw [Array.append_empty] at this
    exact this

/-- `<u64 as SszEncode>::ssz_append_fixed_slice`: chooses the path according to the length. -/
theorem U64.append_fixed_slice.spec (items : Slice Std.U64) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 8 * items.length ≤ Usize.max) :
    U64.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 8 x.val) ⦄ := by
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  have hB : encode.BLOCK_BYTES / 8#usize = ok 1024#usize := by
    unfold encode.BLOCK_BYTES; rfl
  simp only [step_simps, hB, bind_ok]
  spec_split
  · exact U64.append_le_short.spec items buf (by scalar_tac) hb
  · exact U64.append_le_blocks.spec items buf hb

/-- What `Ssz.serialize` gives on a list of `u64`. -/
theorem U64.serialize_list (l : List Std.U64) (limit : Nat) (hl : l.length ≤ limit)
    (hsz : 8 * l.length < 2 ^ 32) :
    serialize (.list Desc.uint64 limit) (.seq (l.map fun x => .uint x.val)) =
      .ok (concatParts (l.map fun x => uintBytes 8 x.val)) := by
  have hfit : ∀ n ∈ l.map (·.val), n < 2 ^ (8 * 8) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 8 limit (l.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint64 = .uint 8 from rfl]
  convert this using 2 <;> rfl

theorem U64.encode_list.spec (v : alloc.vec.Vec Std.U64) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 8 * v.length < 2 ^ 32)
    (hb : buf.length + 8 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U64.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint64 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U64.Insts.LibsszEncodeSszEncode, U64.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U64.append_fixed_slice.spec (alloc.vec.Vec.deref v) buf
    (by simpa [alloc.vec.Vec.deref] using hb) as ⟨ buf', hbuf' ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hbuf'
  exact ⟨_, U64.serialize_list v.val limit hl hsz, hbuf'⟩

/-- `<u64 as SszEncode>::ssz_fixed_slice_to_vec`:
`items.iter().map(|x| x.to_le_bytes()).collect::<Vec<_>>().into_flattened()`. -/
theorem U64.fixed_slice_to_vec.spec (items : Slice Std.U64)
    (hsz : 8 * items.length ≤ Usize.max) :
    U64.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun x => uintBytes 8 x.val) ⦄ := by
  unfold U64.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.map.default,
    StdModel.iter_map, bind_ok]
  step with collect_map_slice
    encode.SszEncodeU64.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64ArrayU88
    core.num.U64.to_le_bytes ()
    (fun _ => by
      simp only [encode.SszEncodeU64.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64ArrayU88.call_mut,
        lift, bind_ok])
    items as ⟨ v, hv ⟩
  have hvl : v.length = items.length := by simp [hv]
  step as ⟨ out, hout ⟩
  rw [hout, hv, bytes_flatten, List.map_map]
  congr 2
  funext x; exact U64.bytes_to_le x

/-- **`Vec<u64>::to_ssz`**: does not go through `ssz_append`; it builds the output `Vec`
directly. It gives the same bytes. -/
theorem U64.vec_to_ssz.spec (v : alloc.vec.Vec Std.U64) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : 8 * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz U64.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list Desc.uint64 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes out.val = enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz
  simp only [U64.Insts.LibsszEncodeSszEncode, U64.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U64.fixed_slice_to_vec.spec (alloc.vec.Vec.deref v)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ out, hout ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hout
  rw [hout]
  exact U64.serialize_list v.val limit hl hsz

/-! ## `u128` -/

/-- `u128::from_le_bytes`, as a number. -/
theorem U128.from_le_val (a : Array Std.U8 16#usize) :
    (core.num.U128.from_le_bytes a).val = leValue UScalar.val a.val := by
  have hx := core.num.U128.from_le_bytes.step_spec a
  simp only [lift, WP.spec_ok] at hx
  have : (core.num.U128.from_le_bytes a).val =
      (BitVec.fromLEBytes (List.map U8.bv a.val)).toNat := by
    simp [UScalar.val, hx]
  rw [this, toNat_fromLEBytes, leValue_map]
  rfl

/-- `u128::to_le_bytes`, as EthLib bytes. -/
theorem U128.bytes_to_le (x : Std.U128) :
    bytes (core.num.U128.to_le_bytes x).val = uintBytes 16 x.val := by
  have h := core.num.U128.to_le_bytes.step_spec x
  simp only [lift, WP.spec_ok] at h
  rw [h, bytes_toLEBytes 16 x.bv (by rfl)]
  rfl

/-- `chunks.iter().map(|c| u128::from_le_bytes(*c)).collect()`: a `map`. -/
theorem U128.from_le_chunks.spec (chunks : Slice (Array Std.U8 16#usize)) :
    decode.u128s_from_le_chunks chunks ⦃ r =>
      r.val = chunks.val.map core.num.U128.from_le_bytes ⦄ := by
  unfold decode.u128s_from_le_chunks
  simp only [core.slice.Slice.is_empty, bind_ok]
  by_cases h0 : chunks.length = 0
  · have hnil : chunks.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [h0, decide_true, ↓reduceIte, alloc.vec.Vec.into_boxed_slice,
      StdModel.into_boxed_slice, WP.spec_ok, hnil]
    rfl
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.map.default, StdModel.iter_map, bind_ok]
    step with collect_map_slice
      decode.u128s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU816U128
      core.num.U128.from_le_bytes ()
      (fun _ => by
        simp only [decode.u128s_from_le_chunks.closure.Insts.CoreOpsFunctionFnMutTupleShared0ArrayU816U128.call_mut,
          lift, bind_ok])
      chunks as ⟨ items, hitems ⟩
    simp only [alloc.vec.Vec.into_boxed_slice, StdModel.into_boxed_slice, WP.spec_ok]
    exact hitems

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
  step with as_chunks_spec 16#usize s (by simp) as ⟨ chunks, remainder, hchunks, hremainder ⟩
  step with U128.from_le_chunks.spec chunks as ⟨ r, hr ⟩
  have hv : (alloc.slice.Slice.into_vec r).val = r.val := rfl
  have hf : ((fun x : Std.U128 => x.val) ∘ core.num.U128.from_le_bytes) =
      (leValue UScalar.val) ∘ (fun a : Array Std.U8 16#usize => a.val) := by
    funext a; exact U128.from_le_val a
  rw [hv, hr, List.map_map, hf, ← List.map_map, hchunks, List.map_map]
  rfl

/-- **Decode `Vec<u128>`** with a limit. -/
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

/-- **`Vec<U128>::from_ssz_bytes`**: it is `decode_list_with_max` without a limit (`usize::MAX`). -/
theorem U128.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes U128.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Std.U128 => .seq (v.val.map fun x => .uint x.val)) r
        (deserialize (.list Desc.uint128 core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact U128.decode_list.spec s _ hs

/-- The loop that fills the output block: the first `k` are already the `to_le_bytes` of the
first `k` elements. -/
theorem U128.short_loop.spec (items : Slice Std.U128) (m : Std.Usize)
    (out : Slice (Array Std.U8 16#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U128.to_le_bytes) :
    encode.u128s_append_le_short_loop items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U128.to_le_bytes ⦄ := by
  unfold encode.u128s_append_le_short_loop
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U128.short_loop.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The short path** (up to one 8 KB block): everything is built in a local array and
appended with a single `extend_from_slice`. -/
theorem U128.append_le_short.spec (items : Slice Std.U128) (buf : alloc.vec.Vec Std.U8)
    (hn : items.length ≤ 512) (hb : buf.length + 16 * items.length ≤ Usize.max) :
    encode.u128s_append_le_short items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 16 x.val) ⦄ := by
  unfold encode.u128s_append_le_short
  simp only [step_simps]
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U128.short_loop.spec items items.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = items.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append, hs, hout1, bytes_flatten, List.map_map]
    congr 3
    funext x; exact U128.bytes_to_le x
  · rename_i h0
    have hnil : items.val = [] := by
      apply List.eq_nil_of_length_eq_zero; scalar_tac
    simp [hnil, concatParts]

/-- The block size, in elements. -/
theorem U128.blocks_B : encode.u128s_append_le_blocks.B = ok 512#usize := by
  unfold encode.u128s_append_le_blocks.B encode.BLOCK_BYTES
  rfl

/-- The inner loop: moves a whole block of 512 elements into the local array. -/
theorem U128.blocks_inner.spec (tmp : Array (Array Std.U8 16#usize) 512#usize)
    (block : Array Std.U128 512#usize) (k : Std.Usize) (hk : k.val ≤ 512)
    (hpre : tmp.val.take k.val = (block.val.take k.val).map core.num.U128.to_le_bytes) :
    encode.u128s_append_le_blocks_loop0_loop0 tmp block k ⦃ tmp' =>
      tmp'.val = block.val.map core.num.U128.to_le_bytes ⦄ := by
  unfold encode.u128s_append_le_blocks_loop0_loop0
  simp only [U128.blocks_B, bind_ok]
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ tmp1, htmp1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U128.blocks_inner.spec tmp1 block k1 (by scalar_tac)
    have hlt : k.val < block.val.length := by scalar_tac
    rw [htmp1, Array.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = 512 := by scalar_tac
    have h1 : tmp.val.take k.val = tmp.val := by
      apply List.take_of_length_le; simp [hkm]
    have h2 : block.val.take k.val = block.val := by
      apply List.take_of_length_le; simp [hkm]
    rw [h1, h2] at hpre
    exact hpre
termination_by 512 - k.val
decreasing_by scalar_decr_tac

/-- The outer loop: one 8 KB `extend_from_slice` per block. -/
theorem U128.blocks_outer.spec (buf : alloc.vec.Vec Std.U8)
    (blocks : Slice (Array Std.U128 512#usize)) (tmp : Array (Array Std.U8 16#usize) 512#usize)
    (i : Std.Usize) (hi : i.val ≤ blocks.length)
    (hb : buf.length + 8192 * (blocks.length - i.val) ≤ Usize.max) :
    encode.u128s_append_le_blocks_loop0 buf blocks tmp i ⦃ buf' _tmp' =>
      bytes buf'.val = bytes buf.val ++ concatParts
        ((((blocks.val.drop i.val).map (·.val)).flatten).map fun x => uintBytes 16 x.val) ∧
      buf'.length = buf.length + 8192 * (blocks.length - i.val) ⦄ := by
  unfold encode.u128s_append_le_blocks_loop0
  simp only [step_simps]
  spec_split
  · have hlt : i.val < blocks.length := by scalar_tac
    step as ⟨ block, hblock ⟩
    step with U128.blocks_inner.spec tmp block 0#usize (by simp) (by simp) as ⟨ tmp1, htmp1 ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ s1, hs1, hs1l ⟩
    step as ⟨ buf1, hbuf1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hs1b : bytes s1.val = concatParts (block.val.map fun x => uintBytes 16 x.val) := by
      rw [hs1, Slice.from_val, htmp1, bytes_flatten, List.map_map]
      congr 2
      funext x; exact U128.bytes_to_le x
    have hs1l' : s1.val.length = 8192 := by
      have : s1.length = 16 * 512 := by rw [hs1l]; simp [Slice.length]
      simpa [Slice.length] using this
    have hb1 : buf1.length + 8192 * (blocks.length - i2.val) ≤ Usize.max := by
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      simp only [alloc.vec.Vec.length] at hb
      omega
    apply WP.spec_mono (U128.blocks_outer.spec buf1 blocks tmp1 i2 (by scalar_tac) hb1)
    intro ⟨buf', tmp'⟩ h
    simp only [WP.uncurry'_pair] at h ⊢
    obtain ⟨h, hl'⟩ := h
    constructor
    · rw [h, hbuf1, bytes_append, hs1b, hi2, Array.append_assoc, ← concatParts_append,
        ← List.map_append]
      congr 3
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.flatten_cons, hblock]
    · rw [hl']
      simp only [alloc.vec.Vec.length, hbuf1, List.length_append, hs1l', hi2]
      omega
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    have him : i.val = blocks.length := by scalar_tac
    rw [him, List.drop_eq_nil_of_le (by simp)]
    simp [concatParts]
termination_by blocks.length - i.val
decreasing_by scalar_decr_tac

/-- The remainder loop (what does not fill a whole block): same as the short path's. -/
theorem U128.blocks_rest.spec (items : Slice Std.U128) (m : Std.Usize)
    (out : Slice (Array Std.U8 16#usize)) (k : Std.Usize)
    (hm : m.val = items.length) (hout : out.length = m.val) (hk : k.val ≤ m.val)
    (hpre : out.val.take k.val = (items.val.take k.val).map core.num.U128.to_le_bytes) :
    encode.u128s_append_le_blocks_loop1 items m out k ⦃ out' =>
      out'.val = items.val.map core.num.U128.to_le_bytes ⦄ := by
  unfold encode.u128s_append_le_blocks_loop1
  spec_split
  · step as ⟨ x, hx ⟩
    simp only [lift, bind_ok]
    step as ⟨ out1, hout1 ⟩
    step as ⟨ k1, hk1 ⟩
    apply U128.blocks_rest.spec items m out1 k1 hm (by rw [hout1]; simpa using hout)
      (by scalar_tac)
    have hlt : k.val < items.val.length := by scalar_tac
    rw [hout1, Slice.set_val_eq, hk1, take_succ_set _ _ _ (by scalar_tac), hpre,
      List.take_add_one, List.getElem?_eq_getElem hlt, hx, List.map_append]
    rfl
  · simp only [WP.spec_ok]
    have hkm : k.val = items.length := by scalar_tac
    have h1 : out.val.take k.val = out.val := by
      apply List.take_of_length_le; simp [Slice.length] at hout; omega
    have h2 : items.val.take k.val = items.val := by
      apply List.take_of_length_le; simp [Slice.length] at hkm; omega
    rw [h1, h2] at hpre
    exact hpre
termination_by m.val - k.val
decreasing_by scalar_decr_tac

/-- **The long path**: whole 8 KB blocks, and then the remainder. -/
theorem U128.append_le_blocks.spec (items : Slice Std.U128) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 16 * items.length ≤ Usize.max) :
    encode.u128s_append_le_blocks items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 16 x.val) ⦄ := by
  unfold encode.u128s_append_le_blocks
  simp only [step_simps]
  step as ⟨ n8, hn8 ⟩
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step with as_chunks_spec 512#usize items (by simp) as ⟨ blocks, rest, hblocks, hrest ⟩
  have hbl : blocks.length = items.length / 512 := by
    have := congrArg List.length hblocks
    simpa [Slice.length] using this
  have hflat : (blocks.val.map (·.val)).flatten = items.val.take (items.length / 512 * 512) := by
    rw [hblocks]; exact flatten_chunks 512 items.val _
  have hsplit : items.val = (blocks.val.map (·.val)).flatten ++ rest.val := by
    rw [hflat, hrest, List.take_append_drop]
  have hrl : rest.length = items.length % 512 := by
    have := congrArg List.length hrest
    simp only [List.length_drop] at this
    simp only [Slice.length] at this ⊢
    omega
  step with U128.blocks_outer.spec buf blocks _ 0#usize (by simp)
    (by have h0 : (0#usize).val = 0 := rfl
        rw [hbl, h0]; simp only [alloc.vec.Vec.length, Slice.length] at hb ⊢; omega)
    as ⟨ buf2, tmp1, hbuf2, hbuf2l ⟩
  rw [List.drop_zero] at hbuf2
  clear hrest hflat hblocks
  have hfin : ∀ tail : Bytes,
      tail = concatParts (rest.val.map fun x => uintBytes 16 x.val) →
      bytes buf2.val ++ tail = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 16 x.val) := by
    intro tail ht
    rw [hbuf2, ht, Array.append_assoc, ← concatParts_append, ← List.map_append, ← hsplit]
  have hrlt : rest.length < 512 := by rw [hrl]; exact Nat.mod_lt _ (by norm_num)
  spec_split
  · step as ⟨ out, back, hout, houtl, hback ⟩
    step with U128.blocks_rest.spec rest rest.len out 0#usize (by simp) houtl (by simp)
      (by simp) as ⟨ out1, hout1 ⟩
    have hl1 : out1.length = rest.length := by simp [Slice.length, hout1]
    step as ⟨ s, hs, hsl ⟩
    step as ⟨ buf', hbuf' ⟩
    rw [hbuf', bytes_append]
    apply hfin
    rw [hs, hout1, bytes_flatten, List.map_map]
    congr 2
    funext x; exact U128.bytes_to_le x
  · have hnil : rest.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      clear hfin hsplit hbuf2 hbuf2l
      scalar_tac
    simp only [WP.spec_ok]
    have := hfin #[] (by rw [hnil]; rfl)
    rw [Array.append_empty] at this
    exact this

/-- `<u128 as SszEncode>::ssz_append_fixed_slice`: chooses the path according to the length. -/
theorem U128.append_fixed_slice.spec (items : Slice Std.U128) (buf : alloc.vec.Vec Std.U8)
    (hb : buf.length + 16 * items.length ≤ Usize.max) :
    U128.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++
        concatParts (items.val.map fun x => uintBytes 16 x.val) ⦄ := by
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  have hB : encode.BLOCK_BYTES / 16#usize = ok 512#usize := by
    unfold encode.BLOCK_BYTES; rfl
  simp only [step_simps, hB, bind_ok]
  spec_split
  · exact U128.append_le_short.spec items buf (by scalar_tac) hb
  · exact U128.append_le_blocks.spec items buf hb

/-- What `Ssz.serialize` gives on a list of `u128`. -/
theorem U128.serialize_list (l : List Std.U128) (limit : Nat) (hl : l.length ≤ limit)
    (hsz : 16 * l.length < 2 ^ 32) :
    serialize (.list Desc.uint128 limit) (.seq (l.map fun x => .uint x.val)) =
      .ok (concatParts (l.map fun x => uintBytes 16 x.val)) := by
  have hfit : ∀ n ∈ l.map (·.val), n < 2 ^ (8 * 16) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 16 limit (l.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint128 = .uint 16 from rfl]
  convert this using 2 <;> rfl

theorem U128.encode_list.spec (v : alloc.vec.Vec Std.U128) (buf : alloc.vec.Vec Std.U8)
    (limit : Nat) (hl : v.length ≤ limit) (hsz : 16 * v.length < 2 ^ 32)
    (hb : buf.length + 16 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U128.Insts.LibsszEncodeSszEncode v buf
      ⦃ buf' => ∃ enc, serialize (.list Desc.uint128 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U128.Insts.LibsszEncodeSszEncode, U128.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U128.append_fixed_slice.spec (alloc.vec.Vec.deref v) buf
    (by simpa [alloc.vec.Vec.deref] using hb) as ⟨ buf', hbuf' ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hbuf'
  exact ⟨_, U128.serialize_list v.val limit hl hsz, hbuf'⟩

/-- `<u128 as SszEncode>::ssz_fixed_slice_to_vec`:
`items.iter().map(|x| x.to_le_bytes()).collect::<Vec<_>>().into_flattened()`. -/
theorem U128.fixed_slice_to_vec.spec (items : Slice Std.U128)
    (hsz : 16 * items.length ≤ Usize.max) :
    U128.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun x => uintBytes 16 x.val) ⦄ := by
  unfold U128.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.map.default,
    StdModel.iter_map, bind_ok]
  step with collect_map_slice
    encode.SszEncodeU128.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U128ArrayU816
    core.num.U128.to_le_bytes ()
    (fun _ => by
      simp only [encode.SszEncodeU128.ssz_fixed_slice_to_vec.closure.Insts.CoreOpsFunctionFnMutTupleShared0U128ArrayU816.call_mut,
        lift, bind_ok])
    items as ⟨ v, hv ⟩
  have hvl : v.length = items.length := by simp [hv]
  step as ⟨ out, hout ⟩
  rw [hout, hv, bytes_flatten, List.map_map]
  congr 2
  funext x; exact U128.bytes_to_le x

/-- **`Vec<u128>::to_ssz`**: does not go through `ssz_append`; it builds the output `Vec`
directly. It gives the same bytes. -/
theorem U128.vec_to_ssz.spec (v : alloc.vec.Vec Std.U128) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : 16 * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz U128.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list Desc.uint128 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes out.val = enc ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz
  simp only [U128.Insts.LibsszEncodeSszEncode, U128.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  simp only [↓reduceIte]
  step with U128.fixed_slice_to_vec.spec (alloc.vec.Vec.deref v)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac) as ⟨ out, hout ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hout
  rw [hout]
  exact U128.serialize_list v.val limit hl hsz

/-! ## `u8` -/

/-- A one-byte chunk is that byte. -/
theorem chunkVal_one (l : List Std.U8) (i : Nat) (h : i < l.length) :
    chunkVal 1 l i = l[i].val := by
  simp [chunkVal, List.take_one, List.head?_drop, List.getElem?_eq_getElem h, leValue]

/-- Read one byte at a time, the chunks are the bytes themselves. -/
theorem map_val_eq_chunkVal_one (l : List Std.U8) :
    l.map (·.val) = (List.range l.length).map (chunkVal 1 l) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [chunkVal_one _ _ (by simpa using h1)]

/-- It is `bytes.to_vec()`: there is no loop. The hypothesis is not used; it is there so that
the statement is the same as for the other widths. -/
theorem U8.ssz_decode_fixed_vec.spec (s : Slice Std.U8) (_h : s.length % 1 = 0) :
    U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec s ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range (s.length / 1)).map (chunkVal 1 s.val)
      | .Err _ => False ⦄ := by
  unfold U8.Insts.LibsszDecodeSszDecode.ssz_decode_fixed_vec
  step as ⟨ v, hv ⟩
  have : v.val = s.val := by rw [hv]; rfl
  rw [this, Nat.div_one]
  exact map_val_eq_chunkVal_one _

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

/-- An encoded `u8` is itself. -/
theorem uintBytes_one (x : Std.U8) : uintBytes 1 x.val = #[byte x] := by
  have := bytes_toLEBytes 1 x.bv (by rfl)
  rw [← UScalar.bv_toNat] at *
  rw [← this]
  simp [BitVec.toLEBytes, bytes, byte]

/-- The bytes of a list of `u8`, one by one. -/
theorem concatParts_uintBytes_one (l : List Std.U8) :
    concatParts (l.map fun x => uintBytes 1 x.val) = bytes l := by
  induction l with
  | nil => simp [concatParts, bytes]
  | cons x l ih => rw [List.map_cons, concatParts, ih, uintBytes_one, bytes_cons]

/-- It is `buf.extend_from_slice(items)`: there is no loop. -/
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
  step as ⟨ buf', hbuf' ⟩
  · simp [alloc.vec.Vec.deref] at *; scalar_tac
  have hbuf'' : bytes buf'.val = bytes buf.val ++
      concatParts (v.val.map fun x => uintBytes 1 x.val) := by
    rw [hbuf', bytes_append, concatParts_uintBytes_one]; simp [alloc.vec.Vec.deref]
  refine ⟨_, ?_, hbuf''⟩
  have hfit : ∀ n ∈ v.val.map (·.val), n < 2 ^ (8 * 1) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 1 limit (v.val.map (·.val)) hfit (by simpa using hl)
    (by simpa using hsz)
  simp only [List.map_map] at this
  rw [show Desc.uint8 = .uint 1 from rfl]
  convert this using 2 <;> simp [Function.comp_def]

/-- **`Vec<U8>::from_ssz_bytes`**: it is `decode_list_with_max` without a limit (`usize::MAX`). -/
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

/-- What `Ssz.serialize` gives on a `[u8; N]`: the same bytes. -/
theorem ArrayU8N.serialize_eq (N : Std.Usize) (a : Array Std.U8 N) (hN : N.val < 2 ^ 32) :
    serialize (.byteVector N.val) (.bytes (bytes a.val)) = .ok (bytes a.val) := by
  have ha : (bytes a.val).size = N.val := by simp
  have h32 : ¬ ((bytes a.val).size ≥ 2 ^ (8 * bytesPerOffset)) := by
    rw [ha, bytesPerOffset]; norm_num; exact hN
  simp only [serialize, ha, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hltN : ¬ (2 ^ (8 * bytesPerOffset) ≤ N.val) := by rw [← ha]; omega
  simp only [hltN, ↓reduceIte]; rfl

/-- **Encode `[u8; N]`** against `byteVector N`. -/
theorem ArrayU8N.ssz_append.spec (N : Std.Usize) (a : Array Std.U8 N) (buf : alloc.vec.Vec Std.U8)
    (hN : N.val < 2 ^ 32) (hb : buf.length + N.val ≤ Usize.max) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append a buf ⦃ buf' =>
      ∃ enc, serialize (.byteVector N.val) (.bytes (bytes a.val)) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  unfold ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ buf', hbuf' ⟩
  exact ⟨bytes a.val, ArrayU8N.serialize_eq N a hN, by rw [hbuf', bytes_append, Slice.from_val]⟩

/-- **In-place encode `[u8; N]`** (`ssz_write_fixed`): overwrites `out`, of length `N`, with
the same bytes. -/
theorem ArrayU8N.ssz_write_fixed.spec (N : Std.Usize) (a : Array Std.U8 N) (out : Slice Std.U8)
    (hN : N.val < 2 ^ 32) (h : out.length = N.val) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_write_fixed a out ⦃ out' =>
      ∃ enc, serialize (.byteVector N.val) (.bytes (bytes a.val)) = .ok enc ∧
        bytes out'.val = enc ⦄ := by
  unfold ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ out', hout' ⟩
  rw [ArrayU8N.serialize_eq N a hN, hout', Slice.from_val]

/-! ## `Vec<[u8; N]>` -/

/-- Chunk `k` of `n` bytes of `l`, as EthLib bytes. -/
def chunkBytes (n : Nat) (l : List Std.U8) (k : Nat) : Bytes := bytes ((l.drop (k * n)).take n)

/-- Cloning a `[u8; N]` does not fail and gives the same array. -/
theorem clone_array_u8 {N : Std.Usize} (a : Array Std.U8 N) :
    (core.clone.CloneArray N core.clone.CloneU8).clone a = ok a := by
  have h := core.array.CloneArray.clone_spec core.clone.CloneU8 a (fun _ _ => rfl)
  show core.array.CloneArray.clone core.clone.CloneU8 a = ok a
  generalize core.array.CloneArray.clone core.clone.CloneU8 a = m at h
  cases m with
  | ret r => rw [WP.spec_ok] at h; rw [h]
  | vis e k => exact ((WP.spec_vis e k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

/-- It is `bytes.as_chunks::<N>().0.to_vec()`: there is no loop. -/
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
  step as ⟨ chunks, remainder, hchunks, hremainder ⟩
  step as ⟨ v, hv ⟩
  · intro a _; exact clone_array_u8 a
  have hvv : v.val = chunks.val := by rw [hv]; rfl
  have := congrArg (List.map bytes) hchunks
  simp only [List.map_map] at this
  rw [hvv]
  exact this

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


/-- **Encode `Vec<[u8; N]>`.** It is
`buf.extend_from_slice(items.as_flattened())`: there is no loop. -/
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
  step as ⟨ plano, hplano, hplanol ⟩
  · simp [alloc.vec.Vec.deref] at *; scalar_tac
  step as ⟨ buf', hbuf' ⟩
  · simp [alloc.vec.Vec.deref] at *; scalar_tac
  have hbuf'' : bytes buf'.val = bytes buf.val ++
      concatParts (v.val.map fun a => bytes a.val) := by
    rw [hbuf', bytes_append, hplano, bytes_flatten]; simp [alloc.vec.Vec.deref]
  refine ⟨_, ?_, hbuf''⟩
  have hd : ∀ d ∈ v.val.map (fun a => bytes a.val), d.size = N.val := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨a, _, rfl⟩ := hd
    simp
  have := serialize_list_byteVector N.val limit (v.val.map (fun a => bytes a.val)) hd hN32
    (by simpa using hl) (by simpa using hsz)
  simp only [List.map_map] at this
  convert this using 2; simp [Function.comp_def]

/-- **`Vec<[u8; N]>::from_ssz_bytes`**: `decode_list_with_max` without a limit. -/
theorem ArrayU8N.vec_from_ssz_bytes.spec (N : Std.Usize) (s : Slice Std.U8) (hN : 0 < N.val)
    (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes (ArrayU8N.Insts.LibsszDecodeSszDecode N) s
      ⦃ r => Agrees (fun v : alloc.vec.Vec (Array Std.U8 N) => .seq (v.val.map fun a => .bytes (bytes a.val))) r
        (deserialize (.list (.byteVector N.val) core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact ArrayU8N.decode_list.spec N s _ hN hs

/-! ## `Vec<bool>`

Each element can fail: the loop invariant carries what has been decoded up to `i` and
compares the rest with EthLib's `deserializeEach .bool`. -/

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

/-- **`Vec<bool>::from_ssz_bytes`**: `decode_list_with_max` without a limit. -/
theorem Bool.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes Bool.Insts.LibsszDecodeSszDecode s
      ⦃ r => Agrees (fun v : alloc.vec.Vec Bool => .seq (v.val.map .bool)) r
        (deserialize (.list .bool core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact Bool.decode_list.spec s _ hs

/-! ## Where libssz and EthLib diverge

EthLib rejects every input of 2³² bytes or more (`offsetOverflow`), even in a list of
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

/-! ## `Vec<T>::to_ssz` for `u8`, `[u8; N]` and `bool` -/

/-- **`Vec<T>::to_ssz` with fixed-size `T` and the default `ssz_fixed_slice_to_vec`**: it is
`ssz_append` on an empty buffer (with the capacity already reserved). -/
theorem vec_to_ssz_default {T : Type} (inst : encode.SszEncode T) (v : alloc.vec.Vec T)
    (w : Std.Usize) (P : alloc.vec.Vec Std.U8 → Prop)
    (hfix : inst.is_fixed_size = ok true) (hw : inst.fixed_size = ok w)
    (hdef : inst.ssz_fixed_slice_to_vec = encode.SszEncode.ssz_fixed_slice_to_vec.default inst)
    (hmul : w.val * v.length ≤ Usize.max)
    (happ : ∀ buf : alloc.vec.Vec Std.U8, buf.val = [] →
      alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append inst v buf ⦃ P ⦄) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz inst v ⦃ P ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz
  simp only [hfix, bind_ok, ↓reduceIte, hdef, encode.SszEncode.ssz_fixed_slice_to_vec.default, hw]
  step as ⟨ i2, hi2 ⟩
  · simpa [alloc.vec.Vec.deref] using hmul
  have := happ (alloc.vec.Vec.with_capacity Std.U8 i2) (by simp [alloc.vec.Vec.with_capacity])
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append at this
  simpa only [hfix, bind_ok, ↓reduceIte] using this

/-- **`Vec<u8>::to_ssz`**. -/
theorem U8.vec_to_ssz.spec (v : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : 1 * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz U8.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list Desc.uint8 limit) (.seq (v.val.map fun x => .uint x.val))
          = .ok enc ∧ bytes out.val = enc ⦄ := by
  apply vec_to_ssz_default U8.Insts.LibsszEncodeSszEncode v 1#usize _ rfl rfl rfl (by scalar_tac)
  intro buf hbuf
  apply WP.spec_mono (U8.encode_list.spec v buf limit hl hsz
    (by simp only [alloc.vec.Vec.length, hbuf]; scalar_tac))
  rintro out ⟨enc, henc, hb⟩
  refine ⟨enc, henc, ?_⟩
  rw [hb, hbuf]; simp [bytes]

/-- **`Vec<[u8; N]>::to_ssz`**. -/
theorem ArrayU8N.vec_to_ssz.spec (N : Std.Usize) (v : alloc.vec.Vec (Array Std.U8 N))
    (limit : Nat) (hl : v.length ≤ limit) (hN32 : N.val < 2 ^ 32)
    (hsz : N.val * v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz (ArrayU8N.Insts.LibsszEncodeSszEncode N) v
      ⦃ out => ∃ enc, serialize (.list (.byteVector N.val) limit)
          (.seq (v.val.map fun a => .bytes (bytes a.val))) = .ok enc ∧ bytes out.val = enc ⦄ := by
  apply vec_to_ssz_default (ArrayU8N.Insts.LibsszEncodeSszEncode N) v N _ rfl rfl rfl
    (by scalar_tac)
  intro buf hbuf
  apply WP.spec_mono (ArrayU8N.encode_list.spec N v buf limit hl hN32 hsz
    (by simp only [alloc.vec.Vec.length, hbuf]; scalar_tac))
  rintro out ⟨enc, henc, hb⟩
  refine ⟨enc, henc, ?_⟩
  rw [hb, hbuf]; simp [bytes]

/-- **`Vec<bool>::to_ssz`**. -/
theorem Bool.vec_to_ssz.spec (v : alloc.vec.Vec Bool) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : v.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.to_ssz Bool.Insts.LibsszEncodeSszEncode v
      ⦃ out => ∃ enc, serialize (.list .bool limit) (.seq (v.val.map .bool)) = .ok enc ∧
          bytes out.val = enc ⦄ := by
  apply vec_to_ssz_default Bool.Insts.LibsszEncodeSszEncode v 1#usize _ rfl rfl rfl
    (by scalar_tac)
  intro buf hbuf
  apply WP.spec_mono (Bool.encode_list.spec v buf limit hl hsz
    (by simp only [alloc.vec.Vec.length, hbuf]; scalar_tac))
  rintro out ⟨enc, henc, hb⟩
  refine ⟨enc, henc, ?_⟩
  rw [hb, hbuf]; simp [bytes]

end Libssz.Proofs
