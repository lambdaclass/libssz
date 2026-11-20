module
public import Libssz.Merkle.Proofs.Tree
@[expose] public section

/-!
# `mix_in_length` and `pack`

* `mix_in_length` is EthLib's `mixIn` with `lengthWord`: the length, written in 32
  little-endian bytes, as the right sibling of the root.
* `pack` is `packBytes`: the bytes in 32-byte nodes, the last one padded with zeros.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz

namespace Libssz.Merkle

/-! ## Integers in 32 bytes -/

/-- An integer that fits in `k` bytes, written in `k + m`: the `k` bytes and `m` zeros. -/
theorem uintBytes_add_zeros (k m v : Nat) (hv : v < 256 ^ k) :
    uintBytes (k + m) v = uintBytes k v ++ Array.replicate m 0 := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    subst this
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Nat.zero_add] at ih ⊢
      rw [uintBytes_succ, ih, uintBytes_zero]
      simp [Array.replicate_succ']
  | succ k ih =>
    rw [Nat.add_right_comm, uintBytes_succ, uintBytes_succ, ih (v / 256) (by
      rw [Nat.pow_succ] at hv; omega), Array.append_assoc]

/-- Writing `l` at the start of `n` copies of `x`: `l` and what remains of the copies. -/
theorem setSlice!_zero_replicate {α : Type} (x : α) (l : List α) (n : Nat) (h : l.length ≤ n) :
    (List.replicate n x).setSlice! 0 l = l ++ List.replicate (n - l.length) x := by
  simp [List.setSlice!, Nat.min_eq_left h, List.drop_replicate]

/-- `u64::to_le_bytes`, as EthLib bytes. -/
theorem U64.bytes_to_le (x : Std.U64) :
    bytes (core.num.U64.to_le_bytes x).val = uintBytes 8 x.val := by
  have h := core.num.U64.to_le_bytes.step_spec x
  simp only [lift, WP.spec_ok] at h
  rw [h, Libssz.Proofs.bytes_toLEBytes 8 x.bv (by rfl)]
  rfl

section Hashed

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **`mix_in_length` is the specification's `mixIn` with `lengthWord`.** -/
theorem mix_in_length.spec (root : Node) (length : Std.Usize) :
    mix_in_length inst h root length ⦃ r =>
      bytes r.val = mixIn (bytes root.val) (lengthWord length.val) ⦄ := by
  unfold mix_in_length
  step as ⟨ s, back, hs, hslen, hback ⟩
  simp only [lift, bind_ok]
  step as ⟨ s2, hs2 ⟩
  step with hash_nodes.spec inst h hl root (back s2) as ⟨ r, hr ⟩
  have hw : bytes (back s2).val = lengthWord length.val := by
    have hcast : (UScalar.cast UScalarTy.U64 length).val = length.val := by
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (by have := usize_lt length; simp [UScalarTy.numBits]; omega)
    set l := (core.num.U64.to_le_bytes (UScalar.cast UScalarTy.U64 length)).val with hl8
    have hlen : l.length = 8 := by simp [hl8]
    have hs2v : s2.val = l := by rw [hs2, hl8]; simp [Array.to_slice]
    have hset : (back s2).val = l ++ List.replicate 24 0#u8 := by
      rw [hback s2, hs2v, Array.repeat_val, setSlice!_zero_replicate _ _ _ (by simp; omega),
        hlen]
      rfl
    rw [hset, Libssz.Proofs.bytes_append, hl8, U64.bytes_to_le, hcast, lengthWord,
      show bytesPerChunk = 8 + 24 from rfl,
      uintBytes_add_zeros 8 24 _ (by have := usize_lt length; omega)]
    congr 1
  rw [hr, mixIn_eq, hw]

include hl in
/-- **`mix_in_selector` is the specification's `mixIn` with the selector in a node**
(`lengthWord`, which is what EthLib mixes into a union: `selectorWord`). -/
theorem mix_in_selector.spec (root : Node) (selector : Std.U8) :
    mix_in_selector inst h root selector ⦃ r =>
      bytes r.val = mixIn (bytes root.val) (lengthWord selector.val) ⦄ := by
  unfold mix_in_selector
  step as ⟨ n1, hn1 ⟩
  step with hash_nodes.spec inst h hl root n1 as ⟨ r, hr ⟩
  have hw : bytes n1.val = lengthWord selector.val := by
    rw [lengthWord, show bytesPerChunk = 1 + 31 from rfl,
      uintBytes_add_zeros 1 31 _ (by have := selector.hBounds; simp at this ⊢; omega),
      uintBytes_succ, uintBytes_zero, hn1, Array.set_val_eq, Array.repeat_val]
    simp [bytes, Libssz.Proofs.byte, Nat.mod_eq_of_lt (show selector.val < 256 by scalar_tac)]
    have e : (selector.val : Nat) = (UInt8.ofBitVec selector.bv).toNat := rfl
    rw [e, UInt8.ofNat_toNat]
  rw [hr, mixIn_eq, hw]

end Hashed

/-! ## `pack` -/

/-- `as_chunks::<32>()` in the `ssz-merkle` extraction: the same model as in the codec. -/
theorem as_chunks32.spec (s : Slice Std.U8) :
    core.slice.Slice.as_chunks 32#usize s ⦃ r =>
      r.1.val.map (·.val) = (List.range (s.length / 32)).map (StdModel.chunk 32 s.val) ∧
      r.2.val = s.val.drop (s.length / 32 * 32) ⦄ := by
  unfold core.slice.Slice.as_chunks StdModel.as_chunks
  have hN : ¬ ((32#usize).val = 0) := by decide
  simp only [hN, ↓reduceIte, WP.spec_ok, Slice.from_val]
  refine ⟨ ?_, rfl ⟩
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem chunksOf_getElem (l : List Node) (i : Nat) (h : i < (chunksOf l).size) :
    (chunksOf l)[i] = bytes (l[i]'(by simpa using h)).val := by
  simp [chunksOf]

/-- **What `pack` builds, compared with `packBytes`.** The full chunks (`whole`), and, if the
length is not a multiple of 32, a last node with the remainder and zeros. -/
theorem packBytes_eq (values : List Std.U8) (whole : List Node) (last : List Node)
    (hw : whole.map (·.val) = (List.range (values.length / 32)).map (StdModel.chunk 32 values))
    (hlast : (values.length % 32 = 0 ∧ last = []) ∨
      (values.length % 32 ≠ 0 ∧ ∃ n : Node, last = [n] ∧
        n.val = values.drop (values.length / 32 * 32) ++
          List.replicate (32 - values.length % 32) 0#u8)) :
    chunksOf (whole ++ last) = packBytes (bytes values) := by
  have hwl : whole.length = values.length / 32 := by
    have := congrArg List.length hw; simpa using this
  have hsize : (whole ++ last).length = (values.length + 31) / 32 := by
    rcases hlast with ⟨ h0, rfl ⟩ | ⟨ h0, n, rfl, _ ⟩ <;> simp [hwl] <;> omega
  apply Array.ext
  · simp [packBytes, hsize, bytesPerChunk]
  · intro i h1 h2
    have hi : i < (whole ++ last).length := by simpa using h1
    have hsz := packBytes_chunk_size (bytes values) i h2
    apply Array.ext
    · rw [hsz, chunksOf_getElem]; simp [bytesPerChunk]
    · intro j hj1 hj2
      have hj : j < 32 := by rw [hsz] at hj2; exact hj2
      have hval : ∀ m : Node, (chunksOf (whole ++ last))[i]'h1 = bytes m.val →
          (m.val[j]? = if i * 32 + j < values.length then values[i * 32 + j]? else some 0#u8) →
          ((chunksOf (whole ++ last))[i])[j] = ((packBytes (bytes values))[i])[j] := by
        intro m hm hmj
        simp only [hm]
        have hml : j < m.val.length := by simp; omega
        rw [show (bytes m.val)[j]'(by simpa using hml) = byte (m.val[j]'hml) by simp [bytes]]
        by_cases hin : i * 32 + j < values.length
        · rw [packBytes_get _ i j h2 (by simpa using hj) (by simpa using hin)]
          rw [if_pos hin, List.getElem?_eq_getElem hml, List.getElem?_eq_getElem hin] at hmj
          simp only [Option.some.injEq] at hmj
          simp [bytes, hmj]
        · rw [packBytes_padding _ i j h2 (by simpa using hj) (by simpa [bytesPerChunk] using hin)]
          rw [if_neg hin, List.getElem?_eq_getElem hml] at hmj
          simp only [Option.some.injEq] at hmj
          rw [hmj]; rfl
      by_cases hiw : i < whole.length
      · apply hval whole[i]
        · rw [chunksOf_getElem, List.getElem_append_left hiw]
        · have hc := congrArg (·[i]?) hw
          simp only [List.getElem?_map, List.getElem?_eq_getElem hiw,
            List.getElem?_range (show i < values.length / 32 by omega), Option.map_some,
            Option.some.injEq] at hc
          rw [hc]
          have hin : i * 32 + j < values.length := by
            have : i < values.length / 32 := by omega
            omega
          rw [if_pos hin]
          simp [StdModel.chunk, List.getElem?_take, List.getElem?_drop, hj, Nat.add_comm]
      · rcases hlast with ⟨ h0, rfl ⟩ | ⟨ h0, n, rfl, hn ⟩
        · simp at hi; omega
        · have hieq : i = whole.length := by simp at hi; omega
          apply hval n
          · rw [chunksOf_getElem]
            simp [hieq]
          · rw [hn]
            have hlen := Nat.div_add_mod values.length 32
            have hi32 : i * 32 = values.length / 32 * 32 := by rw [hieq, hwl]
            by_cases hin : i * 32 + j < values.length
            · rw [if_pos hin, List.getElem?_append_left (by simp; omega),
                List.getElem?_drop]
              rw [hi32]
            · rw [if_neg hin, List.getElem?_append_right (by simp; omega)]
              simp only [List.length_drop, List.getElem?_replicate]
              rw [if_pos (by omega)]

/-- `extend_from_slice` of nodes: cloning a node does not change it, so it appends the same
ones. -/
theorem extend_from_slice_node_spec (v : alloc.vec.Vec Node) (s : Slice Node)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice (core.clone.CloneArray 32#usize core.clone.CloneU8) v s
      ⦃ v' => v'.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  step with List.clone_spec (fun x _ => clone_node x) as ⟨ s', hs', _ ⟩
  simp [hs']

/-- **`pack` is `packBytes`**: the bytes in 32-byte nodes, the last one padded with zeros. -/
theorem pack.spec (values : Slice Std.U8) :
    pack values ⦃ v => chunksOf v.val = packBytes (bytes values.val) ⦄ := by
  unfold pack
  step with as_chunks32.spec values as ⟨ whole, rest, hw, hr ⟩
  have hrl : rest.length = values.length % 32 := by
    simp only [Slice.length, hr, List.length_drop]
    have := Nat.div_add_mod values.length 32
    simp only [Slice.length] at this ⊢
    omega
  step as ⟨ i1, hi1 ⟩
  step with extend_from_slice_node_spec (alloc.vec.Vec.with_capacity (Std.Array Std.U8 32#usize) i1)
    whole (by simp [alloc.vec.Vec.with_capacity]) as ⟨ c1, hc1 ⟩
  have hc1' : c1.val = whole.val := by rw [hc1]; simp [alloc.vec.Vec.with_capacity]
  step as ⟨ b, hb ⟩
  spec_split
  · rename_i hbt
    have hre : values.length % 32 = 0 := by
      have : rest.length = 0 := by rw [← hb]; exact hbt
      omega
    simp only [WP.spec_ok]
    rw [hc1', ← List.append_nil whole.val]
    exact packBytes_eq values.val whole.val [] hw (Or.inl ⟨ hre, rfl ⟩)
  · rename_i hbf
    have hre : values.length % 32 ≠ 0 := by
      have : ¬ rest.length = 0 := by rw [← hb]; exact hbf
      omega
    step as ⟨ sl, back, hsl, hsllen, hback ⟩
    step as ⟨ s1, hs1 ⟩
    step as ⟨ v, hv ⟩
    case h =>
      have hwl : whole.val.length = values.length / 32 := by
        have := congrArg List.length hw; simpa using this
      rw [hc1', hwl]
      clear hw hr hc1 hb hback hsl
      have := values.length_ineq
      scalar_tac
    rw [hv, hc1']
    apply packBytes_eq values.val whole.val [back s1] hw
    refine Or.inr ⟨ hre, back s1, rfl, ?_ ⟩
    rw [hback s1, hs1, Array.repeat_val, setSlice!_zero_replicate _ _ _ (by
      simp only [Slice.length] at hrl; simp; omega), hr]
    congr 2
    have h32 : (32#usize).val = 32 := rfl
    simp only [List.length_drop, h32]
    have := Nat.div_add_mod values.length 32
    simp only [Slice.length] at this ⊢
    omega

/-- `core::cmp::min` of two `usize`. -/
@[step]
theorem min_usize.spec (x y : Std.Usize) :
    core.cmp.min core.cmp.OrdUsize x y ⦃ r => r.val = min x.val y.val ⦄ := by
  simp only [core.cmp.min, core.cmp.OrdUsize, liftFun2, WP.spec_ok,
    core.cmp.impls.OrdUsize.min_val]

/-- **`pack_bits`** is `pack` of the first `⌈num_bits / 8⌉` bytes (or of all of them, if
there are fewer). It does not touch the extra bits of the last byte: the caller leaves them at
zero. -/
theorem pack_bits.spec (bits : Slice Std.U8) (num_bits : Std.Usize) :
    pack_bits bits num_bits ⦃ v =>
      chunksOf v.val = packBytes (bytes (bits.val.take ((num_bits.val + 7) / 8))) ⦄ := by
  unfold pack_bits
  step as ⟨ nb, hnb ⟩
  step as ⟨ m, hm ⟩
  step as ⟨ eff, heff ⟩
  apply WP.spec_mono (pack.spec eff)
  intro v hv
  rw [hv, heff]
  congr 2
  simp only [List.slice, List.drop_zero, Nat.sub_zero]
  rw [hm, hnb, Nat.ceilDiv_eq_add_pred_div]
  have h7 : (num_bits.val + 8 - 1) / 8 = (num_bits.val + 7) / 8 := by omega
  have hlen : bits.len.val = bits.val.length := by simp
  rw [h7, List.take_eq_take_iff, hlen]
  omega

/-! ## `merkleize_progressive` (EIP-7916) -/

section Progressive

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

theorem chunksOf_take (l : List Node) (k : Nat) :
    chunksOf (l.take k) = ((chunksOf l).toList.take k).toArray := by
  simp [chunksOf, List.map_take]

theorem chunksOf_drop (l : List Node) (k : Nat) :
    (chunksOf (l.drop k)).toList = (chunksOf l).toList.drop k := by
  simp [chunksOf, List.map_drop]

theorem pow4_mod3 (l : Nat) : 4 ^ l % 3 = 1 := by
  induction l with
  | zero => rfl
  | succ l ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

include hl in
/-- The step of `merkleize_progressive`: with `num_leaves = 4^level`, the subtree with that
many leaves on the left and the rest on the right. The hypothesis `hbound` says that
`num_leaves * 4` does not overflow: the computation only continues while nodes remain, and
before level `level`, `(4^level - 1) / 3` have already been consumed. -/
theorem merkleize_progressive_inner.spec (chunks : Slice Node) (num_leaves : Std.Usize)
    (level : Nat) (hw : num_leaves.val = 4 ^ level)
    (hbound : chunks.length ≠ 0 → 12 * ((4 ^ level - 1) / 3 + chunks.length) ≤ Usize.max) :
    merkleize_progressive_inner inst h chunks num_leaves ⦃ r =>
      bytes r.val = merkleizeProgressiveUnchecked (chunksOf chunks.val).toList level ⦄ := by
  unfold merkleize_progressive_inner
  rw [merkleizeProgressiveUnchecked_unfold]
  step as ⟨ b, hb ⟩
  spec_split
  · rename_i hbt
    have h0 : chunks.length = 0 := by rw [← hb]; exact hbt
    have hnil : chunks.val = [] := List.eq_nil_of_length_eq_zero h0
    simp only [WP.spec_ok, hnil]
    simp [chunksOf, bytes, Array.repeat_val, zeroChunk, bytesPerChunk]
    rfl
  · rename_i hbf
    have hne : chunks.length ≠ 0 := fun h0 => hbf (by rw [hb]; exact h0)
    have hb' := hbound hne
    have hm3 := pow4_mod3 level
    step as ⟨ take, htake ⟩
    have htake' : take.val = min (4 ^ level) chunks.length := by rw [htake, hw]; simp
    step as ⟨ s, hs, hslen ⟩
    step with merkleize.spec inst h hl s (some num_leaves)
      (by intro l hl'; cases hl'; rw [hslen, htake', hw]; omega) as ⟨ subtree, hsub ⟩
    step as ⟨ s1, hs1, hs1len ⟩
    have hmul : num_leaves.val * 4 ≤ Usize.max := by rw [hw]; omega
    step as ⟨ i1, hi1 ⟩
    have hp1 : 4 ^ (level + 1) = 4 ^ level * 4 := Nat.pow_succ 4 level
    step with merkleize_progressive_inner.spec s1 i1 (level + 1) (by rw [hi1, hw, hp1])
      (by
        intro hs1ne
        rw [hp1]
        have hlt : 4 ^ level < chunks.length := by
          rw [hs1len, htake'] at hs1ne; omega
        rw [hs1len, htake', Nat.min_eq_left (by omega)]
        omega)
      as ⟨ rest, hrest ⟩
    step with hash_nodes.spec inst h hl subtree rest as ⟨ r, hr ⟩
    have hne' : ¬ (chunksOf chunks.val).toList.isEmpty = true := by
      simp [chunksOf]; intro h0; exact hne (by simp [Slice.length, h0])
    have hsv : s.val = chunks.val.take (4 ^ level) := by
      rw [hs, List.slice, List.drop_zero, Nat.sub_zero, htake', List.take_eq_take_iff]
      simp only [Slice.length]; omega
    have hs1v : s1.val = chunks.val.drop (4 ^ level) := by
      rw [hs1, htake']
      by_cases hle : 4 ^ level ≤ chunks.length
      · rw [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right (by omega), List.drop_eq_nil_of_le (by simp [Slice.length]),
          List.drop_eq_nil_of_le (by simp only [Slice.length] at hle; omega)]
    have hsub' : bytes subtree.val =
        subtreeAt ((chunksOf chunks.val).toList.take (4 ^ level)).toArray (depthFor (4 ^ level)) 0 := by
      rw [merkleizeBounded_ok s (some num_leaves)
        (by intro l hl'; cases hl'; rw [hslen, htake', hw]; omega)] at hsub
      simp only [Option.map_some, Option.getD_some, Except.ok.injEq, hw] at hsub
      rw [← hsub, hsv, chunksOf_take]
    have hrest' : bytes rest.val =
        merkleizeProgressiveUnchecked ((chunksOf chunks.val).toList.drop (4 ^ level)) (level + 1) := by
      rw [hrest, hs1v, chunksOf_drop]
    rw [if_neg hne', hr, hsub', hrest']
termination_by chunks.length
decreasing_by
  have := Nat.pow_pos (n := level) (by decide : 0 < 4)
  rw [hs1len, htake']
  omega

include hl in
/-- **`merkleize_progressive` is EthLib's `merkleizeProgressiveUnchecked` (EIP-7916)**, for
fewer than `Usize.max / 12` nodes: with more, `num_leaves * 4` could overflow. A node is 32
bytes, so on 64 bits that is more memory than exists. -/
theorem merkleize_progressive.spec (chunks : Slice Node)
    (hbound : 12 * chunks.length ≤ Usize.max) :
    merkleize_progressive inst h chunks ⦃ r =>
      bytes r.val = merkleizeProgressiveUnchecked (chunksOf chunks.val).toList ⦄ := by
  unfold merkleize_progressive
  exact merkleize_progressive_inner.spec inst h hl chunks 1#usize 0 rfl
    (fun _ => by simpa using hbound)

end Progressive

end Libssz.Merkle
