module
public import Libssz.Merkle.Proofs.Types
@[expose] public section

/-!
# The `hash_tree_root` of `Vec<T>`

`Vec<T>` has no limit in its type. `ssz-merkle` merkleizes it as an SSZ list whose limit is
its own length: the tree of its nodes without a limit, with the length mixed in on the right.
The theorems compare against EthLib's `hashTreeRoot` for `List[T, len]`.

* `Vec<u64>`: basic items, packed. The `hash_tree_root` calls
  `<u64 as SszEncode>::ssz_fixed_slice_to_vec`, from the codec: it is one of the functions
  linked with the codec extraction, and its theorem is the codec's
  (`U64.fixed_slice_to_vec.spec`).
* `Vec<[u8; 48]>`: composite items, one node per item.
* `Vec<[u8; 4]>`: **here libssz does not match the specification** (see `README.md`).
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz

namespace Libssz.Merkle

/-! ## EthLib: the root of a list -/

/-- **The root of a list of basic items** according to EthLib: the tree of the packed items,
with the capacity given by the limit, and the length mixed in on the right. -/
theorem hashTreeRoot_list_basic (elem : Desc) (hb : elem.isBasic = true)
    (hn : elem.nesting = 1) (limit : Nat) (values : List Value) (parts : List Bytes)
    (hl : values.length ≤ limit) (hser : serializeEach elem values = .ok parts) :
    hashTreeRoot (.list elem limit) (.seq values) =
      (merkleizeBoundedUnchecked (packElements parts)
        (some (chunksForBytes (limit * elem.itemLength)))).map
        (fun root => mixIn root (lengthWord values.length)) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.list elem limit).nesting = 1 + 1 by
    simp [Desc.nesting, hn], hashTreeRootAt_succ]
  have hlay : merkleLayout (.list elem limit) (.seq values) =
      .ok (MerkleLayout.packing (packElements parts)
        (some (chunksForBytes (limit * elem.itemLength))) (some (lengthWord values.length))) := by
    simp [merkleLayout, sequenceLayout, hb, hser, Nat.not_lt.mpr hl, Pure.pure, Except.pure,
      Bind.bind, Except.bind]
  simp only [hlay, Bind.bind, Except.bind]
  simp only [layoutChunksAt_eq, MerkleLayout.packing, Leaves.count, Option.getD_none,
    Array.extract_size]
  cases hm : merkleizeBoundedUnchecked (packElements parts)
    (some (chunksForBytes (limit * elem.itemLength))) <;>
    simp [hm, Pure.pure, Except.pure, Except.map]

/-- **The root of a list of composite items** according to EthLib: the tree of the item
roots, with capacity equal to the limit, and the length mixed in on the right. -/
theorem hashTreeRoot_list_composite (elem : Desc) (hb : elem.isBasic = false) (limit : Nat)
    (values : List Value) (roots : List Bytes) (hl : values.length ≤ limit)
    (hroots : values.mapM (hashTreeRoot elem) = .ok roots) :
    hashTreeRoot (.list elem limit) (.seq values) =
      (merkleizeBoundedUnchecked roots.toArray (some limit)).map
        (fun root => mixIn root (lengthWord values.length)) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.list elem limit).nesting = elem.nesting + 1 from rfl,
    hashTreeRootAt_succ]
  have hlay : merkleLayout (.list elem limit) (.seq values) =
      .ok (MerkleLayout.nesting (values.map fun v => some (elem, v)) (some limit)
        (some (lengthWord values.length))) := by
    simp [merkleLayout, sequenceLayout, hb, Nat.not_lt.mpr hl, Pure.pure, Except.pure,
      Bind.bind, Except.bind]
  have hchunks : layoutChunksAt elem.nesting
      (MerkleLayout.nesting (values.map fun v => some (elem, v)) (some limit)
        (some (lengthWord values.length))) = .ok roots.toArray := by
    simp only [layoutChunksAt_eq, MerkleLayout.nesting, Leaves.count, Option.getD_none,
      List.drop_zero, Nat.sub_zero, List.take_length]
    rw [List.mapM_map]
    rw [mapM_congr _ (hashTreeRoot elem) _ (by
      intro v _
      show hashTreeRootAt _ elem v = hashTreeRoot elem v
      exact hashTreeRootAt_eq_hashTreeRoot _ _ _ (Nat.le_refl _)), hroots]
    rfl
  simp only [hlay, Bind.bind, Except.bind]
  rw [hchunks]
  simp only [MerkleLayout.nesting]
  cases hm : merkleizeBoundedUnchecked roots.toArray (some limit) <;>
    simp [hm, Pure.pure, Except.pure, Except.map]

/-- If each item is encoded with `f`, the list of encodings is `map f`. -/
theorem serializeEach_map (elem : Desc) (values : List Value) (f : Value → Bytes)
    (hf : ∀ v ∈ values, serialize elem v = .ok (f v)) :
    serializeEach elem values = .ok (values.map f) := by
  rw [serializeEach_eq]
  induction values with
  | nil => simp [serializeEachFrom]
  | cons v rest ih =>
    simp only [serializeEachFrom, hf v (by simp), Bind.bind, Except.bind]
    rw [serializeEachFrom_eq, ih (fun w hw => hf w (by simp [hw]))]
    rfl

/-- `packElements` packs the concatenation of the parts. -/
theorem foldl_append (acc : Bytes) (parts : List Bytes) :
    parts.foldl (fun total part => total ++ part) acc = acc ++ concatParts parts := by
  induction parts generalizing acc with
  | nil => simp [concatParts]
  | cons p rest ih => simp [concatParts, ih, Array.append_assoc]

theorem packElements_concat (parts : List Bytes) :
    packElements parts = packBytes (concatParts parts) := by
  simp [packElements, foldl_append]

theorem concatParts_uint_size (k : Nat) (xs : List Std.U64) :
    (concatParts (xs.map fun x => uintBytes k x.val)).size = k * xs.length := by
  induction xs with
  | nil => simp [concatParts]
  | cons x rest ih =>
    simp [concatParts, uintBytes_size, ih, Nat.mul_succ]
    omega

/-! ## `Vec<u64>` -/

section Vec

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

/-- `basic_items_bytes` for `u64`: what the codec's `<u64 as SszEncode>::ssz_fixed_slice_to_vec`
writes, linked with its extraction. The theorem is the codec's. -/
theorem basic_items_bytes_u64.spec (items : Slice Std.U64) (hsz : 8 * items.length ≤ Usize.max) :
    basic_items_bytes U64.Insts.LibsszEncodeSszEncode items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun x => uintBytes 8 x.val) ⦄ := by
  unfold basic_items_bytes
  simp only [U64.Insts.LibsszEncodeSszEncode, U64.Insts.LibsszEncodeSszEncode.is_fixed_size,
    libssz_codec.U64.Insts.LibsszEncodeSszEncode.is_fixed_size, bind_ok, ↓reduceIte,
    U64.Insts.LibsszEncodeSszEncode.ssz_fixed_slice_to_vec]
  exact Libssz.Proofs.U64.fixed_slice_to_vec.spec items hsz

include hl in
/-- **`Vec<u64>`**: the `hash_tree_root` is the EthLib one for `List[uint64, len]`. -/
theorem VecU64.hash_tree_root.spec (v : alloc.vec.Vec Std.U64) (hsz : 8 * v.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root U64.Insts.Libssz_merkleHashTreeRoot
      U64.Insts.LibsszEncodeSszEncode inst v h ⦃ r =>
      hashTreeRoot (.list Desc.uint64 v.length) (.seq (v.val.map fun x => .uint x.val)) =
        .ok (bytes r.val) ⦄ := by
  unfold alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [U64.Insts.Libssz_merkleHashTreeRoot, U64.Insts.Libssz_merkleHashTreeRoot.is_basic_type,
    bind_ok, ↓reduceIte]
  have hl8 : 8 * v.length ≤ Usize.max := hsz
  set C := concatParts (v.val.map fun x => uintBytes 8 x.val) with hC
  apply WP.spec_bind (Pₘ := fun chunks : alloc.vec.Vec Node => chunksOf chunks.val = packBytes C)
  · step with basic_items_bytes_u64.spec v.deref (by simpa [alloc.vec.Vec.deref] using hl8)
      as ⟨ b, hb ⟩
    apply WP.spec_mono (pack.spec b.deref)
    intro c hc
    rw [hc]
    congr 1
    simpa [alloc.vec.Vec.deref] using hb
  · intro chunks hc
    have hCs : C.size = 8 * v.length := by rw [hC, concatParts_uint_size]
    step as ⟨ b1, hb1 ⟩
    apply WP.spec_bind (Pₘ := fun root : Node =>
      bytes root.val = subtreeAt (packBytes C) (depthFor (packBytes C).size) 0)
    · split
      · rename_i hbt
        have h0 : chunks.val = [] := by
          have : chunks.length = 0 := by rw [← hb1]; exact hbt
          exact List.eq_nil_of_length_eq_zero this
        step as ⟨ a, ha ⟩
        simp only [lift, bind_ok]
        step with merkleize.spec inst h hl _ none (by simp) as ⟨ root, hroot ⟩
        have hza := bytes_zero_hashes 0 (by omega) a ha
        have hp : packBytes C = #[] := by rw [← hc, h0]; rfl
        simp only [Option.map_none, merkleizeBounded_none] at hroot
        rw [hp, subtreeAt_past _ _ _ (by simp), zeroSubtree_eq, Array.size_empty, depthFor_zero]
        have hc1 : chunksOf (Array.make 1#usize [a] (by simp)).to_slice.val = #[bytes a.val] := by
          simp [chunksOf, Array.to_slice]
        rw [hc1] at hroot
        simp [depthFor_one, subtreeAt_leaf] at hroot
        rw [← hroot, hza]
      · rename_i hbf
        simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
        step with merkleize_in_place.spec inst h hl chunks.slice none (by simp)
          as ⟨ root1, rest, hroot, _ ⟩
        simp only [Option.map_none, merkleizeBounded_none] at hroot
        have hvs : (chunks.slice).val = chunks.val := rfl
        rw [hvs, hc] at hroot
        simp only [Except.ok.injEq] at hroot
        exact hroot.symm
    · intro root hroot
      step with mix_in_length.spec inst h hl root v.len as ⟨ r, hr ⟩
      have hser : serializeEach Desc.uint64 (v.val.map fun x => Value.uint x.val) =
          .ok (v.val.map fun x => uintBytes 8 x.val) := by
        rw [serializeEach_map _ _ (fun val => match val with | .uint n => uintBytes 8 n | _ => #[])
          (by
            intro val hval
            obtain ⟨ x, _, rfl ⟩ := List.mem_map.mp hval
            exact Libssz.Proofs.U64.ser x)]
        simp
      rw [hashTreeRoot_list_basic Desc.uint64 rfl rfl v.length _ _ (by simp) hser,
        packElements_concat, ← hC]
      have hcap : chunksForBytes (v.length * Desc.uint64.itemLength) = (packBytes C).size := by
        simp [chunksForBytes, packBytes, hCs, Desc.uint64, Desc.itemLength, bytesPerChunk]
        ring_nf
      rw [hcap, merkleizeBounded_some_self, merkleizeBounded_none]
      simp only [Except.map, List.length_map]
      rw [hr, hroot]
      simp

/-! ## `Vec<[u8; N]>` with `N ≤ 32` -/

/-- `basic_items_bytes` for `[u8; N]`: the arrays one after another. The default method
`ssz_fixed_slice_to_vec` is translated in this extraction; `ssz_append_fixed_slice` is the
codec's, linked. -/
theorem basic_items_bytes_u8n.spec (N : Std.Usize) (items : Slice (Std.Array Std.U8 N))
    (hsz : N.val * items.length ≤ Usize.max) :
    basic_items_bytes (ArrayU8N.Insts.LibsszEncodeSszEncode N) items ⦃ out =>
      bytes out.val = concatParts (items.val.map fun a => bytes a.val) ⦄ := by
  unfold basic_items_bytes
  simp only [ArrayU8N.Insts.LibsszEncodeSszEncode, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size,
    libssz_codec.ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, bind_ok, ↓reduceIte]
  simp only [ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size,
    libssz_codec.ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, bind_ok]
  step as ⟨ i2, hi2 ⟩
  simp only [ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice,
    libssz_codec.ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice]
  step as ⟨ plano, hplano, hplanol ⟩
  step as ⟨ buf', hbuf' ⟩
  · simp [alloc.vec.Vec.with_capacity]
  rw [hbuf']
  have hnil : (alloc.vec.Vec.with_capacity Std.U8 i2).val = [] := rfl
  rw [hnil, List.nil_append, hplano, Libssz.Proofs.bytes_flatten]

include hl in
/-- **The basic-item path of `Vec<T>`**, for any `T` that claims to be basic: the bytes built
by `basic_items_bytes`, in nodes (`pack`), merkleized without a limit, and the length mixed in
on the right. -/
theorem vec_basic_root {T : Type} (HI : HashTreeRoot T) (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok true) (v : alloc.vec.Vec T) (C : Bytes)
    (hbytes : basic_items_bytes EI v.deref ⦃ out => bytes out.val = C ⦄) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst v h ⦃ r =>
      bytes r.val = mixIn (subtreeAt (packBytes C) (depthFor (packBytes C).size) 0)
        (lengthWord v.length) ⦄ := by
  unfold alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [hbasic, bind_ok, ↓reduceIte]
  apply WP.spec_bind (Pₘ := fun chunks : alloc.vec.Vec Node => chunksOf chunks.val = packBytes C)
  · apply WP.spec_bind hbytes
    intro b hb
    apply WP.spec_mono (pack.spec b.deref)
    intro c hc
    rw [hc]
    congr 1
    simpa [alloc.vec.Vec.deref] using hb
  · intro chunks hc
    step as ⟨ b1, hb1 ⟩
    apply WP.spec_bind (Pₘ := fun root : Node =>
      bytes root.val = subtreeAt (packBytes C) (depthFor (packBytes C).size) 0)
    · split
      · rename_i hbt
        have h0 : chunks.val = [] := by
          have : chunks.length = 0 := by rw [← hb1]; exact hbt
          exact List.eq_nil_of_length_eq_zero this
        step as ⟨ a, ha ⟩
        simp only [lift, bind_ok]
        step with merkleize.spec inst h hl _ none (by simp) as ⟨ root, hroot ⟩
        have hza := bytes_zero_hashes 0 (by omega) a ha
        have hp : packBytes C = #[] := by rw [← hc, h0]; rfl
        simp only [Option.map_none, merkleizeBounded_none] at hroot
        rw [hp, subtreeAt_past _ _ _ (by simp), zeroSubtree_eq, Array.size_empty, depthFor_zero]
        have hc1 : chunksOf (Array.make 1#usize [a] (by simp)).to_slice.val = #[bytes a.val] := by
          simp [chunksOf, Array.to_slice]
        rw [hc1] at hroot
        simp [depthFor_one, subtreeAt_leaf] at hroot
        rw [← hroot, hza]
      · rename_i hbf
        simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
        step with merkleize_in_place.spec inst h hl chunks.slice none (by simp)
          as ⟨ root1, rest, hroot, _ ⟩
        simp only [Option.map_none, merkleizeBounded_none] at hroot
        have hvs : (chunks.slice).val = chunks.val := rfl
        rw [hvs, hc] at hroot
        simp only [Except.ok.injEq] at hroot
        exact hroot.symm
    · intro root hroot
      step with mix_in_length.spec inst h hl root v.len as ⟨ r, hr ⟩
      rw [hr, hroot]
      simp

/-- A `[u8; 4]` as EthLib bytes, padded with zeros to one node. -/
def pad4 (l : Bytes) : Bytes := l ++ Array.replicate 28 0

include hl in
/-- **Here libssz does not match the specification.** For the list of two `[u8; 4]`
`[1, 2, 3, 4]` and `[5, 6, 7, 8]`, the `hash_tree_root` of `Vec<[u8; 4]>` is not EthLib's
`hashTreeRoot` for `List[Bytes4, 2]`, for any hasher that satisfies the specification.
libssz treats `[u8; N]` with `N ≤ 32` as a basic type and packs the eight bytes into a single
node; the specification uses one node per item. See the divergences in `README.md`. -/
theorem VecU8x4.diverges (v : alloc.vec.Vec (Std.Array Std.U8 4#usize))
    (hv : v.val.map (fun a => bytes a.val) = [#[1, 2, 3, 4], #[5, 6, 7, 8]]) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (ArrayU8N.Insts.Libssz_merkleHashTreeRoot 4#usize)
      (ArrayU8N.Insts.LibsszEncodeSszEncode 4#usize) inst v h ⦃ r =>
      hashTreeRoot (.list (.byteVector 4) v.length) (.seq (v.val.map fun a => .bytes (bytes a.val)))
        ≠ .ok (bytes r.val) ⦄ := by
  have hlen : v.length = 2 := by
    have := congrArg List.length hv; simpa using this
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  have hC : concatParts (v.deref.val.map fun a => bytes a.val) = #[1, 2, 3, 4, 5, 6, 7, 8] := by
    rw [hd, hv]; rfl
  apply WP.spec_mono (vec_basic_root inst h hl (ArrayU8N.Insts.Libssz_merkleHashTreeRoot 4#usize)
    (ArrayU8N.Insts.LibsszEncodeSszEncode 4#usize) (by rfl) v _
    (WP.spec_mono (basic_items_bytes_u8n.spec 4#usize v.deref (by
      simp [alloc.vec.Vec.deref]; scalar_tac)) (fun out hout => hout.trans hC)))
  intro r hr
  rw [hr, hlen]
  have hvals : v.val.map (fun a => Value.bytes (bytes a.val)) =
      [.bytes #[1, 2, 3, 4], .bytes #[5, 6, 7, 8]] := by
    have := congrArg (List.map Value.bytes) hv
    simpa [List.map_map, Function.comp_def] using this
  rw [hvals, hashTreeRoot_list_composite (.byteVector 4) rfl 2 _ [pad4 #[1, 2, 3, 4],
    pad4 #[5, 6, 7, 8]] (by simp) (by
      simp only [List.mapM_cons, List.mapM_nil]
      rw [show (4 : Nat) = (#[(1 : UInt8), 2, 3, 4] : Bytes).size from rfl, hashTreeRoot_byteVector,
        show (#[(1 : UInt8), 2, 3, 4] : Bytes).size = (#[(5 : UInt8), 6, 7, 8] : Bytes).size from rfl,
        hashTreeRoot_byteVector]
      simp only [packBytes_one #[(1 : UInt8), 2, 3, 4] (by decide) (by decide),
        packBytes_one #[(5 : UInt8), 6, 7, 8] (by decide) (by decide)]
      simp [depthFor_one, subtreeAt_leaf, pad4, Bind.bind, Except.bind, Pure.pure,
        Except.pure])]
  rw [show (2 : Nat) = (#[pad4 #[1, 2, 3, 4], pad4 #[5, 6, 7, 8]] : Array Bytes).size from rfl,
    merkleizeBounded_some_self, merkleizeBounded_none]
  simp only [Except.map, ne_eq, Except.ok.injEq]
  decide +kernel

end Vec

end Libssz.Merkle
