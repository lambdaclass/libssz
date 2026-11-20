module
public import Libssz.SszTypes.Code.Funs
public import Libssz.Merkle.Proofs.Composite
@[expose] public section

/-!
# The `hash_tree_root` of `SszList` and `SszVector`

`SszList<T, N>` and `SszVector<T, N>` (crate `ssz-types`) store their items in a `Vec<T>`. Their
`hash_tree_root` is that of `Vec<T>` with two differences:

* the tree has the capacity given by the type: `N` nodes for composite items, and
  `⌈N · size / 32⌉` for packed basic items;
* `SszVector` does not mix in the length.

This extraction is linked with those of the tree and the codec (see
`scripts/complete_externals_types.py`): `merkleize_in_place`, `pack`, `mix_in_length` and the
items' `hash_tree_root` are those of the tree extraction, with their theorems.
-/

open Aeneas Aeneas.Std Result
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz
open Libssz.Merkle

namespace Libssz.SszTypes

/-! ## EthLib: the root of a vector -/

/-- **The root of a vector of basic items** according to EthLib: the tree of the packed items,
with the capacity given by the length. Nothing is mixed in. -/
theorem hashTreeRoot_vector_basic (elem : Desc) (hb : elem.isBasic = true)
    (hn : elem.nesting = 1) (n : Nat) (values : List Value) (parts : List Bytes)
    (hl : values.length = n) (hser : serializeEach elem values = .ok parts) :
    hashTreeRoot (.vector elem n) (.seq values) =
      merkleizeBoundedUnchecked (packElements parts) (some (chunksForBytes (n * elem.itemLength))) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.vector elem n).nesting = 1 + 1 by
    simp [Desc.nesting, hn], hashTreeRootAt_succ]
  have hlay : merkleLayout (.vector elem n) (.seq values) =
      .ok (MerkleLayout.packing (packElements parts)
        (some (chunksForBytes (n * elem.itemLength))) none) := by
    simp [merkleLayout, sequenceLayout, hb, hser, hl, Pure.pure, Except.pure,
      Bind.bind, Except.bind]
  simp only [hlay, Bind.bind, Except.bind]
  simp only [layoutChunksAt_eq, MerkleLayout.packing, Leaves.count, Option.getD_none,
    Array.extract_size]
  cases hm : merkleizeBoundedUnchecked (packElements parts)
    (some (chunksForBytes (n * elem.itemLength))) <;>
    simp [hm, Pure.pure, Except.pure]

/-- **The root of a vector of composite items** according to EthLib: the tree of the item
roots, with capacity equal to the length. Nothing is mixed in. -/
theorem hashTreeRoot_vector_composite (elem : Desc) (hb : elem.isBasic = false) (n : Nat)
    (values : List Value) (roots : List Bytes) (hl : values.length = n)
    (hroots : values.mapM (hashTreeRoot elem) = .ok roots) :
    hashTreeRoot (.vector elem n) (.seq values) =
      merkleizeBoundedUnchecked roots.toArray (some n) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.vector elem n).nesting = elem.nesting + 1 from rfl,
    hashTreeRootAt_succ]
  have hlay : merkleLayout (.vector elem n) (.seq values) =
      .ok (MerkleLayout.nesting (values.map fun v => some (elem, v)) (some n) none) := by
    simp [merkleLayout, sequenceLayout, hb, hl, Pure.pure, Except.pure]
  have hchunks : layoutChunksAt elem.nesting
      (MerkleLayout.nesting (values.map fun v => some (elem, v)) (some n) none) =
        .ok roots.toArray := by
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
  cases merkleizeBoundedUnchecked roots.toArray (some n) <;>
    simp [Pure.pure, Except.pure]

/-! ## EthLib: 32-byte items -/

theorem concatParts_size32 (xs : List Bytes) (hx : ∀ x ∈ xs, x.size = 32) :
    (concatParts xs).size = 32 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x r ih =>
    simp only [concatParts, Array.size_append, hx x (by simp),
      ih (fun y hy => hx y (by simp [hy])), List.length_cons]
    omega

/-- Packing 32-byte items one after another gives one node per item. -/
theorem packBytes_concat32 (xs : List Bytes) (hx : ∀ x ∈ xs, x.size = 32) :
    packBytes (concatParts xs) = xs.toArray := by
  have hsize := concatParts_size32 xs hx
  apply Array.ext
  · rw [packBytes_size, hsize]; simp [bytesPerChunk]; omega
  · intro i hi1 hi2
    have hi : i < xs.length := by simpa using hi2
    have he := extract_concatParts 32 xs hx i hi
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at he
    simp only [packBytes, Array.getElem_ofFn, List.getElem_toArray]
    have hb : bytesPerChunk = 32 := rfl
    simp only [hb, show i * 32 + 32 = (i + 1) * 32 by ring, he, hx _ (List.getElem_mem hi),
      Nat.sub_self, Array.replicate_zero, Array.append_empty]

/-- The EthLib root of a `Bytes32` is itself. -/
theorem hashTreeRoot_bytes32 (a : Bytes) (ha : a.size = 32) :
    hashTreeRoot (.byteVector 32) (.bytes a) = .ok a := by
  rw [show (32 : Nat) = a.size from ha.symm, hashTreeRoot_byteVector,
    packBytes_one a (by omega) (by omega)]
  simp [depthFor_one, subtreeAt_leaf, ha]

theorem mapM_bytes32 (xs : List Bytes) (hx : ∀ x ∈ xs, x.size = 32) :
    (xs.map Value.bytes).mapM (hashTreeRoot (.byteVector 32)) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x r ih =>
    simp only [List.map_cons, List.mapM_cons, hashTreeRoot_bytes32 x (hx x (by simp)),
      ih (fun y hy => hx y (by simp [hy]))]
    rfl

/-! ## The bytes of basic items -/

/-- `basic_items_bytes` in `ssz-types` is a copy of the one in `ssz-merkle`. For fixed-size
items, both are `ssz_fixed_slice_to_vec`. -/
theorem basic_items_bytes_eq {T : Type} (EI : libssz_codec.encode.SszEncode T)
    (hf : EI.is_fixed_size = ok true) (s : Slice T) :
    libssz_types.hash_tree_root.basic_items_bytes EI s = libssz_merkle.basic_items_bytes EI s := by
  unfold libssz_types.hash_tree_root.basic_items_bytes libssz_merkle.basic_items_bytes
  simp only [hf, bind_ok, ↓reduceIte]

/-! ## `SszList` and `SszVector` with composite items -/

section Roots

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

/-- What `hash_tree_roots` leaves in a `Vec` of zeros as long as the list: one node per item,
the item's EthLib root. -/
theorem roots_forall₂ {T : Type} (elem : Desc) (val : T → Value) (items : alloc.vec.Vec T)
    (roots : alloc.vec.Vec Node) (s2 : Slice Node)
    (hrl' : roots.slice.length = items.slice.length) (hs2len : s2.length = roots.slice.length)
    (hs2 : ∀ t < (alloc.vec.Vec.deref items).length, ∀ x,
      (alloc.vec.Vec.deref items).val[t]? = some x →
        ∃ r, s2.val[t]? = some r ∧ hashTreeRoot elem (val x) = .ok (bytes r.val)) :
    List.Forall₂ (fun x r => hashTreeRoot elem (val x) = .ok (bytes r.val)) items.val
      ({ slice := s2 } : alloc.vec.Vec Node).val := by
  have hd : (alloc.vec.Vec.deref items).val = items.val := by simp [alloc.vec.Vec.deref]
  apply forall₂_of_getElem?
  · show s2.val.length = items.slice.val.length
    have h1 : s2.length = roots.slice.length := hs2len
    simp only [Slice.length] at h1 hrl'
    rw [h1, hrl']
  · intro t ht x hx
    exact hs2 t (by simpa [alloc.vec.Vec.deref] using ht) x (by rw [hd]; exact hx)

include hl in
/-- **The `hash_tree_root` of `SszList<T, N>` for composite items**: if `T` says it is not
basic, and its rows give the EthLib root for the (non-basic) descriptor `elem` on the items
that satisfy `good`, the list's root is the EthLib root for `List[elem, N]`. It requires what
the type guarantees: that the list has no more than `N` items, and that each item satisfies
its invariant. The item's `SszEncode` is not used. -/
theorem SszList.composite_root {T : Type} {N : Std.Usize} (HI : libssz_merkle.HashTreeRoot T)
    (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok false) (elem : Desc) (helem : elem.isBasic = false)
    (val : T → Value) (good : T → Prop) (d : Nat) (hrows : Rows inst h HI elem val good d)
    (l : libssz_types.list.SszList T N) (hlen : l.length ≤ N.val)
    (hgood : ∀ x ∈ l.val, good x) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst l h ⦃ r =>
      hashTreeRoot (.list elem N.val) (.seq (l.val.map val)) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.list.SszList.len, bind_ok, hbasic, Bool.false_eq_true, ↓reduceIte,
    libssz_types.list.SszList.Insts.CoreOpsDerefDerefSlice.deref, lift, alloc.vec.Vec.deref_mut,
    libssz_types.libssz_merkle.merkleize_in_place, libssz_types.libssz_merkle.mix_in_length,
    libssz_types.libssz_merkle.hash_tree_roots]
  step with alloc.vec.from_elem_spec _ _ _ (clone_node _) as ⟨ roots, hrv, hrl ⟩
  have hd : (alloc.vec.Vec.deref l).val = l.val := by simp [alloc.vec.Vec.deref]
  have hrl' : roots.slice.length = l.slice.length := by
    have e2 : roots.slice.length = roots.length := rfl
    rw [e2, hrl]
    simp
    rfl
  step with hash_tree_roots.spec inst h hl HI elem val good d hrows (alloc.vec.Vec.deref l)
    (by rw [hd]; exact hgood) roots.slice (by
      have : (alloc.vec.Vec.deref l).length = l.slice.length := by
        simp [alloc.vec.Vec.deref, Slice.length]
        rfl
      omega)
    as ⟨ s2, hs2len, hs2, _ ⟩
  have hF := roots_forall₂ elem val l roots s2 hrl' hs2len hs2
  set chunks : alloc.vec.Vec Node := { slice := s2 } with hchunks
  have hroots := mapM_of_forall₂ elem val l.val chunks.val hF
  have hlen' : chunks.val.length = l.val.length := hF.length_eq.symm
  step with merkleize_in_place.spec inst h hl chunks.slice (some N) (by
      intro n hn; simp only [Option.some.injEq] at hn; subst hn
      show chunks.val.length ≤ _; rw [hlen']; exact hlen)
    as ⟨ root, rest, hroot, _ ⟩
  step with mix_in_length.spec inst h hl root (alloc.vec.Vec.len l) as ⟨ r, hr ⟩
  rw [hashTreeRoot_list_composite elem helem N.val _ _ (by simpa using hlen) hroots]
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs] at hroot
  simp only [Option.map_some] at hroot
  have hXe : (chunks.val.map fun r => bytes r.val).toArray = chunksOf chunks.val := rfl
  rw [hXe, hroot]
  simp only [Except.map, List.length_map, hr]
  have e1 : (alloc.vec.Vec.len l).val = l.val.length := by simp
  rw [e1]

include hl in
/-- **The `hash_tree_root` of `SszVector<T, N>` for composite items**: the EthLib root for
`Vector[elem, N]`. It requires what the type guarantees: that the vector has exactly `N` items,
and that each item satisfies its invariant. -/
theorem SszVector.composite_root {T : Type} {N : Std.Usize} (HI : libssz_merkle.HashTreeRoot T)
    (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok false) (elem : Desc) (helem : elem.isBasic = false)
    (val : T → Value) (good : T → Prop) (d : Nat) (hrows : Rows inst h HI elem val good d)
    (v : libssz_types.vector.SszVector T N) (hlen : v.length = N.val)
    (hgood : ∀ x ∈ v.val, good x) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst v h ⦃ r =>
      hashTreeRoot (.vector elem N.val) (.seq (v.val.map val)) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [bind_ok, hbasic, Bool.false_eq_true, ↓reduceIte,
    libssz_types.vector.SszVector.Insts.CoreOpsDerefDerefSlice.deref, lift,
    alloc.vec.Vec.deref_mut, libssz_types.libssz_merkle.merkleize_in_place,
    libssz_types.libssz_merkle.hash_tree_roots, libssz_types.vector.SszVector.len]
  step with alloc.vec.from_elem_spec _ _ _ (clone_node _) as ⟨ roots, hrv, hrl ⟩
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  have hrl' : roots.slice.length = v.slice.length := by
    have e2 : roots.slice.length = roots.length := rfl
    rw [e2, hrl]
    exact hlen.symm
  step with hash_tree_roots.spec inst h hl HI elem val good d hrows (alloc.vec.Vec.deref v)
    (by rw [hd]; exact hgood) roots.slice (by
      have : (alloc.vec.Vec.deref v).length = v.slice.length := by
        simp [alloc.vec.Vec.deref, Slice.length]
        rfl
      omega)
    as ⟨ s2, hs2len, hs2, _ ⟩
  have hF := roots_forall₂ elem val v roots s2 hrl' hs2len hs2
  set chunks : alloc.vec.Vec Node := { slice := s2 } with hchunks
  have hroots := mapM_of_forall₂ elem val v.val chunks.val hF
  have hlen' : chunks.val.length = v.val.length := hF.length_eq.symm
  step with merkleize_in_place.spec inst h hl chunks.slice (some N) (by
      intro n hn; simp only [Option.some.injEq] at hn; subst hn
      show chunks.val.length ≤ _; rw [hlen']; exact le_of_eq hlen)
    as ⟨ root, rest, hroot, _ ⟩
  rw [hashTreeRoot_vector_composite elem helem N.val _ _ (by simpa using hlen) hroots]
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs] at hroot
  simp only [Option.map_some] at hroot
  have hXe : (chunks.val.map fun r => bytes r.val).toArray = chunksOf chunks.val := rfl
  rw [hXe, hroot]

/-! ## `SszList` and `SszVector` with basic items -/

/-- The nodes `pack` produces do not exceed the capacity if the bytes do not exceed `N · k`. -/
theorem pack_le_cap (chunks : alloc.vec.Vec Node) (C : Bytes) (hc : chunksOf chunks.val = packBytes C)
    (cap : Nat) (hC : C.size ≤ cap) : chunks.val.length ≤ chunksForBytes cap := by
  have h1 : (chunksOf chunks.val).size = chunks.val.length := chunksOf_size _
  rw [← h1, hc, packBytes_size]
  simp only [chunksForBytes]
  exact Nat.div_le_div_right (by omega)

include hl in
/-- **The basic-item path of `SszList<T, N>`**, for any `T` that says it is basic and has
fixed size `k`: the bytes built by `basic_items_bytes`, as nodes, merkleized with capacity
`⌈N · k / 32⌉` nodes, and the length mixed in on the right. -/
theorem SszList.basic_rust {T : Type} {N : Std.Usize} (HI : libssz_merkle.HashTreeRoot T)
    (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok true) (k : Std.Usize) (hk : EI.fixed_size = ok k)
    (l : libssz_types.list.SszList T N) (C : Bytes)
    (hbytes : libssz_types.hash_tree_root.basic_items_bytes EI (alloc.vec.Vec.deref l)
      ⦃ out => bytes out.val = C ⦄)
    (hcap : N.val * k.val ≤ Usize.max) (hC : C.size ≤ N.val * k.val) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst l h ⦃ r =>
      (merkleizeBoundedUnchecked (packBytes C) (some (chunksForBytes (N.val * k.val)))).map
        (fun root => mixIn root (lengthWord l.length)) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.list.SszList.len, bind_ok, hbasic, ↓reduceIte,
    libssz_types.list.SszList.Insts.CoreOpsDerefDerefSlice.deref]
  apply WP.spec_bind hbytes
  intro b hb
  simp only [libssz_types.libssz_merkle.pack, libssz_types.libssz_merkle.merkleize_in_place,
    libssz_types.libssz_merkle.mix_in_length]
  apply WP.spec_bind (pack.spec b.deref)
  intro chunks hc
  have hc' : chunksOf chunks.val = packBytes C := by
    rw [hc]; congr 1; simpa [alloc.vec.Vec.deref] using hb
  simp only [hk, bind_ok]
  step as ⟨ i1, hi1 ⟩
  step as ⟨ cap, hcapv ⟩
  have hcap' : cap.val = chunksForBytes (N.val * k.val) := by
    rw [hcapv, hi1, Nat.ceilDiv_eq_add_pred_div]; rfl
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step with merkleize_in_place.spec inst h hl chunks.slice (some cap) (by
      intro n hn; simp only [Option.some.injEq] at hn; subst hn
      show chunks.val.length ≤ _; rw [hcap']; exact pack_le_cap chunks C hc' _ hC)
    as ⟨ root, rest, hroot, _ ⟩
  step with mix_in_length.spec inst h hl root (alloc.vec.Vec.len l) as ⟨ r, hr ⟩
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs, hc'] at hroot
  simp only [Option.map_some, hcap'] at hroot
  rw [hroot]
  simp only [Except.map, hr]
  have e1 : (alloc.vec.Vec.len l).val = l.val.length := by simp
  rw [e1]

include hl in
/-- **The basic-item path of `SszVector<T, N>`**: the same, without mixing in the length. -/
theorem SszVector.basic_rust {T : Type} {N : Std.Usize} (HI : libssz_merkle.HashTreeRoot T)
    (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok true) (k : Std.Usize) (hk : EI.fixed_size = ok k)
    (v : libssz_types.vector.SszVector T N) (C : Bytes)
    (hbytes : libssz_types.hash_tree_root.basic_items_bytes EI (alloc.vec.Vec.deref v)
      ⦃ out => bytes out.val = C ⦄)
    (hcap : N.val * k.val ≤ Usize.max) (hC : C.size ≤ N.val * k.val) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst v h ⦃ r =>
      merkleizeBoundedUnchecked (packBytes C) (some (chunksForBytes (N.val * k.val))) =
        .ok (bytes r.val) ⦄ := by
  unfold libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [bind_ok, hbasic, ↓reduceIte,
    libssz_types.vector.SszVector.Insts.CoreOpsDerefDerefSlice.deref]
  apply WP.spec_bind hbytes
  intro b hb
  simp only [libssz_types.libssz_merkle.pack, libssz_types.libssz_merkle.merkleize_in_place]
  apply WP.spec_bind (pack.spec b.deref)
  intro chunks hc
  have hc' : chunksOf chunks.val = packBytes C := by
    rw [hc]; congr 1; simpa [alloc.vec.Vec.deref] using hb
  simp only [hk, bind_ok]
  step as ⟨ i1, hi1 ⟩
  step as ⟨ cap, hcapv ⟩
  have hcap' : cap.val = chunksForBytes (N.val * k.val) := by
    rw [hcapv, hi1, Nat.ceilDiv_eq_add_pred_div]; rfl
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  step with merkleize_in_place.spec inst h hl chunks.slice (some cap) (by
      intro n hn; simp only [Option.some.injEq] at hn; subst hn
      show chunks.val.length ≤ _; rw [hcap']; exact pack_le_cap chunks C hc' _ hC)
    as ⟨ root, rest, hroot, _ ⟩
  have hvs : (chunks.slice).val = chunks.val := rfl
  rw [hvs, hc'] at hroot
  simp only [Option.map_some, hcap'] at hroot
  exact hroot

/-! ## Concrete items -/

theorem serializeEach_u64 (xs : List Std.U64) :
    serializeEach Desc.uint64 (xs.map fun x => Value.uint x.val) =
      .ok (xs.map fun x => uintBytes 8 x.val) := by
  rw [serializeEach_map _ _ (fun val => match val with | .uint n => uintBytes 8 n | _ => #[])
    (by
      intro val hval
      obtain ⟨ x, _, rfl ⟩ := List.mem_map.mp hval
      exact Libssz.Proofs.U64.ser x)]
  simp

theorem bytes_size32 (a : Std.Array Std.U8 32#usize) : (bytes a.val).size = 32 := by
  simp [bytes]

include hl in
/-- **`SszList<u64, N>`** (for example `attesting_indices`): the `hash_tree_root` is EthLib's
for `List[uint64, N]`. It requires that the list has at most `N` items (the type guarantees
it) and that `8 · N` fits in a `usize` (the Rust code computes `N * 8` and panics if it does not
fit). -/
theorem SszListU64.hash_tree_root.spec {N : Std.Usize} (l : libssz_types.list.SszList Std.U64 N)
    (hlen : l.length ≤ N.val) (hcap : 8 * N.val ≤ Usize.max) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      libssz_types.U64.Insts.Libssz_merkleHashTreeRoot
      libssz_types.U64.Insts.LibsszEncodeSszEncode inst l h ⦃ r =>
      hashTreeRoot (.list Desc.uint64 N.val) (.seq (l.val.map fun x => .uint x.val)) =
        .ok (bytes r.val) ⦄ := by
  set C := concatParts (l.val.map fun x => uintBytes 8 x.val) with hC
  have hCs : C.size = 8 * l.length := by rw [hC, concatParts_uint_size]
  have h8 : (8#usize : Std.Usize).val = 8 := rfl
  apply WP.spec_mono (SszList.basic_rust inst h hl _ _ rfl 8#usize rfl l C ?_
    (by rw [h8]; omega) (by rw [hCs, h8]; have := hlen; nlinarith))
  · intro r hr
    rw [hashTreeRoot_list_basic Desc.uint64 rfl rfl N.val _ _ (by simpa using hlen)
      (serializeEach_u64 l.val), packElements_concat, ← hC, List.length_map]
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    have : alloc.vec.Vec.length l = (l.val).length := rfl
    apply WP.spec_mono (basic_items_bytes_u64.spec (alloc.vec.Vec.deref l)
      (by simp [alloc.vec.Vec.deref]; omega))
    intro out hout
    rw [hout, hC]
    simp [alloc.vec.Vec.deref]

include hl in
/-- **`SszVector<u64, N>`** (for example `slashings`): EthLib's for `Vector[uint64, N]`. -/
theorem SszVectorU64.hash_tree_root.spec {N : Std.Usize}
    (v : libssz_types.vector.SszVector Std.U64 N)
    (hlen : v.length = N.val) (hcap : 8 * N.val ≤ Usize.max) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      libssz_types.U64.Insts.Libssz_merkleHashTreeRoot
      libssz_types.U64.Insts.LibsszEncodeSszEncode inst v h ⦃ r =>
      hashTreeRoot (.vector Desc.uint64 N.val) (.seq (v.val.map fun x => .uint x.val)) =
        .ok (bytes r.val) ⦄ := by
  set C := concatParts (v.val.map fun x => uintBytes 8 x.val) with hC
  have hCs : C.size = 8 * v.length := by rw [hC, concatParts_uint_size]
  have h8 : (8#usize : Std.Usize).val = 8 := rfl
  apply WP.spec_mono (SszVector.basic_rust inst h hl _ _ rfl 8#usize rfl v C ?_
    (by rw [h8]; omega) (by rw [hCs, h8, hlen]; omega))
  · intro r hr
    rw [hashTreeRoot_vector_basic Desc.uint64 rfl rfl N.val _ _ (by simpa using hlen)
      (serializeEach_u64 v.val), packElements_concat, ← hC]
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    have : alloc.vec.Vec.length v = (v.val).length := rfl
    apply WP.spec_mono (basic_items_bytes_u64.spec (alloc.vec.Vec.deref v)
      (by simp [alloc.vec.Vec.deref]; omega))
    intro out hout
    rw [hout, hC]
    simp [alloc.vec.Vec.deref]

theorem bytes_map_size32 (xs : List (Std.Array Std.U8 32#usize)) :
    ∀ x ∈ xs.map (fun a => bytes a.val), x.size = 32 := by
  intro x hx
  obtain ⟨ a, _, rfl ⟩ := List.mem_map.mp hx
  exact bytes_size32 a

include hl in
/-- **`SszList<[u8; 32], N>`** (for example `historical_roots`): EthLib's for
`List[Bytes32, N]`. libssz treats `[u8; 32]` as basic and packs the items; EthLib treats it as
composite, with one node per item. With 32 bytes per item, both trees are the same. -/
theorem SszListBytes32.hash_tree_root.spec {N : Std.Usize}
    (l : libssz_types.list.SszList (Std.Array Std.U8 32#usize) N)
    (hlen : l.length ≤ N.val) (hcap : 32 * N.val ≤ Usize.max) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot 32#usize)
      (libssz_types.ArrayU8N.Insts.LibsszEncodeSszEncode 32#usize) inst l h ⦃ r =>
      hashTreeRoot (.list (.byteVector 32) N.val) (.seq (l.val.map fun a => .bytes (bytes a.val))) =
        .ok (bytes r.val) ⦄ := by
  set xs := l.val.map fun a => bytes a.val with hxs
  have hx := bytes_map_size32 l.val
  have hCs : (concatParts xs).size = 32 * l.length := by
    rw [concatParts_size32 xs hx, hxs, List.length_map]
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  have hlv : alloc.vec.Vec.length l = (l.val).length := rfl
  apply WP.spec_mono (SszList.basic_rust inst h hl _ _ rfl 32#usize rfl l (concatParts xs) ?_
    (by rw [h32]; omega) (by rw [hCs, h32]; omega))
  · intro r hr
    have hvals : (l.val.map fun a => Value.bytes (bytes a.val)) = xs.map Value.bytes := by
      rw [hxs, List.map_map]; rfl
    rw [hvals, hashTreeRoot_list_composite (.byteVector 32) rfl N.val _ xs
      (by rw [List.length_map, hxs, List.length_map]; omega) (mapM_bytes32 xs hx)]
    rw [packBytes_concat32 xs hx, h32,
      show chunksForBytes (N.val * 32) = N.val by simp [chunksForBytes, bytesPerChunk]; omega] at hr
    rw [List.length_map, hxs, List.length_map]
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    apply WP.spec_mono (basic_items_bytes_u8n.spec 32#usize (alloc.vec.Vec.deref l)
      (by simp [alloc.vec.Vec.deref]; omega))
    intro out hout
    rw [hout, hxs]
    simp [alloc.vec.Vec.deref]

include hl in
/-- **`SszVector<[u8; 32], N>`** (for example `block_roots`): EthLib's for
`Vector[Bytes32, N]`. -/
theorem SszVectorBytes32.hash_tree_root.spec {N : Std.Usize}
    (v : libssz_types.vector.SszVector (Std.Array Std.U8 32#usize) N)
    (hlen : v.length = N.val) (hcap : 32 * N.val ≤ Usize.max) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot 32#usize)
      (libssz_types.ArrayU8N.Insts.LibsszEncodeSszEncode 32#usize) inst v h ⦃ r =>
      hashTreeRoot (.vector (.byteVector 32) N.val) (.seq (v.val.map fun a => .bytes (bytes a.val))) =
        .ok (bytes r.val) ⦄ := by
  set xs := v.val.map fun a => bytes a.val with hxs
  have hx := bytes_map_size32 v.val
  have hCs : (concatParts xs).size = 32 * v.length := by
    rw [concatParts_size32 xs hx, hxs, List.length_map]
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  have hlv : alloc.vec.Vec.length v = (v.val).length := rfl
  apply WP.spec_mono (SszVector.basic_rust inst h hl _ _ rfl 32#usize rfl v (concatParts xs) ?_
    (by rw [h32]; omega) (by rw [hCs, h32]; omega))
  · intro r hr
    have hvals : (v.val.map fun a => Value.bytes (bytes a.val)) = xs.map Value.bytes := by
      rw [hxs, List.map_map]; rfl
    rw [hvals, hashTreeRoot_vector_composite (.byteVector 32) rfl N.val _ xs
      (by rw [List.length_map, hxs, List.length_map]; omega) (mapM_bytes32 xs hx)]
    rw [packBytes_concat32 xs hx, h32,
      show chunksForBytes (N.val * 32) = N.val by simp [chunksForBytes, bytesPerChunk]; omega] at hr
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    apply WP.spec_mono (basic_items_bytes_u8n.spec 32#usize (alloc.vec.Vec.deref v)
      (by simp [alloc.vec.Vec.deref]; omega))
    intro out hout
    rw [hout, hxs]
    simp [alloc.vec.Vec.deref]

theorem u8n_not_basic {M : Std.Usize} (hM : 32 < M.val) :
    (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot M).is_basic_type = ok false := by
  simp only [libssz_merkle.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.is_basic_type]
  have : ¬ (M ≤ 32#usize) := by scalar_tac
  simp [this]

include hl in
/-- **`SszList<[u8; M], N>` with `M > 32`** (public keys, signatures): EthLib's for
`List[ByteVector[M], N]`. -/
theorem SszListU8N.hash_tree_root.spec {M N : Std.Usize} (hM : 32 < M.val)
    (l : libssz_types.list.SszList (Std.Array Std.U8 M) N) (hlen : l.length ≤ N.val) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot M)
      (libssz_types.ArrayU8N.Insts.LibsszEncodeSszEncode M) inst l h ⦃ r =>
      hashTreeRoot (.list (.byteVector M.val) N.val) (.seq (l.val.map fun a => .bytes (bytes a.val))) =
        .ok (bytes r.val) ⦄ :=
  SszList.composite_root inst h hl _ _ (u8n_not_basic hM) (.byteVector M.val) rfl _ _ 0
    (ArrayU8N.rows inst h hl) l hlen (fun _ _ => trivial)

include hl in
/-- **`SszVector<[u8; M], N>` with `M > 32`** (for example `pubkeys` of `SyncCommittee`):
EthLib's for `Vector[ByteVector[M], N]`. -/
theorem SszVectorU8N.hash_tree_root.spec {M N : Std.Usize} (hM : 32 < M.val)
    (v : libssz_types.vector.SszVector (Std.Array Std.U8 M) N) (hlen : v.length = N.val) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot M)
      (libssz_types.ArrayU8N.Insts.LibsszEncodeSszEncode M) inst v h ⦃ r =>
      hashTreeRoot (.vector (.byteVector M.val) N.val) (.seq (v.val.map fun a => .bytes (bytes a.val))) =
        .ok (bytes r.val) ⦄ :=
  SszVector.composite_root inst h hl _ _ (u8n_not_basic hM) (.byteVector M.val) rfl _ _ 0
    (ArrayU8N.rows inst h hl) v hlen (fun _ _ => trivial)

include hl in
/-- **`SszList<Validator, N>`** (the `validators` field of `BeaconState`): EthLib's for
`List[Validator, N]`, for any `SszEncode` implementation (the composite-item path does not use
it; see `VecValidator.hash_tree_root.spec`). It holds for every `N`; the mainnet one, 2^40, is a
`usize` only if `usize` has 64 bits, and the Aeneas model does not fix that. -/
theorem SszListValidator.hash_tree_root.spec {N : Std.Usize}
    (EI : libssz_codec.encode.SszEncode libssz_merkle.verif_example.Validator)
    (l : libssz_types.list.SszList libssz_merkle.verif_example.Validator N)
    (hlen : l.length ≤ N.val) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      libssz_merkle.verif_example.Validator.Insts.Libssz_merkleHashTreeRoot EI inst l h ⦃ r =>
      hashTreeRoot (.list (.container Proofs.valNames Proofs.valFields) N.val)
        (.seq (l.val.map valV)) = .ok (bytes r.val) ⦄ :=
  SszList.composite_root inst h hl _ EI rfl _ rfl valV _ 3 (Validator.rows inst h hl)
    l hlen (fun _ _ => trivial)

include hl in
/-- **Here libssz does not match the specification** (see `README.md`): for the vector of the two
`[u8; 4]` `[1, 2, 3, 4]` and `[5, 6, 7, 8]`, the `hash_tree_root` of `SszVector<[u8; 4], 2>` is not
EthLib's `hashTreeRoot` for `Vector[Bytes4, 2]`, with any hasher that meets the specification.
libssz packs the eight bytes into one node, which is the root; the specification uses one node per
item and hashes the two. -/
theorem SszVectorU8x4.diverges
    (v : libssz_types.vector.SszVector (Std.Array Std.U8 4#usize) 2#usize)
    (hv : v.val.map (fun a => bytes a.val) = [#[1, 2, 3, 4], #[5, 6, 7, 8]]) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot 4#usize)
      (libssz_types.ArrayU8N.Insts.LibsszEncodeSszEncode 4#usize) inst v h ⦃ r =>
      hashTreeRoot (.vector (.byteVector 4) 2) (.seq (v.val.map fun a => .bytes (bytes a.val)))
        ≠ .ok (bytes r.val) ⦄ := by
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  have hlen : v.val.length = 2 := by
    have := congrArg List.length hv; simpa using this
  apply WP.spec_mono (SszVector.basic_rust inst h hl _ _ rfl 4#usize rfl v
    #[1, 2, 3, 4, 5, 6, 7, 8] ?_ (by scalar_tac) (by decide))
  · intro r hr
    have hvals : v.val.map (fun a => Value.bytes (bytes a.val)) =
        [.bytes #[1, 2, 3, 4], .bytes #[5, 6, 7, 8]] := by
      have := congrArg (List.map Value.bytes) hv
      simpa [List.map_map, Function.comp_def] using this
    rw [hvals, hashTreeRoot_vector_composite (.byteVector 4) rfl 2 _ [pad4 #[1, 2, 3, 4],
      pad4 #[5, 6, 7, 8]] rfl (by
        simp only [List.mapM_cons, List.mapM_nil]
        rw [show (4 : Nat) = (#[(1 : UInt8), 2, 3, 4] : Bytes).size from rfl,
          hashTreeRoot_byteVector,
          show (#[(1 : UInt8), 2, 3, 4] : Bytes).size = (#[(5 : UInt8), 6, 7, 8] : Bytes).size
            from rfl, hashTreeRoot_byteVector]
        simp only [packBytes_one #[(1 : UInt8), 2, 3, 4] (by decide) (by decide),
          packBytes_one #[(5 : UInt8), 6, 7, 8] (by decide) (by decide)]
        simp [depthFor_one, subtreeAt_leaf, pad4, Bind.bind, Except.bind, Pure.pure,
          Except.pure])]
    rw [show (2#usize : Std.Usize).val = 2 from rfl, show (4#usize : Std.Usize).val = 4 from rfl]
      at hr
    rw [show chunksForBytes (2 * 4) = (packBytes (#[1, 2, 3, 4, 5, 6, 7, 8] : Bytes)).size
        from by decide, merkleizeBounded_some_self, merkleizeBounded_none] at hr
    rw [← hr, show (2 : Nat) = (#[pad4 #[1, 2, 3, 4], pad4 #[5, 6, 7, 8]] : Array Bytes).size
      from rfl, merkleizeBounded_some_self, merkleizeBounded_none]
    simp only [ne_eq, Except.ok.injEq]
    decide +kernel
  · rw [basic_items_bytes_eq _ rfl]
    apply WP.spec_mono (basic_items_bytes_u8n.spec 4#usize (alloc.vec.Vec.deref v)
      (by simp [alloc.vec.Vec.deref]; scalar_tac))
    intro out hout
    rw [hout, hd, hv]
    rfl

end Roots

/-! ## The containers in `verif_example.rs`

The EthLib types of each container, written as in consensus-specs (phase0 and altair, with
the mainnet sizes). The theorems' hypotheses are the invariants of the Rust types: an
`SszVector<T, N>` has exactly `N` items, and an `SszList<T, N>` no more than `N`. The
`ssz-types` constructors (`try_from`, decoding) guarantee them. -/

/-- A sequence of byte arrays as an EthLib value. -/
def bytesSeqV {M : Std.Usize} (xs : alloc.vec.Vec (Std.Array Std.U8 M)) : Value :=
  .seq (xs.val.map fun a => .bytes (bytes a.val))

/-- A sequence of `u64`s as an EthLib value. -/
def uintSeqV (xs : alloc.vec.Vec Std.U64) : Value := .seq (xs.val.map fun x => .uint x.val)

def hbNames : List String := ["block_roots", "state_roots"]
def hbFields : List Desc := [.vector (.byteVector 32) 8192, .vector (.byteVector 32) 8192]
def hbV (x : libssz_types.verif_example.HistoricalBatch) : Value :=
  .seq [bytesSeqV x.block_roots, bytesSeqV x.state_roots]

def iaNames : List String := ["attesting_indices", "data", "signature"]
def iaFields : List Desc :=
  [.list Desc.uint64 2048, .container Proofs.adNames Proofs.adFields, .byteVector 96]
def iaV (x : libssz_types.verif_example.IndexedAttestation) : Value :=
  .seq [uintSeqV x.attesting_indices, adV x.data, .bytes (bytes x.signature.val)]

def ddNames : List String := ["pubkey", "withdrawal_credentials", "amount", "signature"]
def ddFields : List Desc := [.byteVector 48, .byteVector 32, Desc.uint64, .byteVector 96]
def ddV (x : libssz_types.verif_example.DepositData) : Value :=
  .seq [.bytes (bytes x.pubkey.val), .bytes (bytes x.withdrawal_credentials.val),
    .uint x.amount.val, .bytes (bytes x.signature.val)]

def depNames : List String := ["proof", "data"]
def depFields : List Desc := [.vector (.byteVector 32) 33, .container ddNames ddFields]
def depV (x : libssz_types.verif_example.Deposit) : Value :=
  .seq [bytesSeqV x.proof, ddV x.data]

def scNames : List String := ["pubkeys", "aggregate_pubkey"]
def scFields : List Desc := [.vector (.byteVector 48) 512, .byteVector 48]
def scV (x : libssz_types.verif_example.SyncCommittee) : Value :=
  .seq [bytesSeqV x.pubkeys, .bytes (bytes x.aggregate_pubkey.val)]

def slNames : List String := ["block_roots", "historical_roots", "randao_mixes", "slashings"]
def slFields : List Desc :=
  [.vector (.byteVector 32) 8192, .list (.byteVector 32) 16777216, .vector (.byteVector 32) 65536,
    .vector Desc.uint64 8192]
def slV (x : libssz_types.verif_example.StateLists) : Value :=
  .seq [bytesSeqV x.block_roots, bytesSeqV x.historical_roots, bytesSeqV x.randao_mixes,
    uintSeqV x.slashings]

section Containers

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **`IndexedAttestation`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem IndexedAttestation.hash_tree_root.spec (x : libssz_types.verif_example.IndexedAttestation)
    (hai : x.attesting_indices.length ≤ 2048) :
    libssz_types.verif_example.IndexedAttestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container iaNames iaFields) (iaV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.IndexedAttestation.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.verif_example.AttestationData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with SszListU64.hash_tree_root.spec inst h hl x.attesting_indices hai (by scalar_tac)
    as ⟨ a0, h0 ⟩
  step with AttestationData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.signature as ⟨ a2, h2 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold iaV uintSeqV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val] rfl
    (by simp only [iaFields] at *; simp [h0, h1, h2, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 3#usize [a0, a1, a2] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show iaFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val]).size from rfl,
    merkleizeBounded_some_self, ← hr]

include hl in
/-- **`HistoricalBatch`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem HistoricalBatch.hash_tree_root.spec (x : libssz_types.verif_example.HistoricalBatch)
    (hb : x.block_roots.length = 8192) (hs : x.state_roots.length = 8192) :
    libssz_types.verif_example.HistoricalBatch.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container hbNames hbFields) (hbV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.HistoricalBatch.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.merkleize_in_place]
  step with SszVectorBytes32.hash_tree_root.spec inst h hl x.block_roots hb (by scalar_tac)
    as ⟨ a0, h0 ⟩
  step with SszVectorBytes32.hash_tree_root.spec inst h hl x.state_roots hs (by scalar_tac)
    as ⟨ a1, h1 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold hbV bytesSeqV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val] rfl
    (by simp only [hbFields] at *; simp [h0, h1, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 2#usize [a0, a1] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show hbFields.length = (#[bytes a0.val, bytes a1.val]).size from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **`DepositData`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem DepositData.hash_tree_root.spec (x : libssz_types.verif_example.DepositData) :
    libssz_types.verif_example.DepositData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container ddNames ddFields) (ddV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.DepositData.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root]
  simp only [libssz_types.libssz_merkle.merkleize_in_place]
  step with ArrayU8N.hash_tree_root.spec inst h hl x.pubkey as ⟨ a0, h0 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.withdrawal_credentials as ⟨ a1, h1 ⟩
  step with U64.hash_tree_root.spec inst h x.amount as ⟨ a2, h2 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.signature as ⟨ a3, h3 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold ddV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
    (by simp only [ddFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 4#usize [a0, a1, a2, a3] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show ddFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val]).size from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **`Deposit`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem Deposit.hash_tree_root.spec (x : libssz_types.verif_example.Deposit)
    (hp : x.proof.length = 33) :
    libssz_types.verif_example.Deposit.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container depNames depFields) (depV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.Deposit.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.merkleize_in_place]
  step with SszVectorBytes32.hash_tree_root.spec inst h hl x.proof hp (by scalar_tac)
    as ⟨ a0, h0 ⟩
  step with DepositData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold depV bytesSeqV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val] rfl
    (by simp only [depFields] at *; simp [h0, h1, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 2#usize [a0, a1] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show depFields.length = (#[bytes a0.val, bytes a1.val]).size from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **The rows of `Deposit`** (requires `proof` to have 33 nodes): the roots of its 2 fields,
the bottom level of its tree. -/
theorem Deposit.rows :
    Rows inst h libssz_types.verif_example.Deposit.Insts.Libssz_merkleHashTreeRoot (.container depNames depFields) depV
      (fun x => x.proof.length = 33) 1 where
  small := by omega
  width := ⟨ 2#usize, rfl, rfl ⟩
  row x row hgood hlen := by
    simp only [libssz_types.verif_example.Deposit.Insts.Libssz_merkleHashTreeRoot]
    unfold libssz_types.verif_example.Deposit.Insts.Libssz_merkleHashTreeRoot.hash_tree_root_row
    have hp : x.proof.length = 33 := hgood
    have hlen' : row.val.length = 2 := hlen
    obtain ⟨ b0, b1, hrowv ⟩ := list_len2 row.val hlen'
    step with SszVectorBytes32.hash_tree_root.spec inst h hl x.proof hp (by scalar_tac) as ⟨ a0, h0 ⟩
    step as ⟨ row1, hrow1 ⟩
    have hl1 : row1.length = 2 := by
      rw [hrow1]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    step with DepositData.hash_tree_root.spec inst h hl x.data as ⟨ a1, h1 ⟩
    step as ⟨ row2, hrow2 ⟩
    have hl2 : row2.length = 2 := by
      rw [hrow2]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    have hrv : row2.val = [a0, a1] := by
      rw [hrow2, hrow1]
      simp only [Slice.set_val_eq, hrowv]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    unfold RowRoot depV bytesSeqV
    rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val] rfl
      (by simp only [depFields] at *; simp [h0, h1, Pure.pure, Except.pure, Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [a0, a1] 1 (by simp [depthFor])

include hl in
/-- **`SyncCommittee`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem SyncCommittee.hash_tree_root.spec (x : libssz_types.verif_example.SyncCommittee)
    (hp : x.pubkeys.length = 512) :
    libssz_types.verif_example.SyncCommittee.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container scNames scFields) (scV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.SyncCommittee.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root]
  simp only [libssz_types.libssz_merkle.merkleize_in_place]
  step with SszVectorU8N.hash_tree_root.spec inst h hl (M := 48#usize) (by decide) x.pubkeys hp
    as ⟨ a0, h0 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.aggregate_pubkey as ⟨ a1, h1 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold scV bytesSeqV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val] rfl
    (by simp only [scFields] at *; simp [h0, h1, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 2#usize [a0, a1] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show scFields.length = (#[bytes a0.val, bytes a1.val]).size from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **`StateLists`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem StateLists.hash_tree_root.spec (x : libssz_types.verif_example.StateLists)
    (hb : x.block_roots.length = 8192) (hh : x.historical_roots.length ≤ 16777216)
    (hr : x.randao_mixes.length = 65536) (hs : x.slashings.length = 8192) :
    libssz_types.verif_example.StateLists.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container slNames slFields) (slV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.StateLists.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.libssz_merkle.merkleize_in_place]
  step with SszVectorBytes32.hash_tree_root.spec inst h hl x.block_roots hb (by scalar_tac)
    as ⟨ a0, h0 ⟩
  step with SszListBytes32.hash_tree_root.spec inst h hl x.historical_roots hh (by scalar_tac)
    as ⟨ a1, h1 ⟩
  step with SszVectorBytes32.hash_tree_root.spec inst h hl x.randao_mixes hr (by scalar_tac)
    as ⟨ a2, h2 ⟩
  step with SszVectorU64.hash_tree_root.spec inst h hl x.slashings hs (by scalar_tac)
    as ⟨ a3, h3 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold slV bytesSeqV uintSeqV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
    (by simp only [slFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 4#usize [a0, a1, a2, a3] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show slFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val]).size from rfl, merkleizeBounded_some_self, ← hr]

end Containers

end Libssz.SszTypes
