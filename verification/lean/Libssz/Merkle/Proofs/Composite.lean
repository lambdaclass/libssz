module
public import Libssz.Merkle.Proofs.Vecs
@[expose] public section

/-!
# Lists of composite items

For composite items, the `hash_tree_root` of `Vec<T>` (and those of `SszList` and `SszVector`,
in `ssz-types`) gets the item roots from `hash_tree_roots`. That function writes the item rows
(`hash_tree_root_row`, `hash_tree_root_width` nodes each) one after another, as many items as
fit in 256 nodes, and hashes all their trees together with `merkleize_groups`: each level of
all the trees is a single hasher layer.

* `merkleize_groups.spec`: with groups of `2^d` nodes, node `t` of the result is the subtree
  of height `d` that starts at node `t · 2^d`.
* `Rows`: what the rows of a type must satisfy for `hash_tree_roots` to produce their roots:
  the row's tree has the item's EthLib root. It holds for the default row (`Rows.of_default`:
  the root alone, a one-node tree) and for the rows the macro generates for a container (the
  roots of its fields, padded with zeros up to `2^d`; `Validator.rows`).
* `hash_tree_roots.spec`: if the rows satisfy `Rows`, node `i` is the root of item `i`.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz

namespace Libssz.Merkle

/-! ## A subtree only reads its leaves -/

theorem subtreeAt_chunks_congr (l1 l2 : List Node) (d a b : Nat)
    (h : ∀ k < 2 ^ d, l1[a + k]? = l2[b + k]?) :
    subtreeAt (chunksOf l1) d a = subtreeAt (chunksOf l2) d b :=
  subtreeAt_congr _ _ d a b (fun k hk => by rw [chunksOf_getElem?, chunksOf_getElem?, h k hk])

/-- Appending zero nodes at the end changes no subtree: the specification already reads zeros
past the data. -/
theorem subtreeAt_append_zeros (C : Array Bytes) (n d s : Nat) :
    subtreeAt (C ++ Array.replicate n zeroChunk) d s = subtreeAt C d s := by
  rw [subtreeAt_eq_subtreeRoot, subtreeAt_eq_subtreeRoot]
  congr 1
  funext i
  unfold padded
  by_cases hk : s + i < C.size
  · rw [Array.getElem?_append_left hk]
  · rw [Array.getElem?_eq_none (by omega : C.size ≤ s + i)]
    by_cases hk2 : s + i < C.size + n
    · rw [Array.getElem?_append_right (by omega), Array.getElem?_replicate]
      simp only [show s + i - C.size < n from by omega, ite_true]
      rfl
    · rw [Array.getElem?_eq_none (by simp; omega)]

/-- **A parent at level `l + 1`, with a sibling**: if the nodes of `src` are the subtrees of
height `l` and node `2j` has a sibling, parent `j` is the subtree of height `l + 1`. -/
theorem parentOf_subtreeAt_pair (C : Array Bytes) (l : Nat) (src : List Node) (zero : Node)
    (hsrc : ∀ k < src.length,
      (src[k]?.map fun n => bytes n.val) = some (subtreeAt C l (k * 2 ^ l)))
    (j : Nat) (hj : 2 * j + 1 < src.length) :
    parentOf src zero j = subtreeAt C (l + 1) (j * 2 ^ (l + 1)) := by
  rw [subtreeAt_split]
  unfold parentOf
  have hidx1 : j * 2 ^ (l + 1) = 2 * j * 2 ^ l := by rw [Nat.pow_succ]; ring
  have hidx2 : 2 * j * 2 ^ l + 2 ^ l = (2 * j + 1) * 2 ^ l := by ring
  rw [hidx1, hidx2]
  congr 1
  · have h1 := hsrc (2 * j) (by omega)
    rw [List.getElem?_eq_getElem (show 2 * j < src.length by omega)] at h1 ⊢
    simpa using h1
  · have h1 := hsrc (2 * j + 1) hj
    rw [List.getElem?_eq_getElem hj] at h1 ⊢
    simpa using h1

/-- Copying a slice onto another of the same length leaves the copy. -/
theorem copy_from_slice_eq {α : Type} (ci : core.marker.Copy α) (s0 s1 : Slice α)
    (h : s0.length = s1.length) : core.slice.Slice.copy_from_slice ci s0 s1 = ok s1 := by
  unfold core.slice.Slice.copy_from_slice
  have : s0.len = s1.len := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len, Slice.length] using h
  simp [this]

/-- From the item-by-item, position-by-position relation to `Forall₂`. -/
theorem forall₂_of_getElem? {α β : Type} (Q : α → β → Prop) (xs : List α) (ys : List β)
    (hlen : ys.length = xs.length)
    (h : ∀ t < xs.length, ∀ x, xs[t]? = some x → ∃ y, ys[t]? = some y ∧ Q x y) :
    List.Forall₂ Q xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Forall₂.nil
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨ y', hy', hq ⟩ := h 0 (by simp) x rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy'
      subst hy'
      refine List.Forall₂.cons hq (ih ys (by simpa using hlen) ?_)
      intro t ht x' hx'
      obtain ⟨ y', hy', hq' ⟩ := h (t + 1) (by simp; omega) x' (by simpa using hx')
      exact ⟨ y', by simpa using hy', hq' ⟩

/-! ## From `Forall₂` to `mapM` -/

/-- If each node is the root of its item, `mapM hashTreeRoot` of the items gives the nodes. -/
theorem mapM_of_forall₂ {T : Type} (elem : Desc) (val : T → Value) :
    ∀ (xs : List T) (rs : List Node),
    List.Forall₂ (fun x r => hashTreeRoot elem (val x) = .ok (bytes r.val)) xs rs →
    (xs.map val).mapM (hashTreeRoot elem) = .ok (rs.map fun r => bytes r.val) := by
  intro xs rs h
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    simp only [List.map_cons, List.mapM_cons, hxy, ih]
    rfl

section Groups

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

/-! ## `merkleize_groups` -/

include hl in
/-- The loop of `merkleize_groups`. The first `len = g · 2^e` nodes are the subtrees of height
`l` of `C`; each iteration hashes one level in place. Since `len` is even while levels remain,
no node is left without a sibling. -/
theorem merkleize_groups_loop.spec (C : Array Bytes) (g : Nat) (nodes : Slice Node)
    (len w : Std.Usize) (l e : Nat)
    (hw : w.val = 2 ^ e) (hlen : len.val = g * 2 ^ e) (hlenN : len.val ≤ nodes.length)
    (hnodes : ∀ k < len.val, (nodes.val[k]?.map fun n => bytes n.val) =
      some (subtreeAt C l (k * 2 ^ l))) :
    merkleize_groups_loop inst h nodes len w ⦃ r =>
      r.length = nodes.length ∧
      ∀ t < g, (r.val[t]?.map fun n => bytes n.val) =
        some (subtreeAt C (l + e) (t * 2 ^ (l + e))) ⦄ := by
  unfold merkleize_groups_loop
  spec_split
  · rename_i hgt
    obtain ⟨ e', rfl ⟩ : ∃ e', e = e' + 1 := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0
        simp only [pow_zero] at hw
        scalar_tac
      · exact ⟨ e - 1, by omega ⟩
    have hpow : 2 ^ (e' + 1) = 2 * 2 ^ e' := by rw [Nat.pow_succ]; ring
    step as ⟨ s, back, hs, hslen, hback ⟩
    step as ⟨ a, ha ⟩
    step with hl.hash_layer_in_place s a as ⟨ s1, hs1len, hs1par, hs1rest ⟩
    step as ⟨ len1, hlen1 ⟩
    step as ⟨ w1, hw1 ⟩
    have hl1 : len1.val = g * 2 ^ e' := by
      rw [hlen1, hlen, hpow]
      rw [show g * (2 * 2 ^ e') = (g * 2 ^ e') * 2 by ring]
      omega
    have hsk : ∀ k < len.val, s.val[k]? = nodes.val[k]? := by
      intro k hk
      rw [hs, List.slice, List.drop_zero, List.getElem?_take]
      simp [hk]
    have hb := hback s1
    have hbl : (back s1).length = nodes.length := by
      simp only [Slice.length, hb, List.length_setSlice!]
    have hbk : ∀ k < len.val, (back s1).val[k]? = s1.val[k]? := by
      intro k hk
      rw [hb, List.setSlice!_getElem?_middle _ _ _ _ ⟨ by omega, by scalar_tac, by scalar_tac ⟩]
      simp
    apply WP.spec_mono (merkleize_groups_loop.spec C g (back s1) len1 w1 (l + 1) e'
      (by rw [hw1, hw, hpow]; omega) hl1 (by rw [hbl]; omega)
      (by
        intro k hk
        rw [hbk k (by omega)]
        have hk' : k < s.length / 2 + s.length % 2 := by
          rw [hslen, hlen, hpow]; rw [hl1] at hk
          rw [show g * (2 * 2 ^ e') = (g * 2 ^ e') * 2 by ring]
          omega
        rw [hs1par k hk']
        congr 1
        apply parentOf_subtreeAt_pair C l s.val a
        · intro m hm
          rw [hsk m (by scalar_tac)]
          exact hnodes m (by scalar_tac)
        · have : s.val.length = len.val := hslen
          rw [this, hlen, hpow]; rw [hl1] at hk
          rw [show g * (2 * 2 ^ e') = (g * 2 ^ e') * 2 by ring]
          omega))
    intro r ⟨ hrl, hr ⟩
    refine ⟨ by rw [hrl, hbl], ?_ ⟩
    intro t ht
    rw [hr t ht, show l + 1 + e' = l + (e' + 1) by omega]
  · simp only [WP.spec_ok]
    rename_i hle
    have he0 : e = 0 := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · exact h0
      · have : 2 ≤ 2 ^ e := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h0
        scalar_tac
    subst he0
    refine ⟨ trivial, ?_ ⟩
    intro t ht
    simp only [Nat.add_zero]
    exact hnodes t (by simp at hlen; omega)
termination_by w.val
decreasing_by scalar_decr_tac

include hl in
/-- **`merkleize_groups`**: with `g` groups of `2^d` nodes, node `t` of the result is the tree
of height `d` of group `t`, that is, the subtree that starts at node `t · 2^d`. -/
theorem merkleize_groups.spec (nodes : Slice Node) (width : Std.Usize) (g d : Nat)
    (hw : width.val = 2 ^ d) (hn : nodes.length = g * 2 ^ d) :
    merkleize_groups inst h nodes width ⦃ r =>
      r.length = nodes.length ∧
      ∀ t < g, (r.val[t]?.map fun n => bytes n.val) =
        some (subtreeAt (chunksOf nodes.val) d (t * 2 ^ d)) ⦄ := by
  unfold merkleize_groups
  have := merkleize_groups_loop.spec inst h hl (chunksOf nodes.val) g nodes nodes.len width 0 d
    hw (by simpa using hn) (by simp)
    (by intro k hk; exact leaves nodes.val k (by simpa using hk))
  simpa using this

end Groups

/-! ## The rows -/

section Rows

variable {H : Type} (inst : Sha256Hasher H) (h : H)

/-- The tree of height `d` of row `row` has the EthLib root of `x`. -/
def RowRoot {T : Type} (elem : Desc) (val : T → Value) (d : Nat) (x : T) (row : List Node) :
    Prop :=
  hashTreeRoot elem (val x) = .ok (subtreeAt (chunksOf row) d 0)

/-- **The rows of `HI` give the EthLib root of `elem`**, for the items satisfying `good` (the
invariant of the item's type, if it has one). `hash_tree_root_width` is `2^d`, with `d ≤ 8`
(up to 256 nodes), and the row of `2^d` nodes written by `hash_tree_root_row` is the bottom
level of a tree whose root is the EthLib one. -/
structure Rows {T : Type} (HI : HashTreeRoot T) (elem : Desc) (val : T → Value)
    (good : T → Prop) (d : Nat) : Prop where
  small : d ≤ 8
  width : ∃ w : Std.Usize, HI.hash_tree_root_width = ok w ∧ w.val = 2 ^ d
  row : ∀ x (row : Slice Node), good x → row.length = 2 ^ d →
    HI.hash_tree_root_row inst x h row ⦃ r => r.length = 2 ^ d ∧ RowRoot elem val d x r.val ⦄

/-- **The default row**: one node, the root. A tree of height 0 is its single node. -/
theorem Rows.of_default {T : Type} (HI : HashTreeRoot T) (elem : Desc) (val : T → Value)
    (good : T → Prop) (hw : HI.hash_tree_root_width = ok 1#usize)
    (hrow : ∀ x row, HI.hash_tree_root_row inst x h row =
      HashTreeRoot.hash_tree_root_row.default HI inst x h row)
    (hitem : ∀ x, good x → HI.hash_tree_root inst x h ⦃ r =>
      hashTreeRoot elem (val x) = .ok (bytes r.val) ⦄) :
    Rows inst h HI elem val good 0 where
  small := by omega
  width := ⟨ 1#usize, hw, rfl ⟩
  row x row hgx hlen := by
    rw [hrow]
    unfold HashTreeRoot.hash_tree_root_row.default
    step with hitem x hgx as ⟨ r, hr ⟩
    step as ⟨ row', hrow' ⟩
    have hl' : row'.length = 1 := by
      rw [hrow']; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    refine ⟨ hl', ?_ ⟩
    unfold RowRoot
    have hl0 : 0 < row.val.length := by
      have : row.val.length = 1 := hlen
      omega
    rw [hr, subtreeAt_leaf, chunksOf_getElem?, hrow', Slice.set_val_eq]
    simp [List.getElem?_set, hl0]

/-! ### The rows the macro generates

For a container with `k` fields, the row is the roots of the fields followed by `2^d - k` zero
nodes, with `2^d` the first power of two that is not less than `k`. -/

theorem bytes_zeroNode : bytes zeroNode.val = zeroChunk := by
  simp [bytes, Array.repeat_val, zeroChunk, bytesPerChunk]
  rfl

theorem chunksOf_append_zeros (l : List Node) (n : Nat) :
    chunksOf (l ++ List.replicate n zeroNode) =
      chunksOf l ++ Array.replicate n zeroChunk := by
  simp only [chunksOf, List.map_append, List.map_replicate, bytes_zeroNode]
  apply Array.ext'
  simp

/-- **The root of a container is the tree of its row.** If the roots of its `k` fields are
`roots` and `depthFor k = d`, the specification gives the subtree of height `d` of the roots
followed by zeros. -/
theorem container_row_root (roots : List Node) (d : Nat) (hd : depthFor roots.length = d) :
    merkleizeBoundedUnchecked (roots.map fun r => bytes r.val).toArray (some roots.length) =
      .ok (subtreeAt (chunksOf (roots ++ List.replicate (2 ^ d - roots.length) zeroNode)) d 0) := by
  rw [merkleizeBoundedUnchecked_eq]
  simp only [List.size_toArray, List.length_map, lt_self_iff_false, ite_false, hd]
  rw [chunksOf_append_zeros, subtreeAt_append_zeros]
  rfl

/-- A list of 2, 4 or 8 elements, written out element by element. -/
theorem list_len2 {α : Type} (l : List α) (h : l.length = 2) : ∃ b0 b1, l = [b0, b1] := by
  match l, h with
  | [b0, b1], _ => exact ⟨ b0, b1, rfl ⟩

theorem list_len4 {α : Type} (l : List α) (h : l.length = 4) :
    ∃ b0 b1 b2 b3, l = [b0, b1, b2, b3] := by
  match l, h with
  | [b0, b1, b2, b3], _ => exact ⟨ b0, b1, b2, b3, rfl ⟩

theorem list_len8 {α : Type} (l : List α) (h : l.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7, l = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨ b0, b1, b2, b3, b4, b5, b6, b7, rfl ⟩

end Rows

/-! ## `hash_tree_roots` -/

section Roots

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

/-- The inner loop: the row of item `i + j` in nodes `j · 2^d` to `(j + 1) · 2^d - 1` of
`leaves`, for `j` up to `m`. -/
theorem hash_tree_roots_loop0_loop0.spec {T : Type} (HI : HashTreeRoot T) (elem : Desc)
    (val : T → Value) (good : T → Prop) (d : Nat) (hr : Rows inst h HI elem val good d)
    (items : Slice T) (hgood : ∀ x ∈ items.val, good x)
    (width : Std.Usize) (hw : width.val = 2 ^ d) (leaves : Std.Array Node 256#usize)
    (i m j : Std.Usize) (him : i.val + m.val ≤ items.length) (hm : m.val * 2 ^ d ≤ 256)
    (hj : j.val ≤ m.val)
    (hinv : ∀ t < j.val, ∀ x, items.val[i.val + t]? = some x →
      hashTreeRoot elem (val x) = .ok (subtreeAt (chunksOf leaves.val) d (t * 2 ^ d))) :
    hash_tree_roots_loop0_loop0 HI inst items h width leaves i m j ⦃ leaves' =>
      ∀ t < m.val, ∀ x, items.val[i.val + t]? = some x →
        hashTreeRoot elem (val x) = .ok (subtreeAt (chunksOf leaves'.val) d (t * 2 ^ d)) ⦄ := by
  unfold hash_tree_roots_loop0_loop0
  spec_split
  · rename_i hjm
    have hjm' : j.val < m.val := by scalar_tac
    have hjw : (j.val + 1) * 2 ^ d ≤ 256 :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hm
    have hmax : items.length ≤ Usize.max := by scalar_tac
    have hij : i.val + j.val < items.length := by omega
    step as ⟨ i1, hi1 ⟩
    step as ⟨ x, hx ⟩
    have hjw' : j.val * 2 ^ d + 2 ^ d ≤ 256 := by rw [Nat.add_mul] at hjw; omega
    have hjw0 : j.val * width.val ≤ 256 := by rw [hw]; omega
    step as ⟨ i2, hi2 ⟩
    step as ⟨ i3, hi3 ⟩
    have hjw1 : i3.val * width.val ≤ 256 := by rw [hi3, hw]; exact hjw
    step as ⟨ i4, hi4 ⟩
    have h24 : i2.val ≤ i4.val := by
      rw [hi2, hi4, hi3]; exact Nat.mul_le_mul_right _ (by omega)
    have h4 : i4.val ≤ 256 := by rw [hi4]; exact hjw1
    step as ⟨ s, back, hs, hslen, hback ⟩
    have hgx : good x := hgood x (by rw [hx]; exact List.getElem_mem _)
    step with hr.row x s hgx (by rw [hslen, hi4, hi2, hi3, hw]; ring_nf; omega)
      as ⟨ s1, hs1len, hs1root ⟩
    have hb := hback s1
    have hlv : leaves.val.length = 256 := by simp
    apply hash_tree_roots_loop0_loop0.spec HI elem val good d hr items hgood width hw
      (back s1) i m i3 him hm (by scalar_tac)
    · intro t ht x' hx'
      by_cases htj : t < j.val
      · rw [hinv t htj x' hx']
        congr 1
        apply subtreeAt_chunks_congr
        intro k hk
        rw [hb, List.setSlice!_getElem?_prefix]
        have : t * 2 ^ d + k < (t + 1) * 2 ^ d := by rw [Nat.add_mul]; omega
        have : (t + 1) * 2 ^ d ≤ j.val * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
        rw [hi2, hw]
        omega
      · have htj' : t = j.val := by scalar_tac
        subst htj'
        have hxx : x' = x := by
          have h1 : items.val[i.val + j.val]? = some x :=
            getElem?_of_eq _ i1.val _ (by scalar_tac) x hx (by scalar_tac)
          rw [h1] at hx'
          exact (Option.some.inj hx').symm
        subst hxx
        rw [hs1root]
        congr 1
        apply subtreeAt_chunks_congr
        intro k hk
        have hi2' : i2.val = j.val * 2 ^ d := by rw [hi2, hw]
        have hs1v : s1.val.length = 2 ^ d := hs1len
        rw [hb, Nat.zero_add, List.setSlice!_getElem?_middle _ _ _ _ ⟨ by omega, by omega,
          by omega ⟩]
        congr 1
        omega
  · simp only [WP.spec_ok]
    intro t ht x hx
    exact hinv t (by scalar_tac) x hx
termination_by m.val - j.val
decreasing_by scalar_decr_tac

include hl in
/-- The outer loop: `m` items at a time, their rows, their trees together, and the roots into
`out`. -/
theorem hash_tree_roots_loop0.spec {T : Type} (HI : HashTreeRoot T) (elem : Desc)
    (val : T → Value) (good : T → Prop) (d : Nat) (hr : Rows inst h HI elem val good d)
    (items : Slice T) (hgood : ∀ x ∈ items.val, good x) (out out0 : Slice Node) (width per_block : Std.Usize) (hw : width.val = 2 ^ d)
    (hpb : per_block.val = 256 / 2 ^ d) (leaves : Std.Array Node 256#usize) (i : Std.Usize)
    (hlen : out.length = out0.length) (hout : items.length ≤ out.length)
    (hi : i.val ≤ items.length)
    (hdone : ∀ t < i.val, ∀ x, items.val[t]? = some x →
      ∃ r, out.val[t]? = some r ∧ hashTreeRoot elem (val x) = .ok (bytes r.val))
    (hrest : ∀ t, i.val ≤ t → out.val[t]? = out0.val[t]?) :
    hash_tree_roots_loop0 HI inst items h out width per_block leaves i ⦃ out' =>
      out'.length = out0.length ∧
      (∀ t < items.length, ∀ x, items.val[t]? = some x →
        ∃ r, out'.val[t]? = some r ∧ hashTreeRoot elem (val x) = .ok (bytes r.val)) ∧
      (∀ t, items.length ≤ t → out'.val[t]? = out0.val[t]?) ⦄ := by
  have hd := hr.small
  have hp1 : 1 ≤ 256 / 2 ^ d := by
    have : 2 ^ d ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hd
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos d)).mpr (by simpa using this)
  have hpbw : (256 / 2 ^ d) * 2 ^ d ≤ 256 := Nat.div_mul_le_self _ _
  unfold hash_tree_roots_loop0
  dsimp only
  spec_split
  · rename_i hlt
    have hlt' : i.val < items.length := by scalar_tac
    step as ⟨ i3, hi3 ⟩
    apply WP.spec_bind (Pₘ := fun m : Std.Usize =>
      1 ≤ m.val ∧ i.val + m.val ≤ items.length ∧ m.val ≤ per_block.val)
    · split
      · step as ⟨ i4, hi4 ⟩
        refine ⟨ by scalar_tac, by scalar_tac, by scalar_tac ⟩
      · simp only [WP.spec_ok]
        refine ⟨ by scalar_tac, by scalar_tac, le_refl _ ⟩
    · intro m ⟨ hm1, hm2, hm3 ⟩
      have hmw : m.val * 2 ^ d ≤ 256 :=
        le_trans (Nat.mul_le_mul_right _ (by rw [← hpb]; exact hm3)) hpbw
      step with hash_tree_roots_loop0_loop0.spec inst h HI elem val good d hr items hgood width hw
        leaves
        i m 0#usize hm2 hmw (by scalar_tac) (by intro t ht; simp at ht) as ⟨ leaves1, hrows ⟩
      have hmw' : m.val * width.val ≤ 256 := by rw [hw]; exact hmw
      step as ⟨ i4, hi4 ⟩
      have h4 : i4.val ≤ 256 := by rw [hi4]; exact hmw'
      have hm256 : m.val ≤ 256 :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos d)) hmw
      step as ⟨ s, back, hs, hslen, hback ⟩
      step with merkleize_groups.spec inst h hl s width m.val d hw
        (by rw [hslen, hi4, hw]) as ⟨ s1, hs1len, hs1 ⟩
      step as ⟨ i5, hi5 ⟩
      step as ⟨ s2, back1, hs2, hs2len, hback1 ⟩
      have hb := hback s1
      step as ⟨ s3, hs3, hs3len ⟩
      have hs23 : s2.length = s3.length := by rw [hs2len, hs3len, hi5]; omega
      have hs3v : s3.val.length = m.val := hs3len
      have houtv : items.val.length ≤ out.val.length := hout
      rw [copy_from_slice_eq _ _ _ hs23]
      simp only [bind_ok]
      have hb1 : (back1 s3).val = out.val.setSlice! i.val s3.val := by
        rw [hback1 s3, Slice.setSlice!_val]
      have hlv : leaves1.val.length = 256 := by simp
      have hs1l : s1.val.length = m.val * 2 ^ d := by
        have : s1.length = s.length := hs1len
        simp only [Slice.length] at this hslen
        rw [this, hslen, hi4, hw]
      -- Node `k < m` of what is copied is the root of item `i + k`.
      have hcopy : ∀ k < m.val, ∀ x, items.val[i.val + k]? = some x →
          ∃ r, s3.val[k]? = some r ∧ hashTreeRoot elem (val x) = .ok (bytes r.val) := by
        intro k hk x hx
        have hk3 : s3.val[k]? = s1.val[k]? := by
          have hbl : (back s1).val.length = 256 := by simp
          rw [hs3, List.getElem?_slice _ _ _ _ ⟨ by simp [Array.to_slice, hbl]; omega,
            by omega ⟩]
          rw [Array.val_to_slice]
          have hkm : k < m.val * 2 ^ d :=
            lt_of_lt_of_le hk (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos d))
          rw [Nat.zero_add, hb, List.setSlice!_getElem?_middle _ _ _ _ ⟨ by omega,
            by rw [hs1l]; exact hkm, by rw [hlv]; omega ⟩]
          simp
        have hk1 := hs1 k hk
        obtain ⟨ r, hr1 ⟩ : ∃ r, s1.val[k]? = some r := by
          rcases h' : s1.val[k]? with _ | r
          · rw [h'] at hk1; simp at hk1
          · exact ⟨ r, rfl ⟩
        refine ⟨ r, by rw [hk3, hr1], ?_ ⟩
        rw [hr1] at hk1
        simp only [Option.map_some, Option.some.injEq] at hk1
        rw [hrows k hk x hx, hk1]
        congr 1
        apply subtreeAt_chunks_congr
        intro j hj
        rw [hs, List.getElem?_slice _ _ _ _ ⟨ by rw [hlv, hi4, hw]; exact hmw, by
          rw [hi4, hw]
          have : (k + 1) * 2 ^ d ≤ m.val * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul] at this
          omega ⟩]
        rw [Nat.zero_add]
      have hol : (back1 s3).length = out.length := by
        simp only [Slice.length]; rw [hb1, List.length_setSlice!]
      apply WP.spec_mono (hash_tree_roots_loop0.spec HI elem val good d hr items hgood (back1 s3)
        out0
        width per_block hw hpb (back s1) i5 (by rw [hol, hlen]) (by rw [hol]; exact hout)
        (by scalar_tac) ?_ ?_)
      · intro r hrr
        exact hrr
      · intro t ht x hx
        by_cases hti : t < i.val
        · obtain ⟨ r, hr1, hr2 ⟩ := hdone t hti x hx
          refine ⟨ r, ?_, hr2 ⟩
          rw [hb1, List.setSlice!_getElem?_prefix _ _ _ _ hti, hr1]
        · have hk : t - i.val < m.val := by scalar_tac
          obtain ⟨ r, hr1, hr2 ⟩ := hcopy (t - i.val) hk x
            (by rw [show i.val + (t - i.val) = t by omega]; exact hx)
          refine ⟨ r, ?_, hr2 ⟩
          have hti5 : t < i.val + m.val := by scalar_tac
          have hm2v : i.val + m.val ≤ items.val.length := hm2
          rw [hb1, List.setSlice!_getElem?_middle _ _ _ _ ⟨ by omega, by omega, by omega ⟩,
            hr1]
      · intro t ht
        have hti5 : i.val + m.val ≤ t := by scalar_tac
        rw [hb1, List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
        exact hrest t (by scalar_tac)
  · simp only [WP.spec_ok]
    have hil : i.val = items.length := by scalar_tac
    refine ⟨ hlen, ?_, ?_ ⟩
    · intro t ht x hx
      exact hdone t (by omega) x hx
    · intro t ht
      exact hrest t (by omega)
termination_by items.length - i.val
decreasing_by scalar_decr_tac

include hl in
/-- **`hash_tree_roots`**: if the rows of the type give the EthLib root (`Rows`), it leaves
the root of item `t` in `out[t]`, and the rest of `out` as it was. -/
theorem hash_tree_roots.spec {T : Type} (HI : HashTreeRoot T) (elem : Desc) (val : T → Value)
    (good : T → Prop) (d : Nat) (hr : Rows inst h HI elem val good d) (items : Slice T)
    (hgood : ∀ x ∈ items.val, good x) (out : Slice Node) (hout : items.length ≤ out.length) :
    hash_tree_roots HI inst items h out ⦃ out' =>
      out'.length = out.length ∧
      (∀ t < items.length, ∀ x, items.val[t]? = some x →
        ∃ r, out'.val[t]? = some r ∧ hashTreeRoot elem (val x) = .ok (bytes r.val)) ∧
      (∀ t, items.length ≤ t → out'.val[t]? = out.val[t]?) ⦄ := by
  obtain ⟨ w, hw, hwv ⟩ := hr.width
  have hd := hr.small
  have hw256 : 2 ^ d ≤ 256 := by
    have : 2 ^ d ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hd
    simpa using this
  have hwpos : 0 < 2 ^ d := Nat.two_pow_pos d
  unfold hash_tree_roots
  rw [hw]
  simp only [bind_ok]
  step
  step
  step as ⟨ per_block, hpb ⟩
  apply hash_tree_roots_loop0.spec inst h hl HI elem val good d hr items hgood out out w
    per_block hwv
    (by rw [hpb, hwv]) _ 0#usize rfl hout (by simp)
    (by intro t ht; simp at ht) (by intro t _; rfl)

end Roots

/-! ## `Vec<T>` with composite items -/

section Vec

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **The `hash_tree_root` of `Vec<T>` for composite items**: if `T` claims not to be basic,
and its rows give the EthLib root for the descriptor `elem` (not basic), the one of the `Vec`
is the EthLib root for `List[elem, len]`. The item's `SszEncode` is not used: the theorem
holds for any of them. -/
theorem vec_composite_root {T : Type} (HI : HashTreeRoot T) (EI : libssz_codec.encode.SszEncode T)
    (hbasic : HI.is_basic_type = ok false) (elem : Desc) (helem : elem.isBasic = false)
    (val : T → Value) (good : T → Prop) (d : Nat) (hrows : Rows inst h HI elem val good d)
    (v : alloc.vec.Vec T) (hgood : ∀ x ∈ v.val, good x) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root HI EI inst v h ⦃ r =>
      hashTreeRoot (.list elem v.length) (.seq (v.val.map val)) = .ok (bytes r.val) ⦄ := by
  unfold alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [hbasic, bind_ok, Bool.false_eq_true, ↓reduceIte]
  step with alloc.vec.from_elem_spec _ _ _ (clone_node _) as ⟨ roots, hrv, hrl ⟩
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  have hrl' : roots.slice.length = v.slice.length := by
    have e : (↑v.len : Nat) = v.length := by simp
    have e2 : roots.slice.length = roots.length := rfl
    rw [e2, hrl, e]
    rfl
  have hd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
  step with hash_tree_roots.spec inst h hl HI elem val good d hrows (alloc.vec.Vec.deref v)
    (by rw [hd]; exact hgood) roots.slice (by
      have : (alloc.vec.Vec.deref v).length = v.slice.length := by
        simp [alloc.vec.Vec.deref, Slice.length]
        rfl
      omega)
    as ⟨ s2, hs2len, hs2, _ ⟩
  set chunks : alloc.vec.Vec Node := { slice := s2 } with hchunks
  have hF : List.Forall₂ (fun x r => hashTreeRoot elem (val x) = .ok (bytes r.val))
      v.val chunks.val := by
    apply forall₂_of_getElem?
    · have h1 : s2.length = roots.slice.length := hs2len
      show s2.val.length = v.slice.val.length
      simp only [Slice.length] at h1 hrl'
      rw [h1, hrl']
    · intro t ht x hx
      exact hs2 t (by simpa [alloc.vec.Vec.deref] using ht) x (by rw [hd]; exact hx)
  have hroots := mapM_of_forall₂ elem val v.val chunks.val hF
  have hlen : chunks.val.length = v.val.length := hF.length_eq.symm
  set X := chunksOf chunks.val with hX
  have hXs : X.size = v.length := by
    simp [hX, chunksOf, hlen, alloc.vec.Vec.length]
  step as ⟨ b1, hb1 ⟩
  apply WP.spec_bind (Pₘ := fun root : Node =>
    bytes root.val = subtreeAt X (depthFor X.size) 0)
  · split
    · rename_i hbt
      have h0 : chunks.val = [] := by
        have : chunks.length = 0 := by rw [← hb1]; exact hbt
        exact List.eq_nil_of_length_eq_zero this
      step as ⟨ a, ha ⟩
      step with merkleize.spec inst h hl _ none (by simp) as ⟨ root, hroot ⟩
      have hza := bytes_zero_hashes 0 (by omega) a ha
      have hp : X = #[] := by rw [hX, h0]; rfl
      simp only [Option.map_none, merkleizeBounded_none] at hroot
      rw [hp, subtreeAt_past _ _ _ (by simp), zeroSubtree_eq, Array.size_empty, depthFor_zero]
      have hc1 : chunksOf (Array.make 1#usize [a] (by simp)).to_slice.val = #[bytes a.val] := by
        simp [chunksOf, Array.to_slice]
      rw [hc1] at hroot
      simp [depthFor_one, subtreeAt_leaf] at hroot
      rw [← hroot, hza]
    · step with merkleize_in_place.spec inst h hl chunks.slice none (by simp)
        as ⟨ root1, rest, hroot, _ ⟩
      simp only [Option.map_none, merkleizeBounded_none] at hroot
      have hvs : (chunks.slice).val = chunks.val := rfl
      rw [hvs, ← hX] at hroot
      simp only [Except.ok.injEq] at hroot
      exact hroot.symm
  · intro root hroot
    step with mix_in_length.spec inst h hl root v.len as ⟨ r, hr ⟩
    rw [hashTreeRoot_list_composite elem helem v.length _ _ (by simp) hroots]
    have hXe : (chunks.val.map fun r => bytes r.val).toArray = X := rfl
    rw [hXe, ← hXs, merkleizeBounded_some_self, merkleizeBounded_none]
    simp only [Except.map, List.length_map, hXs]
    rw [hr, hroot, hXs]
    have e1 : v.len.val = v.val.length := by simp
    rw [e1]

/-- The rows of `[u8; N]` are the default ones: the root alone. -/
theorem ArrayU8N.rows {N : Std.Usize} (hl : Lawful inst h) :
    Rows inst h (ArrayU8N.Insts.Libssz_merkleHashTreeRoot N) (.byteVector N.val)
      (fun a => .bytes (bytes a.val)) (fun _ => True) 0 :=
  Rows.of_default inst h _ _ _ _ rfl (fun _ _ => rfl)
    (fun x _ => ArrayU8N.hash_tree_root.spec inst h hl x)

include hl in
/-- **`Vec<[u8; N]>` with `N > 32`** (for example `Vec<[u8; 48]>`, public keys): the
`hash_tree_root` is the EthLib one for `List[ByteVector[N], len]`. With `N > 32`, libssz
treats the array as composite, like the specification. -/
theorem VecU8N.hash_tree_root.spec {N : Std.Usize} (hN : 32 < N.val)
    (v : alloc.vec.Vec (Std.Array Std.U8 N)) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (ArrayU8N.Insts.Libssz_merkleHashTreeRoot N) (ArrayU8N.Insts.LibsszEncodeSszEncode N)
      inst v h ⦃ r =>
      hashTreeRoot (.list (.byteVector N.val) v.length)
        (.seq (v.val.map fun a => .bytes (bytes a.val))) = .ok (bytes r.val) ⦄ :=
  vec_composite_root inst h hl _ _ (by
      simp only [ArrayU8N.Insts.Libssz_merkleHashTreeRoot.is_basic_type]
      have : ¬ (N ≤ 32#usize) := by scalar_tac
      simp [this]) (.byteVector N.val) rfl _ _ 0 (ArrayU8N.rows inst h hl) v (fun _ _ => trivial)

include hl in
/-- **The rows of `Validator`**: the roots of its eight fields, the bottom level of its
tree. -/
theorem Validator.rows :
    Rows inst h verif_example.Validator.Insts.Libssz_merkleHashTreeRoot
      (.container Proofs.valNames Proofs.valFields) valV (fun _ => True) 3 where
  small := by omega
  width := ⟨ 8#usize, rfl, rfl ⟩
  row x row _ hlen := by
    simp only [verif_example.Validator.Insts.Libssz_merkleHashTreeRoot]
    unfold verif_example.Validator.Insts.Libssz_merkleHashTreeRoot.hash_tree_root_row
    have hlen' : row.val.length = 8 := hlen
    obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7, hb ⟩ := list_len8 row.val hlen'
    step with ArrayU8N.hash_tree_root.spec inst h hl x.pubkey as ⟨ a0, h0 ⟩
    step as ⟨ row1, hrow1 ⟩
    have hl1 : row1.length = 8 := by
      rw [hrow1]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    step with ArrayU8N.hash_tree_root.spec inst h hl x.withdrawal_credentials as ⟨ a1, h1 ⟩
    step as ⟨ row2, hrow2 ⟩
    have hl2 : row2.length = 8 := by
      rw [hrow2]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    step with U64.hash_tree_root.spec inst h x.effective_balance as ⟨ a2, h2 ⟩
    step as ⟨ row3, hrow3 ⟩
    have hl3 : row3.length = 8 := by
      rw [hrow3]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl2
    step with Bool.hash_tree_root.spec inst h x.slashed as ⟨ a3, h3 ⟩
    step as ⟨ row4, hrow4 ⟩
    have hl4 : row4.length = 8 := by
      rw [hrow4]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl3
    step with U64.hash_tree_root.spec inst h x.activation_eligibility_epoch as ⟨ a4, h4 ⟩
    step as ⟨ row5, hrow5 ⟩
    have hl5 : row5.length = 8 := by
      rw [hrow5]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl4
    step with U64.hash_tree_root.spec inst h x.activation_epoch as ⟨ a5, h5 ⟩
    step as ⟨ row6, hrow6 ⟩
    have hl6 : row6.length = 8 := by
      rw [hrow6]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl5
    step with U64.hash_tree_root.spec inst h x.exit_epoch as ⟨ a6, h6 ⟩
    step as ⟨ row7, hrow7 ⟩
    have hl7 : row7.length = 8 := by
      rw [hrow7]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl6
    step with U64.hash_tree_root.spec inst h x.withdrawable_epoch as ⟨ a7, h7 ⟩
    step as ⟨ r, hr ⟩
    have hrv : r.val = [a0, a1, a2, a3, a4, a5, a6, a7] := by
      rw [hr, hrow7, hrow6, hrow5, hrow4, hrow3, hrow2, hrow1]
      simp only [Slice.set_val_eq, hb]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    have h0' : hashTreeRoot (.byteVector 48) (.bytes (bytes x.pubkey.val)) =
      .ok (bytes a0.val) := h0
    have h1' : hashTreeRoot (.byteVector 32) (.bytes (bytes x.withdrawal_credentials.val)) =
      .ok (bytes a1.val) := h1
    unfold RowRoot valV
    rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val,
      bytes a4.val, bytes a5.val, bytes a6.val, bytes a7.val] rfl
      (by simp [Proofs.valFields, h0', h1', h2, h3, h4, h5, h6, h7, Pure.pure, Except.pure,
        Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [a0, a1, a2, a3, a4, a5, a6, a7] 3 (by simp [depthFor])

include hl in
/-- **`Vec<Validator>`** (the validator list): the `hash_tree_root` is the EthLib one for
`List[Validator, len]`, **for any implementation of `SszEncode`**. In Rust,
`Vec<T>: HashTreeRoot` requires `T: SszEncode`, but the composite-item path does not use it.
The `Validator` in `verif_example.rs` has no `SszEncode` (extracting the one generated by
`#[derive(SszEncode)]` is not needed): the theorem holds for whichever one any `Validator`
with this `hash_tree_root` has. -/
theorem VecValidator.hash_tree_root.spec (EI : libssz_codec.encode.SszEncode verif_example.Validator)
    (v : alloc.vec.Vec verif_example.Validator) :
    alloc.vec.Vec.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      verif_example.Validator.Insts.Libssz_merkleHashTreeRoot EI inst v h ⦃ r =>
      hashTreeRoot (.list (.container Proofs.valNames Proofs.valFields) v.length)
        (.seq (v.val.map valV)) = .ok (bytes r.val) ⦄ :=
  vec_composite_root inst h hl _ EI rfl _ rfl valV _ 3 (Validator.rows inst h hl) v
    (fun _ _ => trivial)

end Vec

end Libssz.Merkle
