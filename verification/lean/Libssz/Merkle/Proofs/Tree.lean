module
public import Libssz.Merkle.Proofs.Hasher
public import Libssz.Merkle.Proofs.Zero
public import Mathlib.Data.Nat.Log
import all Aeneas.Std.Array.Core
@[expose] public section

/-!
# The tree: `merkleize` and `merkleize_in_place`

For every hasher that satisfies the specification (`Lawful`), `merkleize` and
`merkleize_in_place` return the root given by EthLib's `merkleizeBoundedUnchecked`, with or
without a limit.

The code and the specification traverse the tree in opposite directions. EthLib defines it
top-down (`subtreeAt`: a subtree is the `combine` of its two halves). `ssz-merkle` computes
it bottom-up: one level per iteration, written over the previous one (`real_root`), and then
the levels that only have zeros on the right (`virtual_root`). The invariant linking them:
after `l` iterations, node `k` is `subtreeAt C l (k * 2^l)`.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz

namespace Libssz.Merkle

/-- The nodes of a slice as the array of `Bytes` that the specification takes. -/
def chunksOf (l : List Node) : Array Bytes := (l.map fun n => bytes n.val).toArray

@[simp] theorem chunksOf_size (l : List Node) : (chunksOf l).size = l.length := by
  simp [chunksOf]

theorem chunksOf_getElem? (l : List Node) (k : Nat) :
    (chunksOf l)[k]? = l[k]?.map fun n => bytes n.val := by
  simp [chunksOf]

/-! ## The depth -/

/-- No `usize` exceeds `2^64`. -/
theorem usize_lt (x : Std.Usize) : x.val < 2 ^ 64 := by
  have h := x.hBounds
  rcases System.Platform.numBits_eq with h64 | h64 <;>
    simp only [UScalarTy.numBits, h64] at h <;> omega

/-- The tree depth required by a `usize` fits in the zero table. -/
theorem depthFor_le_64 (n : Nat) (h : n < 2 ^ 64) : depthFor n ≤ 64 :=
  depthFor_le_of_le_two_pow (Nat.le_of_lt h)

/-- With two or more leaves, `depthFor` is `log₂ (n - 1) + 1`. -/
theorem depthFor_eq_log (n : Nat) (h : 2 ≤ n) : depthFor n = Nat.log 2 (n - 1) + 1 := by
  apply Nat.le_antisymm
  · apply depthFor_le_of_le_two_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (n - 1)
    omega
  · have hle := le_two_pow_depthFor n
    have hpow := Nat.pow_log_le_self 2 (x := n - 1) (by omega)
    by_contra hlt
    have : 2 ^ depthFor n ≤ 2 ^ Nat.log 2 (n - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- For two or more leaves, the tree has one more level than that of the half (rounded up).
This is the recursion of `depthFor`. -/
theorem depthFor_half (n : Nat) (h : 2 ≤ n) : depthFor n = depthFor ((n + 1) / 2) + 1 := by
  rw [depthFor, ite_eq_right (by omega)]

theorem depthFor_one : depthFor 1 = 0 := by rw [depthFor]; simp

theorem depthFor_zero : depthFor 0 = 0 := by rw [depthFor]; simp

/-- **`ceil_log2` is `depthFor`.** -/
@[step]
theorem ceil_log2.spec (count : Std.Usize) : ceil_log2 count ⦃ d => d.val = depthFor count.val ⦄ := by
  unfold ceil_log2
  spec_split
  · simp only [WP.spec_ok]
    rename_i hle
    have : count.val ≤ 1 := by scalar_tac
    rw [depthFor, ite_eq_left this]; rfl
  · rename_i hgt
    have h2 : 2 ≤ count.val := by scalar_tac
    step as ⟨ i, hi ⟩
    have hi64 : (UScalar.cast .U64 i).val = i.val := by
      rw [UScalar.cast_val_eq]; have := usize_lt i
      exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
    simp only [lift, bind_ok]
    have hlog : Nat.log 2 i.val < 64 :=
      Nat.log_lt_of_lt_pow (by scalar_tac) (usize_lt i)
    have hlz : (core.num.U64.leading_zeros (UScalar.cast .U64 i)).val
        = 63 - Nat.log 2 i.val := by
      have htn : (UScalar.cast .U64 i).bv.toNat = i.val := hi64
      have hne : (UScalar.cast .U64 i).bv ≠ 0 := by
        intro h0
        have : i.val = 0 := by rw [← htn, h0]; simp
        scalar_tac
      simp only [core.num.U64.leading_zeros, BitVec.leadingZeros, hne, ↓reduceIte, htn]
      simp only [UScalar.val]
      simp
      omega
    step as ⟨ i3, hi3 ⟩
    have h3 : i3.val = Nat.log 2 i.val + 1 := by rw [hi3, hlz]; omega
    rw [UScalar.cast_val_eq, depthFor_eq_log _ h2, h3, ← hi]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h64 | h64 <;>
      simp only [UScalarTy.numBits, h64] <;> omega

/-- **`tree_depth` is the depth the specification requires**: that of the limit, if there is
one, or that of the nodes. -/
@[step]
theorem tree_depth.spec (len : Std.Usize) (limit : Option Std.Usize)
    (h : ∀ l, limit = some l → len.val ≤ l.val) :
    tree_depth len limit ⦃ d => d.val = depthFor ((limit.map (·.val)).getD len.val) ⦄ := by
  unfold tree_depth
  rcases limit with _ | l
  · simp only [bind_ok]
    apply WP.spec_mono (ceil_log2.spec len)
    intro d hd; simpa using hd
  · have hl := h l rfl
    have hle : len ≤ l := by scalar_tac
    simp only [hle, ↓reduceIte, bind_ok]
    apply WP.spec_mono (ceil_log2.spec l)
    intro d hd; simpa using hd

/-! ## Copying nodes -/

theorem mapM_ok {α : Type} (l : List α) :
    List.mapM_with_length (m := Result) (fun x => ok x) l = ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mapM_with_length, ih, bind_tc_ok]
    rfl

/-- Cloning a node (`[u8; 32]`) does not change it. -/
theorem clone_node (x : Node) : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone x = ok x := by
  simp only [core.array.CloneArray.clone, Array.clone, List.clone]
  rw [mapM_ok]
  simp only [bind_tc_ok]
  congr 1
  exact Aeneas.Std.Array.ext _ _ (by simp)

/-! ## The zero table, in the code -/

theorem bytes_zero_hashes (k : Nat) (hk : k < 65) (a : Node)
    (ha : a = ZERO_HASHES.val[k]'(by simp; omega)) :
    bytes a.val = zeroRoot combine zeroChunk k := by
  rw [← zeroRow_eq k (by omega), zeroRow, ha, getElem!_pos]

/-! ## One tree level -/

/-- **A parent at level `l + 1`.** If the nodes of `src` are the specification's subtrees of
height `l`, parent `j` computed by a layer is the subtree of height `l + 1`. If the last node
has no sibling, `zero` takes its place, the root of the zero tree of height `l`: that is what
the specification puts at a position past the data. -/
theorem parentOf_subtreeAt (C : Array Bytes) (l : Nat) (src : List Node) (zero : Node)
    (hsrc : ∀ k < src.length,
      (src[k]?.map fun n => bytes n.val) = some (subtreeAt C l (k * 2 ^ l)))
    (hcov : C.size ≤ src.length * 2 ^ l)
    (hzero : bytes zero.val = zeroRoot combine zeroChunk l)
    (j : Nat) (hj : 2 * j < src.length) :
    parentOf src zero j = subtreeAt C (l + 1) (j * 2 ^ (l + 1)) := by
  rw [subtreeAt_split]
  unfold parentOf
  have hidx1 : j * 2 ^ (l + 1) = 2 * j * 2 ^ l := by rw [Nat.pow_succ]; ring
  have hidx2 : 2 * j * 2 ^ l + 2 ^ l = (2 * j + 1) * 2 ^ l := by ring
  rw [hidx1, hidx2]
  congr 1
  · have h1 := hsrc (2 * j) hj
    rw [List.getElem?_eq_getElem hj] at h1 ⊢
    simpa using h1
  · by_cases h2 : 2 * j + 1 < src.length
    · have h1 := hsrc (2 * j + 1) h2
      rw [List.getElem?_eq_getElem h2] at h1 ⊢
      simpa using h1
    · rw [List.getElem?_eq_none (by omega), Option.getD_none, hzero,
        subtreeAt_past _ _ _ (by
          calc C.size ≤ src.length * 2 ^ l := hcov
            _ ≤ (2 * j + 1) * 2 ^ l := Nat.mul_le_mul_right _ (by omega)),
        zeroSubtree_eq]

/-! ## `real_root`: bottom-up -/

section Real

variable {H : Type} (inst : Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- The loop of `real_root`. The first `len` nodes are the subtrees of height `level` that
cover the data `C`: `len = ⌈|C| / 2^level⌉`. Each iteration hashes one level in place; at the
end one node remains, the root of the subtree of height `level + depthFor len`. -/
theorem real_root_loop.spec (C : Array Bytes) (nodes : Slice Node) (level len : Std.Usize)
    (hlen : 1 ≤ len.val) (hlenN : len.val ≤ nodes.length)
    (hcov1 : (len.val - 1) * 2 ^ level.val < C.size)
    (hcov2 : C.size ≤ len.val * 2 ^ level.val)
    (hnodes : ∀ k < len.val, (nodes.val[k]?.map fun n => bytes n.val) =
      some (subtreeAt C level.val (k * 2 ^ level.val)))
    (hdepth : level.val + depthFor len.val ≤ 64) :
    real_root_loop inst h nodes level len ⦃ r =>
      r.length = nodes.length ∧
      (r.val[0]?.map fun n => bytes n.val) =
        some (subtreeAt C (level.val + depthFor len.val) 0) ⦄ := by
  unfold real_root_loop
  spec_split
  · rename_i hgt
    have h2 : 2 ≤ len.val := by scalar_tac
    have hd := depthFor_half len.val h2
    have hlev : level.val < 64 := by omega
    step as ⟨ s, back, hs, hslen, hback ⟩
    step as ⟨ a, ha ⟩
    have hza : bytes a.val = zeroRoot combine zeroChunk level.val :=
      bytes_zero_hashes level.val (by omega) a ha
    have hsk : ∀ k < len.val, s.val[k]? = nodes.val[k]? := by
      intro k hk
      rw [hs, List.slice, List.drop_zero, List.getElem?_take]
      simp [hk]
    step with hl.hash_layer_in_place s a as ⟨ s1, hs1len, hs1par, hs1rest ⟩
    step as ⟨ len1, hlen1 ⟩
    step as ⟨ level1, hlevel1 ⟩
    have hl1 : len1.val = (len.val + 1) / 2 := by rw [hlen1, Nat.ceilDiv_eq_add_pred_div]; omega
    have hb := hback s1
    have hbl : (back s1).length = nodes.length := by
      simp only [Slice.length, hb, List.length_setSlice!]
    have hbk : ∀ k < len.val, (back s1).val[k]? = s1.val[k]? := by
      intro k hk
      rw [hb, List.setSlice!_getElem?_middle _ _ _ _ ⟨ by omega, by scalar_tac, by scalar_tac ⟩]
      simp
    have hpow : 2 ^ level1.val = 2 * 2 ^ level.val := by rw [hlevel1, Nat.pow_succ]; ring
    apply WP.spec_mono (real_root_loop.spec C (back s1) level1 len1 (by omega)
      (by rw [hbl]; omega)
      (by
        rw [hpow]
        calc (len1.val - 1) * (2 * 2 ^ level.val) = (2 * (len1.val - 1)) * 2 ^ level.val := by
              ring
          _ ≤ (len.val - 1) * 2 ^ level.val := Nat.mul_le_mul_right _ (by omega)
          _ < C.size := hcov1)
      (by
        rw [hpow]
        calc C.size ≤ len.val * 2 ^ level.val := hcov2
          _ ≤ (2 * len1.val) * 2 ^ level.val := Nat.mul_le_mul_right _ (by omega)
          _ = len1.val * (2 * 2 ^ level.val) := by ring)
      (by
        intro k hk
        rw [hbk k (by omega)]
        have hk' : k < s.length / 2 + s.length % 2 := by rw [hslen]; omega
        rw [hs1par k hk', hlevel1]
        congr 1
        apply parentOf_subtreeAt C level.val s.val a
        · intro m hm
          rw [hsk m (by scalar_tac)]
          exact hnodes m (by scalar_tac)
        · have : s.val.length = len.val := hslen
          rw [this]; exact hcov2
        · exact hza
        · have : s.val.length = len.val := hslen
          rw [this]; omega)
      (by rw [hlevel1, hl1]; omega))
    intro r ⟨ hrl, hr0 ⟩
    refine ⟨ by rw [hrl, hbl], ?_ ⟩
    have heq : level1.val + depthFor len1.val = level.val + depthFor len.val := by
      rw [hlevel1, hl1, hd]; omega
    rw [hr0, heq]
  · simp only [WP.spec_ok]
    rename_i hle
    have h1 : len.val = 1 := by scalar_tac
    refine ⟨ by trivial, ?_ ⟩
    rw [h1, depthFor_one, Nat.add_zero]
    have := hnodes 0 (by omega)
    simpa using this
termination_by len.val
decreasing_by scalar_decr_tac

include hl in
/-- **`real_root`**: the root of the smallest subtree that covers the data. -/
theorem real_root.spec (C : Array Bytes) (nodes : Slice Node) (level : Std.Usize)
    (hlen : 1 ≤ nodes.length)
    (hcov1 : (nodes.length - 1) * 2 ^ level.val < C.size)
    (hcov2 : C.size ≤ nodes.length * 2 ^ level.val)
    (hnodes : ∀ k < nodes.length, (nodes.val[k]?.map fun n => bytes n.val) =
      some (subtreeAt C level.val (k * 2 ^ level.val)))
    (hdepth : level.val + depthFor nodes.length ≤ 64) :
    real_root inst h nodes level ⦃ root rest =>
      bytes root.val = subtreeAt C (level.val + depthFor nodes.length) 0 ∧
      rest.length = nodes.length ⦄ := by
  unfold real_root
  step with real_root_loop.spec inst h hl C nodes level nodes.len (by scalar_tac)
    (by scalar_tac) (by simpa using hcov1) (by simpa using hcov2)
    (by intro k hk; exact hnodes k (by scalar_tac)) (by simpa using hdepth)
    as ⟨ n1, hn1l, hn10 ⟩
  step as ⟨ a, ha ⟩
  refine ⟨ ?_, hn1l ⟩
  rw [List.getElem?_eq_getElem (by scalar_tac), ← ha] at hn10
  simpa using hn10

include hl in
/-- `hash_nodes` is `hash_pair`. -/
theorem hash_nodes.spec (a b : Node) :
    hash_nodes inst h a b ⦃ r => bytes r.val = combine (bytes a.val) (bytes b.val) ⦄ := by
  unfold hash_nodes
  exact hl.hash_pair a b

include hl in
/-- The loop of `virtual_root`: each iteration goes up one level, with the zero tree of that
level as the right sibling. -/
theorem virtual_root_loop.spec (C : Array Bytes) (root : Node) (depth level : Std.Usize)
    (hdepth : depth.val ≤ 64) (hcov : C.size ≤ 2 ^ level.val)
    (hroot : bytes root.val = subtreeAt C level.val 0) (hle : level.val ≤ depth.val) :
    virtual_root_loop inst h root depth level ⦃ r => bytes r.val = subtreeAt C depth.val 0 ⦄ := by
  unfold virtual_root_loop
  spec_split
  · rename_i hlt
    step as ⟨ a, ha ⟩
    have hza := bytes_zero_hashes level.val (by scalar_tac) a ha
    step with hash_nodes.spec inst h hl root a as ⟨ root1, hroot1 ⟩
    step as ⟨ level1, hlevel1 ⟩
    have hpow : 2 ^ level.val ≤ 2 ^ level1.val :=
      Nat.pow_le_pow_right (by decide) (by omega)
    apply WP.spec_mono (virtual_root_loop.spec C root1 depth level1 hdepth (by omega)
      (by
        rw [hroot1, hlevel1, subtreeAt_split, hroot, hza, Nat.zero_add,
          subtreeAt_past _ _ _ hcov, zeroSubtree_eq])
      (by scalar_tac))
    intro r hr; exact hr
  · simp only [WP.spec_ok]
    rename_i hge
    have : level.val = depth.val := by scalar_tac
    rw [← this]; exact hroot
termination_by depth.val - level.val
decreasing_by scalar_decr_tac

include hl in
/-- **`virtual_root`**: from the root of the subtree covering the `len` nodes to that of the
tree of height `depth`. -/
theorem virtual_root.spec (C : Array Bytes) (root : Node) (len depth : Std.Usize)
    (hC : C.size = len.val) (hdepth : depth.val ≤ 64) (hle : depthFor len.val ≤ depth.val)
    (hroot : bytes root.val = subtreeAt C (depthFor len.val) 0) :
    virtual_root inst h root len depth ⦃ r => bytes r.val = subtreeAt C depth.val 0 ⦄ := by
  unfold virtual_root
  step as ⟨ lev, hlev ⟩
  apply virtual_root_loop.spec inst h hl C root depth lev hdepth
    (by rw [hlev, hC]; exact le_two_pow_depthFor _) (by rw [hlev]; exact hroot)
    (by rw [hlev]; exact hle)

include hl in
/-- **`real_root_on_stack`**: the first level goes into a stack array, and from there it
continues with `real_root`. -/
theorem real_root_on_stack.spec (M : Std.Usize) (chunks : Slice Node)
    (h2 : 2 ≤ chunks.length) (hM : chunks.length ≤ 2 * M.val) :
    real_root_on_stack M inst h chunks ⦃ r =>
      bytes r.val = subtreeAt (chunksOf chunks.val) (depthFor chunks.length) 0 ⦄ := by
  unfold real_root_on_stack
  step as ⟨ s, back, hs, hback ⟩
  have hsl : s.length = M.val := by simp [Slice.length, hs]
  step as ⟨ a1, ha1 ⟩
  have hz0 := bytes_zero_hashes 0 (by omega) a1 ha1
  step with hl.hash_layer chunks s a1 (by rw [hsl]; omega) as ⟨ s1, hs1l, hs1par, hs1rest ⟩
  step as ⟨ i1, hi1 ⟩
  have hi1' : i1.val = (chunks.length + 1) / 2 := by
    rw [hi1, Nat.ceilDiv_eq_add_pred_div]; simp
  step as ⟨ s2, back2, hs2, hs2len, hback2 ⟩
  have hb1 : (back s1).val = s1.val := by
    rw [hback]; exact Array.from_slice_val _ _ (by scalar_tac)
  have hs2k : ∀ k < i1.val, s2.val[k]? = s1.val[k]? := by
    intro k hk
    rw [hs2, hb1, List.slice, List.drop_zero, List.getElem?_take]
    simp [hk]
  have hn64 : depthFor chunks.length ≤ 64 :=
    depthFor_le_64 _ (by have := usize_lt chunks.len; simpa using this)
  have hd := depthFor_half chunks.length h2
  have hC := chunksOf_size chunks.val
  step with real_root.spec inst h hl (chunksOf chunks.val) s2 1#usize (by scalar_tac)
    (by simp only [hC]; scalar_tac) (by simp only [hC]; scalar_tac)
    (by
      intro k hk
      rw [hs2k k (by scalar_tac)]
      have hk' : k < chunks.val.length / 2 + chunks.val.length % 2 := by scalar_tac
      rw [hs1par k hk']
      congr 1
      have := parentOf_subtreeAt (chunksOf chunks.val) 0 chunks.val a1
        (by
          intro m hm
          rw [subtreeAt_leaf, chunksOf_getElem?]
          simp [List.getElem?_eq_getElem hm])
        (by simp) hz0 k (by scalar_tac)
      simpa using this)
    (by
      have : s2.length = (chunks.length + 1) / 2 := by rw [hs2len, hi1']
      have h1 : (1#usize).val = 1 := rfl
      simp only [this, h1]; omega)
    as ⟨ a2, rest, ha2, hrest ⟩
  rw [ha2]
  congr 1
  simp only [hs2len, hi1']
  omega

/-- The leaves: node `k` is the subtree of height 0 at position `k`. -/
theorem leaves (l : List Node) (k : Nat) (hk : k < l.length) :
    (l[k]?.map fun n => bytes n.val) = some (subtreeAt (chunksOf l) 0 (k * 2 ^ 0)) := by
  rw [subtreeAt_leaf, chunksOf_getElem?]
  simp [List.getElem?_eq_getElem hk]

/-- What the specification requires: the root of the tree with the depth of the limit (or of
the nodes, without a limit), if the nodes do not exceed the limit. -/
theorem merkleizeBounded_ok (chunks : Slice Node) (limit : Option Std.Usize)
    (hlimit : ∀ l, limit = some l → chunks.length ≤ l.val) :
    merkleizeBoundedUnchecked (chunksOf chunks.val) (limit.map (·.val)) =
      .ok (subtreeAt (chunksOf chunks.val)
        (depthFor ((limit.map (·.val)).getD chunks.length)) 0) := by
  rw [merkleizeBoundedUnchecked_eq]
  rcases limit with _ | l
  · simp [chunksOf_size]; rfl
  · have := hlimit l rfl
    have hn : ¬ l.val < (chunksOf chunks.val).size := by simp [chunksOf_size]; omega
    simp only [Option.map_some, Option.getD_some, hn, ↓reduceIte]
    rfl

/-- The depth required by a limit or a `usize` length fits in the table. -/
theorem depth_cap_le_64 (chunks : Slice Node) (limit : Option Std.Usize) :
    depthFor ((limit.map (·.val)).getD chunks.length) ≤ 64 := by
  apply depthFor_le_64
  rcases limit with _ | l
  · have := usize_lt chunks.len; simpa using this
  · simpa using usize_lt l

include hl in
/-- **`merkleize` is EthLib's `merkleizeBoundedUnchecked`**, with or without a limit, when
the nodes do not exceed the limit. -/
theorem merkleize.spec (chunks : Slice Node) (limit : Option Std.Usize)
    (hlimit : ∀ l, limit = some l → chunks.length ≤ l.val) :
    merkleize inst h chunks limit ⦃ r =>
      merkleizeBoundedUnchecked (chunksOf chunks.val) (limit.map (·.val)) =
        .ok (bytes r.val) ⦄ := by
  rw [merkleizeBounded_ok chunks limit hlimit]
  suffices hs : merkleize inst h chunks limit ⦃ r => bytes r.val = subtreeAt (chunksOf chunks.val)
      (depthFor ((limit.map (·.val)).getD chunks.length)) 0 ⦄ by
    exact WP.spec_mono hs (fun r hr => by rw [hr])
  have hcap : chunks.length ≤ (limit.map (·.val)).getD chunks.length := by
    rcases limit with _ | l
    · simp
    · simpa using hlimit l rfl
  have hd64 := depth_cap_le_64 chunks limit
  have hC := chunksOf_size chunks.val
  unfold merkleize
  step with tree_depth.spec chunks.len limit (by intro l hl; simpa using hlimit l hl)
    as ⟨ depth, hdepth ⟩
  have hdepth' : depth.val = depthFor ((limit.map (·.val)).getD chunks.length) := by
    simpa using hdepth
  step as ⟨ b, hb ⟩
  spec_split
  · rename_i hempty
    step as ⟨ a, ha ⟩
    have hza := bytes_zero_hashes depth.val (by omega) a ha
    have h0 : chunks.length = 0 := by scalar_tac
    rw [hza, ← hdepth', subtreeAt_past _ _ _ (by simp [hC, h0]), zeroSubtree_eq]
  · rename_i hne
    have h1 : 1 ≤ chunks.length := by scalar_tac
    have hle : depthFor chunks.length ≤ depth.val :=
      hdepth' ▸ depthFor_le_depthFor hcap
    have hvirt : ∀ root : Node,
        bytes root.val = subtreeAt (chunksOf chunks.val) (depthFor chunks.length) 0 →
        virtual_root inst h root chunks.len depth ⦃ r => bytes r.val =
          subtreeAt (chunksOf chunks.val) (depthFor ((limit.map (·.val)).getD chunks.length)) 0 ⦄ := by
      intro root hroot
      apply WP.spec_mono (virtual_root.spec inst h hl (chunksOf chunks.val) root chunks.len depth
        (by simp [hC]) (by omega) (by simpa using hle) (by simpa using hroot))
      intro r hr
      rw [hr, hdepth']
    split
    · rename_i hone
      have hone' : chunks.length = 1 := by scalar_tac
      step as ⟨ root, hroot ⟩
      apply hvirt root
      rw [hone', depthFor_one]
      have := leaves chunks.val 0 (by scalar_tac)
      rw [List.getElem?_eq_getElem (by scalar_tac), ← hroot] at this
      simpa using this
    · rename_i hone
      have h2 : 2 ≤ chunks.length := by scalar_tac
      split
      · rename_i h8
        step with real_root_on_stack.spec inst h hl 4#usize chunks h2 (by scalar_tac)
          as ⟨ root, hroot ⟩
        exact hvirt root hroot
      · rename_i h8
        split
        · rename_i h32
          step with real_root_on_stack.spec inst h hl 16#usize chunks h2 (by scalar_tac)
            as ⟨ root, hroot ⟩
          exact hvirt root hroot
        · rename_i h32
          have hclone : ∀ x ∈ chunks.val,
              (core.clone.CloneArray 32#usize core.clone.CloneU8).clone x = ok x :=
            fun x _ => clone_node x
          step as ⟨ v, hv ⟩
          simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
          rw [← hv]
          have hn64 : depthFor chunks.length ≤ 64 :=
            depthFor_le_64 _ (by have := usize_lt chunks.len; simpa using this)
          have h0 : (0#usize).val = 0 := rfl
          step with real_root.spec inst h hl (chunksOf chunks.val) chunks 0#usize h1
            (by simp only [h0, Nat.pow_zero, Nat.mul_one, hC]; scalar_tac)
            (by simp only [h0, Nat.pow_zero, Nat.mul_one, hC]; scalar_tac)
            (fun k hk => by simpa using leaves chunks.val k hk) (by simpa using hn64)
            as ⟨ r1, hroot1, hrest1 ⟩
          rcases r1 with ⟨ root1, rest1 ⟩
          change WP.spec (Std.bind (ok root1)
            (fun root => virtual_root inst h root chunks.len depth)) _
          rw [bind_ok]
          exact hvirt root1 (by simpa using hroot1)

include hl in
/-- **`merkleize_in_place` is EthLib's `merkleizeBoundedUnchecked`**, same as `merkleize`.
What is left in `chunks` is unspecified; only its length is. -/
theorem merkleize_in_place.spec (chunks : Slice Node) (limit : Option Std.Usize)
    (hlimit : ∀ l, limit = some l → chunks.length ≤ l.val) :
    merkleize_in_place inst h chunks limit ⦃ root rest =>
      merkleizeBoundedUnchecked (chunksOf chunks.val) (limit.map (·.val)) =
        .ok (bytes root.val) ∧ rest.length = chunks.length ⦄ := by
  rw [merkleizeBounded_ok chunks limit hlimit]
  have hcap : chunks.length ≤ (limit.map (·.val)).getD chunks.length := by
    rcases limit with _ | l
    · simp
    · simpa using hlimit l rfl
  have hd64 := depth_cap_le_64 chunks limit
  have hC := chunksOf_size chunks.val
  unfold merkleize_in_place
  step with tree_depth.spec chunks.len limit (by intro l hl; simpa using hlimit l hl)
    as ⟨ depth, hdepth ⟩
  have hdepth' : depth.val = depthFor ((limit.map (·.val)).getD chunks.length) := by
    simpa using hdepth
  step as ⟨ b, hb ⟩
  spec_split
  · rename_i hempty
    step as ⟨ a, ha ⟩
    have hza := bytes_zero_hashes depth.val (by omega) a ha
    have h0 : chunks.length = 0 := by scalar_tac
    rw [hza, ← hdepth', subtreeAt_past _ _ _ (by simp [hC, h0]), zeroSubtree_eq]
  · rename_i hne
    have h1 : 1 ≤ chunks.length := by scalar_tac
    have hle : depthFor chunks.length ≤ depth.val :=
      hdepth' ▸ depthFor_le_depthFor hcap
    have hn64 : depthFor chunks.length ≤ 64 :=
      depthFor_le_64 _ (by have := usize_lt chunks.len; simpa using this)
    have h0 : (0#usize).val = 0 := rfl
    step with real_root.spec inst h hl (chunksOf chunks.val) chunks 0#usize h1
      (by simp only [h0, Nat.pow_zero, Nat.mul_one, hC]; scalar_tac)
      (by simp only [h0, Nat.pow_zero, Nat.mul_one, hC]; scalar_tac)
      (fun k hk => by simpa using leaves chunks.val k hk) (by simpa using hn64)
      as ⟨ root, rest, hroot, hrest ⟩
    step with virtual_root.spec inst h hl (chunksOf chunks.val) root chunks.len depth
      (by simp [hC]) (by omega) (by simpa using hle) (by simpa using hroot)
      as ⟨ a, ha ⟩
    refine ⟨ ?_, hrest ⟩
    rw [ha, hdepth']

end Real

end Libssz.Merkle
