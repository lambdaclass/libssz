module
public import Libssz.Merkle.Proofs.Kernel
@[expose] public section

/-!
# Hashers that satisfy the specification

The `ssz-merkle` tree (`merkleize`, `mix_in_length`, …) takes the hasher as a parameter
(`&impl Sha256Hasher`) and only uses it through three methods: `hash_pair`, `hash_layer` and
`hash_layer_in_place`. `Lawful` states what those three must do for the tree to be the one in
the specification: compute EthLib's `combine`.

Two ways to satisfy it, both proved here:

* **The trait's default methods.** The default `hash_layer` and `hash_layer_in_place` are
  `layer` and `layer_in_place`, which call `hash_pair` one pair at a time. It suffices that
  `hash_pair` computes `combine` (`Lawful.of_hash_pair`).
* **The SHA-NI kernel.** `shaniHasher` has the methods that `Sha2Hasher` uses when the
  processor has the SHA instructions (`shani_lawful`).

`Sha2Hasher` itself is not extracted: its `hash` calls the `sha2` crate, and it chooses
between the kernel and `sha2` with `shani::available()`, the processor detection.
`shaniHasher` copies by hand what `Sha2Hasher` does when that detection returns true; see the
TCB in the README.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz (combine)

namespace Libssz.Merkle

/-- What one tree layer leaves in `r`, written over `out` from the nodes `src`: the first
`⌈|src| / 2⌉` slots are the parents according to the specification (`parentOf`, with `zero`
as the sibling of the last node if one is left over), and the rest of `out` is unchanged. -/
abbrev LayerPost (src : List Node) (zero : Node) (out r : Slice Node) : Prop :=
  r.length = out.length ∧
  (∀ j, j < (src.length / 2 + src.length % 2) →
    (r.val[j]?.map fun n => bytes n.val) = some (parentOf src zero j)) ∧
  (∀ j, (src.length / 2 + src.length % 2) ≤ j → r.val[j]? = out.val[j]?)

/-- **A hasher that satisfies the specification**: its three methods compute EthLib's
`combine`. The layers do not fail if `out` has room for all the parents. -/
structure Lawful {H : Type} (inst : Sha256Hasher H) (h : H) : Prop where
  hash_pair : ∀ a b, inst.hash_pair h a b ⦃ r =>
    bytes r.val = combine (bytes a.val) (bytes b.val) ⦄
  hash_layer : ∀ (nodes out : Slice Node) (zero : Node),
    nodes.length / 2 + nodes.length % 2 ≤ out.length →
    inst.hash_layer h nodes out zero ⦃ r => LayerPost nodes.val zero out r ⦄
  hash_layer_in_place : ∀ (nodes : Slice Node) (zero : Node),
    inst.hash_layer_in_place h nodes zero ⦃ r => LayerPost nodes.val zero nodes r ⦄

/-! ## The SHA-NI kernel -/

/-- The empty slice, the `&[]` that `Sha2Hasher::hash_layer_in_place` passes to the kernel. -/
def emptyNodes : Slice Node := Slice.new Node

/-- The methods of `Sha2Hasher` when `shani::available()` returns true (`lib.rs`):
`hash_pair` and `hash_layer` are the kernel's, and `hash_layer_in_place` is `hash_layer` with
`in_place = true`. `hash` is the one from the `sha2` crate, which the tree does not use: it
stays a parameter. -/
def shaniHasher (hash : Unit → Slice Std.U8 → Result Node) : Sha256Hasher Unit where
  hash := hash
  hash_pair := fun _ a b => shani.hash_pair a b
  hash_layer := fun _ nodes out zero => shani.hash_layer nodes out false zero
  hash_layer_in_place := fun _ nodes zero => shani.hash_layer emptyNodes nodes true zero

/-- **The SHA-NI kernel satisfies the specification.** -/
theorem shani_lawful (hash : Unit → Slice Std.U8 → Result Node) :
    Lawful (shaniHasher hash) () where
  hash_pair a b := hash_pair.spec a b
  hash_layer nodes out zero h := by
    apply WP.spec_mono (hash_layer.spec nodes out false zero (by simpa [sourceOf] using h))
    intro r ⟨ hl, hpar, hrest ⟩
    exact ⟨ hl, fun j hj => hpar j (by simpa [sourceOf] using hj),
      fun j hj => hrest j (by simpa [sourceOf] using hj) ⟩
  hash_layer_in_place nodes zero := by
    apply WP.spec_mono (hash_layer.spec emptyNodes nodes true zero (by simp [sourceOf]; omega))
    intro r ⟨ hl, hpar, hrest ⟩
    exact ⟨ hl, fun j hj => hpar j (by simpa [sourceOf] using hj),
      fun j hj => hrest j (by simpa [sourceOf] using hj) ⟩

/-! ## The default methods -/

section Default

variable {H : Type} (inst : Sha256Hasher H) (h : H)
  (hp : ∀ a b, inst.hash_pair h a b ⦃ r => bytes r.val = combine (bytes a.val) (bytes b.val) ⦄)

include hp in
/-- The loop of `layer`: parent `k` in `out[k]`, for `k` from `k` up to `pairs`. -/
theorem layer_loop.spec (nodes out : Slice Node) (zero : Node) (pairs k : Std.Usize)
    (hpairs : pairs.val = nodes.length / 2) (hk : k.val ≤ pairs.val)
    (hout : pairs.val ≤ out.length) :
    layer_loop inst h nodes out pairs k ⦃ r =>
      r.length = out.length ∧
      (∀ j, k.val ≤ j → j < pairs.val →
        (r.val[j]?.map fun n => bytes n.val) = some (parentOf nodes.val zero j)) ∧
      (∀ j, j < k.val ∨ pairs.val ≤ j → r.val[j]? = out.val[j]?) ⦄ := by
  unfold layer_loop
  spec_split
  · step as ⟨ i, hi ⟩
    step as ⟨ a, ha ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ a1, ha1 ⟩
    step with hp as ⟨ a2, ha2 ⟩
    step as ⟨ s, hs ⟩
    step as ⟨ k1, hk1 ⟩
    have hsl : s.length = out.length := by
      rw [hs]; simp only [Slice.length, Slice.set_val_eq, List.length_set]
    apply WP.spec_mono (layer_loop.spec nodes s zero pairs k1 hpairs (by scalar_tac)
      (by rw [hsl]; exact hout))
    intro r ⟨ hl, hpar, hrest ⟩
    refine ⟨ by rw [hl, hsl], ?_, ?_ ⟩
    · intro j hj1 hj2
      by_cases hjk : j = k.val
      · subst hjk
        rw [hrest k.val (Or.inl (by scalar_tac)), hs, Slice.set_val_eq,
          List.getElem?_set_self (by scalar_tac)]
        simp only [Option.map_some, ha2]
        rw [parentOf_eq _ zero k.val a a1]
        · exact getElem?_of_eq _ i.val _ (by scalar_tac) a ha (by scalar_tac)
        · rw [getElem?_of_eq _ i1.val _ (by scalar_tac) a1 ha1 (by scalar_tac)]
          rfl
      · exact hpar j (by scalar_tac) hj2
    · intro j hj
      rw [hrest j (by scalar_tac), hs, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
  · simp only [WP.spec_ok]
    exact ⟨ by trivial, fun j h1 h2 => by scalar_tac, fun j _ => by trivial ⟩
termination_by pairs.val - k.val
decreasing_by scalar_decr_tac

include hp in
/-- **`layer` (the default `hash_layer`) satisfies the specification.** -/
theorem layer.spec (nodes out : Slice Node) (zero : Node)
    (hout : nodes.length / 2 + nodes.length % 2 ≤ out.length) :
    layer inst h nodes out zero ⦃ r => LayerPost nodes.val zero out r ⦄ := by
  unfold layer
  step as ⟨ pairs, hpairs ⟩
  step with layer_loop.spec inst h hp nodes out zero pairs 0#usize
    (by scalar_tac) (by scalar_tac) (by scalar_tac) as ⟨ out1, hl1, hpar1, hrest1 ⟩
  step as ⟨ i2, hi2 ⟩
  spec_split
  · rename_i hone
    have hone' : i2.val = 1 := by rw [hone]; rfl
    step as ⟨ i3, hi3 ⟩
    step as ⟨ a, ha ⟩
    step with hp as ⟨ a1, ha1 ⟩
    step as ⟨ r, hr ⟩
    refine ⟨ ?_, ?_, ?_ ⟩
    · rw [hr]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    · intro j hj
      by_cases hjk : j = pairs.val
      · subst hjk
        rw [hr, Slice.set_val_eq, List.getElem?_set_self (by scalar_tac)]
        simp only [Option.map_some, ha1]
        rw [parentOf_eq _ zero pairs.val a zero]
        · exact getElem?_of_eq _ i3.val _ (by scalar_tac) a ha (by scalar_tac)
        · rw [List.getElem?_eq_none (by scalar_tac)]
          rfl
      · rw [hr, Slice.set_val_eq, List.getElem?_set_ne (Ne.symm hjk)]
        exact hpar1 j (Nat.zero_le _) (by scalar_tac)
    · intro j hj
      rw [hr, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
      exact hrest1 j (Or.inr (by scalar_tac))
  · simp only [WP.spec_ok]
    refine ⟨ hl1, ?_, ?_ ⟩
    · intro j hj
      exact hpar1 j (Nat.zero_le _) (by scalar_tac)
    · intro j hj
      exact hrest1 j (Or.inr (by scalar_tac))

include hp in
/-- The loop of `layer_in_place`. What has not been read yet, from `k` on, is still the layer
below (`src`): parent `k` is written to `nodes[k]` and `nodes[2k]` and `nodes[2k + 1]` are
read, with `k ≤ 2k`. -/
theorem layer_in_place_loop.spec (nodes : Slice Node) (zero : Node) (pairs k : Std.Usize)
    (src : List Node) (hlen : nodes.length = src.length)
    (hsrc : ∀ j, k.val ≤ j → nodes.val[j]? = src[j]?)
    (hpairs : pairs.val = src.length / 2) (hk : k.val ≤ pairs.val) :
    layer_in_place_loop inst h nodes pairs k ⦃ r =>
      r.length = nodes.length ∧
      (∀ j, k.val ≤ j → j < pairs.val →
        (r.val[j]?.map fun n => bytes n.val) = some (parentOf src zero j)) ∧
      (∀ j, j < k.val ∨ pairs.val ≤ j → r.val[j]? = nodes.val[j]?) ⦄ := by
  unfold layer_in_place_loop
  spec_split
  · step as ⟨ i, hi ⟩
    step as ⟨ a, ha ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ a1, ha1 ⟩
    step with hp as ⟨ parent, hparent ⟩
    step as ⟨ s, hs ⟩
    step as ⟨ k1, hk1 ⟩
    have hsl : s.length = nodes.length := by
      rw [hs]; simp only [Slice.length, Slice.set_val_eq, List.length_set]
    apply WP.spec_mono (layer_in_place_loop.spec s zero pairs k1 src (by rw [hsl, hlen])
      (by
        intro j hj
        rw [hs, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
        exact hsrc j (by scalar_tac))
      hpairs (by scalar_tac))
    intro r ⟨ hl, hpar, hrest ⟩
    refine ⟨ by rw [hl, hsl], ?_, ?_ ⟩
    · intro j hj1 hj2
      by_cases hjk : j = k.val
      · subst hjk
        rw [hrest k.val (Or.inl (by scalar_tac)), hs, Slice.set_val_eq,
          List.getElem?_set_self (by scalar_tac)]
        simp only [Option.map_some, hparent]
        rw [parentOf_eq _ zero k.val a a1]
        · rw [← hsrc (2 * k.val) (by omega)]
          exact getElem?_of_eq _ i.val _ (by scalar_tac) a ha (by scalar_tac)
        · rw [← hsrc (2 * k.val + 1) (by omega),
            getElem?_of_eq _ i1.val _ (by scalar_tac) a1 ha1 (by scalar_tac)]
          rfl
      · exact hpar j (by scalar_tac) hj2
    · intro j hj
      rw [hrest j (by scalar_tac), hs, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
  · simp only [WP.spec_ok]
    exact ⟨ by trivial, fun j h1 h2 => by scalar_tac, fun j _ => by trivial ⟩
termination_by pairs.val - k.val
decreasing_by scalar_decr_tac

include hp in
/-- **`layer_in_place` (the default `hash_layer_in_place`) satisfies the specification.** -/
theorem layer_in_place.spec (nodes : Slice Node) (zero : Node) :
    layer_in_place inst h nodes zero ⦃ r => LayerPost nodes.val zero nodes r ⦄ := by
  unfold layer_in_place
  step as ⟨ pairs, hpairs ⟩
  step with layer_in_place_loop.spec inst h hp nodes zero pairs 0#usize nodes.val rfl
    (fun j _ => rfl) (by scalar_tac) (by scalar_tac) as ⟨ n1, hl1, hpar1, hrest1 ⟩
  step as ⟨ i2, hi2 ⟩
  spec_split
  · rename_i hone
    have hone' : i2.val = 1 := by rw [hone]; rfl
    step as ⟨ i3, hi3 ⟩
    step as ⟨ a, ha ⟩
    step with hp as ⟨ parent, hparent ⟩
    step as ⟨ r, hr ⟩
    refine ⟨ ?_, ?_, ?_ ⟩
    · rw [hr]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    · intro j hj
      by_cases hjk : j = pairs.val
      · subst hjk
        rw [hr, Slice.set_val_eq, List.getElem?_set_self (by scalar_tac)]
        simp only [Option.map_some, hparent]
        rw [parentOf_eq _ zero pairs.val a zero]
        · rw [← hrest1 (2 * pairs.val) (Or.inr (by scalar_tac))]
          exact getElem?_of_eq _ i3.val _ (by scalar_tac) a ha (by scalar_tac)
        · rw [List.getElem?_eq_none (by scalar_tac)]
          rfl
      · rw [hr, Slice.set_val_eq, List.getElem?_set_ne (Ne.symm hjk)]
        exact hpar1 j (Nat.zero_le _) (by scalar_tac)
    · intro j hj
      rw [hr, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
      exact hrest1 j (Or.inr (by scalar_tac))
  · simp only [WP.spec_ok]
    refine ⟨ hl1, ?_, ?_ ⟩
    · intro j hj
      exact hpar1 j (Nat.zero_le _) (by scalar_tac)
    · intro j hj
      exact hrest1 j (Or.inr (by scalar_tac))

include hp in
/-- **A hasher that only defines `hash_pair`, leaving the other two methods as defaults,
satisfies the specification if its `hash_pair` computes `combine`.** -/
theorem Lawful.of_hash_pair
    (hl : ∀ nodes out zero, inst.hash_layer h nodes out zero = layer inst h nodes out zero)
    (hlp : ∀ nodes zero, inst.hash_layer_in_place h nodes zero =
      layer_in_place inst h nodes zero) :
    Lawful inst h where
  hash_pair := hp
  hash_layer nodes out zero hout := by rw [hl]; exact layer.spec inst h hp nodes out zero hout
  hash_layer_in_place nodes zero := by rw [hlp]; exact layer_in_place.spec inst h hp nodes zero

end Default

end Libssz.Merkle
