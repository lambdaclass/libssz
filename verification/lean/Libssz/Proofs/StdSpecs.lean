module
public import Libssz.Proofs.Bridge
public import Libssz.Proofs.Iter
public import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import all Aeneas.Data.List.List
@[expose] public section

/-!
# What the proofs use from the hand-written models

`StdModel.lean` states what we **assume** six standard library functions do. Here is, as
theorems, the only thing the proofs use from those models:

* `as_chunks_spec`: `as_chunks::<N>()` with `N > 0` does not fail and returns the `len / N`
  chunks and the remainder; `flatten_chunks` says that the chunks, laid end to end, are the
  prefix of the slice.
* `as_flattened_spec` and `into_flattened_spec`: `as_flattened()` and `into_flattened()` do
  not fail if the result fits in a `usize`, and are the concatenation.
* `collect_map_slice` (in `Iter.lean`): `slice.iter().map(f).collect::<Vec<_>>()` is `List.map`.

Plus three list lemmas used by the loops that write into already-allocated memory.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz_codec
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## List lemmas -/

/-- Writing position `i` and keeping the first `i + 1`: the first `i` from before, and the new
value. -/
theorem take_succ_set {α : Type} (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl i)]
  simp [h]

/-- Overwriting `le` in `A ++ Z` right after `A`. -/
theorem setSlice!_append {α : Type} (A Z le : List α) (h : le.length ≤ Z.length) :
    (A ++ Z).setSlice! A.length le = A ++ le ++ Z.drop le.length := by
  simp [List.setSlice!, Nat.min_eq_left h, List.drop_append]

/-- Growing with a fill value: what was there, plus the new fill. -/
theorem resize_grow {α : Type} (l : List α) (n : Nat) (x : α) (h : l.length ≤ n) :
    l.resize n x = l ++ List.replicate (n - l.length) x := by
  simp [List.resize, List.take_of_length_le h]

/-! ## `as_chunks`, `as_flattened`, `into_flattened` -/

/-- `as_chunks::<N>()` with `N > 0` does not fail, and returns the `len / N` chunks and the
remainder. -/
@[step]
theorem as_chunks_spec {T : Type} (N : Std.Usize) (s : Slice T) (hN : 0 < N.val) :
    core.slice.Slice.as_chunks N s ⦃ r =>
      r.1.val.map (·.val) = (List.range (s.length / N.val)).map (StdModel.chunk N.val s.val) ∧
      r.2.val = s.val.drop (s.length / N.val * N.val) ⦄ := by
  unfold core.slice.Slice.as_chunks StdModel.as_chunks
  have hN' : ¬ (N.val = 0) := by omega
  simp only [hN', ↓reduceIte, WP.spec_ok, Slice.from_val, and_true]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- The first `k` chunks of `N`, laid end to end, are the first `k * N` elements. -/
theorem flatten_chunks {T : Type} (N : Nat) (l : List T) (k : Nat) :
    ((List.range k).map (StdModel.chunk N l)).flatten = l.take (k * N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp [StdModel.chunk, Nat.succ_mul, List.take_add]

/-- The length of several `[T; N]` laid end to end. -/
theorem length_flatten_arrays {T : Type} {N : Std.Usize} (l : List (Array T N)) :
    ((l.map (·.val)).flatten).length = N.val * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_succ]; omega

/-- `as_flattened()` does not fail if the result fits in a `usize`, and is the concatenation. -/
@[step]
theorem as_flattened_spec {T : Type} {N : Std.Usize} (s : Slice (Array T N))
    (h : N.val * s.length ≤ Usize.max) :
    core.slice.SliceArray.as_flattened s ⦃ r =>
      r.val = (s.val.map (·.val)).flatten ∧ r.length = N.val * s.length ⦄ := by
  unfold core.slice.SliceArray.as_flattened StdModel.as_flattened
  have h' : ((s.val.map (·.val)).flatten).length ≤ Usize.max := by
    rw [length_flatten_arrays]; exact h
  simp only [h', ↓reduceDIte, WP.spec_ok, Slice.from_val, true_and, Slice.length]
  exact length_flatten_arrays _

/-- `into_flattened()`: the same, on an owned `Vec`. -/
@[step]
theorem into_flattened_spec {T : Type} {N : Std.Usize} (v : alloc.vec.Vec (Array T N))
    (h : N.val * v.length ≤ Usize.max) :
    alloc.vec.VecArray.into_flattened alloc.alloc.Global v ⦃ r =>
      r.val = (v.val.map (·.val)).flatten ∧ r.length = N.val * v.length ⦄ := by
  unfold alloc.vec.VecArray.into_flattened StdModel.into_flattened
  have h' : ((v.val.map (·.val)).flatten).length ≤ Usize.max := by
    rw [length_flatten_arrays]; exact h
  simp only [h', ↓reduceDIte, WP.spec_ok, alloc.vec.Vec.from_val, true_and, alloc.vec.Vec.length]
  exact length_flatten_arrays _

/-- The bytes of several `[u8; N]` laid end to end. -/
theorem bytes_flatten {N : Std.Usize} (l : List (Array Std.U8 N)) :
    bytes ((l.map (·.val)).flatten) = concatParts (l.map fun a => bytes a.val) := by
  induction l with
  | nil => simp [concatParts, bytes]
  | cons a l ih => simp [concatParts, ih]

end Libssz.Proofs
