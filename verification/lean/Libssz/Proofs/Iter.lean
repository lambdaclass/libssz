module
public import Libssz.Code.Funs
import all Aeneas.Std.Alloc.Vec.IntoIter
@[expose] public section

/-!
# `slice.iter().map(f).collect::<Vec<_>>()`

In libssz, lists of integers are built with an iterator: `chunks.iter().map(|c|
u64::from_le_bytes(*c)).collect()` (decode) and `items.iter().map(|x| x.to_le_bytes()).collect()`
(encode into a new `Vec`). There is only one fact to know about that chain,
`collect_map_slice`: if the closure is a pure function `g`, the result is `s.map g`.

What is used from each model:

* `slice::Iter` and `Iterator::collect` for `Vec` (`iterToList`): from the Aeneas library;
* `Iterator::map` and `<Map<I, F> as Iterator>::next`: written by hand in `StdModel.lean`.
-/

open Aeneas Aeneas.Std Result
open libssz_codec

namespace Libssz.Proofs

/-- One step of `s.iter().map(f)` stopped at position `i`, when the closure computes the pure
function `g` and does not change state. -/
theorem map_slice_next {F T B : Type} (inst : core.ops.function.FnMut F T B) (g : T → B) (f : F)
    (hg : ∀ x, inst.call_mut f x = ok (g x, f)) (s : Slice T) (i : Nat) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      (core.iter.traits.iterator.IteratorSliceIter T) inst ⟨⟨s, i⟩, f⟩ =
    if h : i < s.length then ok (some (g (s.val[i]'h)), ⟨⟨s, i + 1⟩, f⟩)
    else ok (none, ⟨⟨s, i⟩, f⟩) := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next StdModel.map_next
  simp only [core.slice.iter.IteratorSliceIter.next]
  by_cases h : i < s.length
  · simp [h, hg]
    rfl
  · simp [h]

/-- `iterToList` on `s.iter().map(f)` from position `i`: the accumulator, then `g` of what
remains. -/
theorem iterToList_map_slice {F T B : Type} (inst : core.ops.function.FnMut F T B) (g : T → B)
    (f : F) (hg : ∀ x, inst.call_mut f x = ok (g x, f)) (s : Slice T) :
    ∀ (n i : Nat) (acc : List B), n = s.length - i → i ≤ s.length →
    alloc.vec.FromIteratorVec.iterToList
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorSliceIter T) inst) ⟨⟨s, i⟩, f⟩ acc
    = ok (acc.reverse ++ (s.val.drop i).map g) := by
  intro n
  induction n with
  | zero =>
    intro i acc hn hi
    have hi' : ¬ i < s.length := by omega
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator]
    rw [map_slice_next inst g f hg s i]
    simp [hi', List.drop_eq_nil_of_le (show s.val.length ≤ i by simpa [Slice.length] using hi')]
  | succ n ih =>
    intro i acc hn hi
    have hi' : i < s.length := by omega
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator]
    rw [map_slice_next inst g f hg s i]
    simp only [hi', ↓reduceDIte, bind_ok]
    have := ih (i + 1) (g (s.val[i]'hi') :: acc) (by omega) (by omega)
    simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator] at this
    refine Eq.trans this ?_
    have hd : (s.val.drop i).map g = g (s.val[i]'hi') :: (s.val.drop (i + 1)).map g := by
      rw [List.drop_eq_getElem_cons (show i < s.val.length from hi')]; rfl
    rw [hd, List.reverse_cons, List.append_assoc]; rfl

/-- **`s.iter().map(f).collect::<Vec<_>>()`** does not fail and is `s.map g`. -/
theorem collect_map_slice {F T B : Type} (inst : core.ops.function.FnMut F T B) (g : T → B)
    (f : F) (hg : ∀ x, inst.call_mut f x = ok (g x, f)) (s : Slice T) :
    core.iter.traits.iterator.Iterator.collect.default
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorSliceIter T) inst)
      (core.iter.traits.collect.FromIteratorVec B) ⟨⟨s, 0⟩, f⟩ ⦃ v => v.val = s.val.map g ⦄ := by
  unfold core.iter.traits.iterator.Iterator.collect.default
  simp only [alloc.vec.FromIteratorVec.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
  rw [iterToList_map_slice inst g f hg s s.length 0 [] (by simp) (by simp)]
  simp

end Libssz.Proofs
