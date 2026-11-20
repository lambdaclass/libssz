module
public import Aeneas
@[expose] public section

/-!
# Hand-written models of standard library functions

libssz uses six functions from the Rust standard library that the Aeneas Lean library does
not model yet. Here is what we **assume** they do. This file is part of the trusted computing
base (TCB) of libssz: the theorems talk about these definitions, not about the code of `core`
and `alloc`.

All of them follow the Rust documentation.

**Reinterpreting memory without copying it.** Internally they are `unsafe` code in
`core`/`alloc`, which is why Aeneas cannot extract them:

* `<[T]>::as_chunks::<N>()` splits a slice into chunks of `N` elements and also returns the
  remainder, what is left at the end and does not fill a whole chunk.
* `<[[T; N]]>::as_flattened()` is the inverse: it views a slice of arrays as a flat slice.
* `Vec::<[T; N]>::into_flattened()` is the same as `as_flattened`, but on an owned `Vec`: it
  returns a `Vec<T>` with the same elements.
* `Vec::into_boxed_slice()` turns the `Vec<T>` into a `Box<[T]>` with the same elements
  (dropping any spare capacity).

In Rust the result of the first two points to the same memory as the argument. The functional
model of Aeneas does not distinguish this, and it does not need to, because both borrows are
shared (`&`), so nobody can modify the memory while they exist. The other two consume their
argument.

**`iter.map(f)`.** Aeneas models `Iterator::next` of `slice::Iter` and `collect` into a `Vec`,
but not the `Map` adapter:

* `Iterator::map` only stores the iterator and the function (it is lazy: it calls nothing).
* `<Map<I, F> as Iterator>::next` asks the inner iterator for the next element and, if there
  is one, applies the function to it. In `core` it is `self.iter.next().map(&mut self.f)`.
-/

open Aeneas Aeneas.Std Result

namespace Libssz.StdModel

/-- Chunk `i` of `N` elements of `l`. -/
def chunk {T : Type _} (N : Nat) (l : List T) (i : Nat) : List T := (l.drop (i * N)).take N

theorem chunk_length {T : Type _} (N : Nat) (l : List T) (i : Nat) (hi : i < l.length / N) :
    (chunk N l i).length = N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have h1 : (i + 1) * N ≤ l.length := (Nat.le_div_iff_mul_le hN).mp hi
  rw [Nat.add_mul, Nat.one_mul] at h1
  simp only [chunk, List.length_take, List.length_drop]
  omega

/-- `<[T]>::as_chunks::<N>()`: the `len / N` full chunks, and the remainder.

With `N = 0` Rust panics (`assert!(N != 0, "chunk size must be non-zero")`), and so does this
model: any theorem saying the code does not fail has to prove `N ≠ 0`. -/
def as_chunks {T : Type _} (N : Std.Usize) (s : Slice T) :
    Result ((Slice (Array T N)) × (Slice T)) :=
  if N.val = 0 then fail .panic
  else
    let n := s.val.length / N.val
    let chunks : List (Array T N) :=
      List.ofFn fun (i : Fin n) => Array.from (chunk N.val s.val i.val) (chunk_length _ _ _ i.isLt)
    let remainder : List T := s.val.drop (n * N.val)
    ok (Slice.from chunks (by
          have h1 : n ≤ s.val.length := Nat.div_le_self _ _
          have h2 : s.val.length ≤ Usize.max := s.length_ineq
          simp only [chunks, List.length_ofFn]; omega),
        Slice.from remainder (by
          have h2 : s.val.length ≤ Usize.max := s.length_ineq
          simp only [remainder, List.length_drop]; omega))

/-- `<[[T; N]]>::as_flattened()`: the arrays, one after the other.

Rust panics if `len * N` does not fit in a `usize` (this can only happen with zero-sized
types). Here it is the same, stated on the length of the result. -/
def as_flattened {T : Type _} {N : Std.Usize} (s : Slice (Array T N)) : Result (Slice T) :=
  let plano : List T := (s.val.map fun a => a.val).flatten
  if h : plano.length ≤ Usize.max then ok (Slice.from plano h)
  else fail .panic

/-- `Vec::<[T; N]>::into_flattened()`: the arrays, one after the other, in a `Vec`.

Like `as_flattened`: Rust panics if `len * N` does not fit in a `usize`. -/
def into_flattened {T : Type _} {N : Std.Usize} (v : alloc.vec.Vec (Array T N)) :
    Result (alloc.vec.Vec T) :=
  let plano : List T := (v.val.map fun a => a.val).flatten
  if h : plano.length ≤ Usize.max then ok (alloc.vec.Vec.from plano h)
  else fail .panic

/-- `Vec::into_boxed_slice()`: the same elements, as `Box<[T]>`. (Aeneas translates
`Box<[T]>` as `Slice T`, and a `Vec T` is a `Slice T` under another name.) -/
def into_boxed_slice {T : Type _} (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok v.slice

/-- `Iterator::map`: stores the iterator and the function. -/
def iter_map {I : Type _} {F : Type _} (iter : I) (f : F) :
    Result (core.iter.adapters.map.Map I F) :=
  ok ⟨iter, f⟩

/-- `<Map<I, F> as Iterator>::next`: the next element of the inner iterator, passed through
the function. If the inner iterator or the function fails, it fails. -/
def map_next {B : Type _} {I : Type _} {F : Type _} {Item : Type _}
    (iterInst : core.iter.traits.iterator.Iterator I Item)
    (fnInst : core.ops.function.FnMut F Item B) (m : core.iter.adapters.map.Map I F) :
    Result ((Option B) × (core.iter.adapters.map.Map I F)) := do
  let (opt, iter) ← iterInst.next m.iter
  match opt with
  | none => ok (none, ⟨iter, m.f⟩)
  | some x =>
    let (y, f) ← fnInst.call_mut m.f x
    ok (some y, ⟨iter, f⟩)

end Libssz.StdModel
