module
public import Aeneas
@[expose] public section

/-!
# Handwritten model of `SmallVec` (crate `smallvec` 1.16)

`SszBitlist` and `SszBitvector` (crate `ssz-types`) store their bytes in a
`SmallVec<[u8; 64]>`: a vector that keeps up to 64 items inline and, beyond that, requests them
from the allocator. Charon does not translate the `smallvec` crate (it is a separate crate, and it
uses `unsafe` internally), so Aeneas leaves the type and the five functions `ssz-types` uses as
holes. This file is their model; `scripts/complete_externals_types.py` plugs it in.

**What is assumed.** That a `SmallVec` behaves like a `Vec` of its items: where they are stored
does not change its contents. Each function is the `Vec` (or slice) function that the `smallvec`
documentation says does the same thing:

* `SmallVec<A>`: a `Vec` of the items of `A` (Aeneas passes the item type, `A::Item`, as a
  parameter);
* `from_slice(s)`: a vector with a copy of the items of `s`;
* `deref`: the slice of its items;
* `index_mut`: that of a `Vec`, with the same index (fails out of range, as in Rust);
* `truncate(len)`: keeps the first `len` items; if it has `len` or fewer, it does not change;
* `<[T; 64] as smallvec::Array>::size()`: 64.

As in Aeneas's model of `Vec`, running out of memory is not modeled.

The model was chosen instead of replacing `SmallVec` with a `Vec` in libssz because with a `Vec`
decoding and encoding small bitfields is slower (one memory allocation per bitfield): see the
README.
-/

open Aeneas Aeneas.Std Result

namespace Libssz.SmallVecModel

/-- A `SmallVec<A>` is a vector of the items of `A`. -/
abbrev SmallVec (_A : Type) (Item : Type) : Type := alloc.vec.Vec Item

/-- `SmallVec::from_slice`: a copy of the slice's items. -/
def from_slice {Item : Type} (s : Slice Item) : Result (alloc.vec.Vec Item) :=
  ok ⟨s⟩

/-- `<SmallVec as Deref>::deref`: the slice of the items. -/
def deref {Item : Type} (v : alloc.vec.Vec Item) : Result (Slice Item) :=
  ok (alloc.vec.Vec.deref v)

/-- `SmallVec::truncate`: the first `len` items, or all of them if there are `len` or fewer. -/
def truncate {Item : Type} (v : alloc.vec.Vec Item) (len : Std.Usize) :
    Result (alloc.vec.Vec Item) :=
  ok (alloc.vec.Vec.from (v.val.take len.val) (by have := v.property; simp only [List.length_take]; omega))

end Libssz.SmallVecModel
