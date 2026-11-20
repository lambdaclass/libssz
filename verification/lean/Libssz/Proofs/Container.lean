module
public import Libssz.Proofs.VarEncode
public import Libssz.Proofs.Uint
-- To reason about `List.resize` (used by `Vec::resize`), whose body Aeneas does not expose.
import all Aeneas.Data.List.List
@[expose] public section

/-!
# Containers (`ContainerEncoder`, `ContainerDecoder`), libssz ≡ EthLib

An `ssz-derive` container is not a library function: for each struct, the macro generates a
sequence of calls to `ContainerEncoder` and `ContainerDecoder`. That is why the proof has two
parts:

1. **The methods, generic in the field type.** Each one is specified over an invariant of
   the state:
   * `EncInv`: the buffer is what was there before, the fixed part written so far, zeros and
     the bodies. It is maintained by `with_capacity.spec`, `append_fixed.spec` (which uses
     `copy_within.spec`), `append_variable.spec` and `finalize.spec`.
   * `DecInv`: the input, the cursor, the offsets read and how many bodies have been decoded.
     It is maintained by `new.spec`, `decode_fixed.spec`, `read_first_offset.spec`,
     `read_next_offset.spec` and `decode_variable.spec`.

   The macro calls `decode_fixed_part` and `decode_variable_part` for each field, and those
   two have their own specifications, built from the ones above.

   These theorems hold for any container the macro generates.
2. **A concrete container.** `verif_example::Example` is `{a: u64, b: Vec<u8>, c: bool,
   d: Vec<u16>}`, with the `#[derive]` of `ssz-derive` (`crates/ssz/src/verif_example.rs`,
   behind the `verif-example` feature): the model is the code the macro generates. It is
   composed from the theorems above and compared with EthLib's
   `deserialize`/`serialize` on `.container names exFields`:
   * `Example.from_ssz_bytes.spec`: the decode, for every input shorter than 2³² bytes, with
     the errors of `ErrMatchC` (those of `ErrMatch` plus one case where the two sides check
     in a different order);
   * `Example.encode.agrees`: the encode, if the encoding is shorter than 2³²;
   * `Example.encode.diverges`: **the offset-overflow divergence in `ContainerEncoder`**.

On the EthLib side, `eth_decode` and `eth_encode` evaluate the container's `deserialize` and
`serialize` to a cascade of checks and to `exLayout`.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## `copy_within` -/

theorem copy_step {α : Type} (orig : List α) (d s k : Nat) (hk : s + k < orig.length)
    (hno : d + k < s) :
    (orig.take d ++ (orig.drop s).take k ++ orig.drop (d + k)).set (d + k) orig[s + k] =
      orig.take d ++ (orig.drop s).take (k + 1) ++ orig.drop (d + k + 1) := by
  have hA : (orig.take d).length = d := by simp; omega
  have hB : ((orig.drop s).take k).length = k := by simp; omega
  rw [List.set_append_right _ _ (by simp [hA, hB]), List.length_append, hA, hB, Nat.sub_self,
    List.drop_eq_getElem_cons (show d + k < orig.length by omega), List.set_cons_zero,
    List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hk]
  simp

theorem copy_within_loop0.spec (buf : Slice Std.U8) (src count dest k : Std.Usize)
    (orig : List Std.U8) (hk : k.val ≤ count.val) (hno : dest.val + count.val ≤ src.val)
    (hsrc : src.val + count.val ≤ orig.length)
    (hbuf : buf.val = orig.take dest.val ++ (orig.drop src.val).take k.val ++
      orig.drop (dest.val + k.val)) :
    encode.copy_within_loop0 buf src count dest k ⦃ buf' =>
      buf'.val = orig.take dest.val ++ (orig.drop src.val).take count.val ++
        orig.drop (dest.val + count.val) ⦄ := by
  unfold encode.copy_within_loop0
  have hlen : buf.length = orig.length := by
    simp only [Slice.length, hbuf, List.length_append, List.length_take, List.length_drop]
    omega
  spec_split
  · have hlt : k.val < count.val := by scalar_tac
    step as ⟨ i, hi ⟩
    step as ⟨ x, hx ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s, hs ⟩
    step as ⟨ k1, hk1 ⟩
    apply copy_within_loop0.spec s src count dest k1 orig (by scalar_tac) hno hsrc
    have hxv : x = orig[src.val + k.val]'(by omega) := by
      rw [hx]
      simp only [hbuf, hi]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_take, List.length_drop, List.getElem_drop]
      congr 1
      omega
    rw [hs, Slice.set_val_eq, hbuf, hi2, hk1, hxv]
    exact copy_step orig dest.val src.val k.val (by omega) (by omega)
  · simp only [WP.spec_ok]
    have : k.val = count.val := by scalar_tac
    rw [hbuf, this]
termination_by count.val - k.val
decreasing_by scalar_decr_tac

/-- `copy_within` when the destination lies before the source, without overlapping (the case
of `append_fixed`): copies `count` bytes from `src` to `dest`. -/
theorem copy_within.spec (buf : Slice Std.U8) (src count dest : Std.Usize)
    (hno : dest.val + count.val ≤ src.val) (hsrc : src.val + count.val ≤ buf.length) :
    encode.copy_within buf src count dest ⦃ buf' =>
      buf'.val = buf.val.take dest.val ++ (buf.val.drop src.val).take count.val ++
        buf.val.drop (dest.val + count.val) ⦄ := by
  unfold encode.copy_within
  have hl := Slice.len_val buf
  simp only [step_simps]
  step
  step as ⟨ i2, hi2 ⟩
  step
  step as ⟨ i4, hi4 ⟩
  step
  simp only [show dest ≤ src by scalar_tac, ↓reduceIte]
  exact copy_within_loop0.spec buf src count dest 0#usize buf.val (by simp) hno hsrc
    (by simp)

/-! ## `ContainerEncoder` -/

/-- The state of a `ContainerEncoder` partway through. The buffer holds, in order:
* what was there before the container started (`L0`);
* the fixed part written so far (`head`);
* zeros up to the `F` bytes of the fixed part;
* the bodies of the variable-size fields written so far (`body`). -/
def EncInv (ce : encode.ContainerEncoder) (L0 : List UInt8) (F : Nat) (head body : List UInt8) :
    Prop :=
  ce.buf.val.map byte = L0 ++ head ++ List.replicate (F - head.length) 0 ++ body ∧
  ce.start.val = L0.length ∧ ce.fixed_cursor.val = L0.length + head.length ∧
  ce.fixed_part_len.val = F ∧ head.length ≤ F

theorem EncInv.length {ce : encode.ContainerEncoder} {L0 : List UInt8} {F : Nat}
    {head body : List UInt8} (h : EncInv ce L0 F head body) :
    ce.buf.length = L0.length + F + body.length := by
  have := congrArg List.length h.1
  simp only [List.length_map, List.length_append, List.length_replicate] at this
  simp only [alloc.vec.Vec.length, this]
  have := h.2.2.2.2
  omega

theorem fixed_patch {α : Type} (P H B E : List α) (z : α) (F : Nat) (hH : H.length + E.length ≤ F)
    (L : List α) (hL : L = P ++ H ++ List.replicate (F - H.length) z ++ B ++ E) :
    (L.take (P.length + H.length) ++ (L.drop (P.length + F + B.length)).take E.length ++
       L.drop (P.length + H.length + E.length)).take (P.length + F + B.length) =
    P ++ (H ++ E) ++ List.replicate (F - (H ++ E).length) z ++ B := by
  subst hL
  have h1 : (P ++ H ++ List.replicate (F - H.length) z ++ B ++ E).take (P.length + H.length) =
      P ++ H := by
    rw [show P ++ H ++ List.replicate (F - H.length) z ++ B ++ E =
      (P ++ H) ++ (List.replicate (F - H.length) z ++ B ++ E) by simp only [List.append_assoc]]
    exact List.take_left' (by simp)
  have h2 : (P ++ H ++ List.replicate (F - H.length) z ++ B ++ E).drop (P.length + F + B.length) =
      E := by
    exact List.drop_left' (by simp; omega)
  have h3 : (P ++ H ++ List.replicate (F - H.length) z ++ B ++ E).drop
      (P.length + H.length + E.length) =
      List.replicate (F - H.length - E.length) z ++ B ++ E := by
    rw [show P ++ H ++ List.replicate (F - H.length) z ++ B ++ E =
      (P ++ H) ++ (List.replicate (F - H.length) z ++ (B ++ E)) by simp only [List.append_assoc],
      show P.length + H.length + E.length = (P ++ H).length + E.length by simp, ← List.drop_drop,
      List.drop_left, List.drop_append_of_le_length (by simp; omega), List.drop_replicate]
    simp only [List.append_assoc]
  rw [h1, h2, h3, List.take_of_length_le (le_refl _)]
  rw [show P ++ H ++ E ++ (List.replicate (F - H.length - E.length) z ++ B ++ E) =
    (P ++ (H ++ E) ++ List.replicate (F - (H ++ E).length) z ++ B) ++ E by
      simp only [List.append_assoc, List.length_append, Nat.sub_add_eq]]
  exact List.take_left' (by simp; omega)

theorem with_capacity.spec (buf : alloc.vec.Vec Std.U8) (F total : Std.Usize)
    (h : buf.length + F.val ≤ Usize.max) :
    encode.ContainerEncoder.with_capacity buf F total ⦃ ce back =>
      EncInv ce (buf.val.map byte) F.val [] [] ∧ ∀ c, back c = c.buf ⦄ := by
  unfold encode.ContainerEncoder.with_capacity
  simp only [alloc.vec.Vec.reserve, bind_ok]
  step as ⟨ i, hi ⟩
  step as ⟨ buf2, hbuf2 ⟩
  refine ⟨⟨?_, by simp, by simp, by simp, by simp⟩, by simp⟩
  rw [hbuf2, hi]
  simp [List.resize, alloc.vec.Vec.length, show byte 0#u8 = 0 from rfl]

theorem append_fixed.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (ce : encode.ContainerEncoder) (x : T) (L0 : List UInt8) (F : Nat) (head body : List UInt8)
    (hinv : EncInv ce L0 F head body) (hfit : head.length + (encOf x).size ≤ F)
    (hmax : ce.buf.length + (encOf x).size ≤ Usize.max) :
    encode.ContainerEncoder.append_fixed inst ce x ⦃ ce' back =>
      EncInv ce' L0 F (head ++ (encOf x).toList) body ∧ ∀ c, (back c).buf = c.buf ⦄ := by
  obtain ⟨hb, hst, hcur, hF, hhF⟩ := hinv
  have hlen := (show EncInv ce L0 F head body from ⟨hb, hst, hcur, hF, hhF⟩).length
  unfold encode.ContainerEncoder.append_fixed
  simp only [step_simps]
  step with helem x ce.buf hmax as ⟨ v, hv ⟩
  have hvl : v.val.map byte = ce.buf.val.map byte ++ (encOf x).toList := by
    have := congrArg Array.toList hv
    simpa [bytes] using this
  have hvlen : v.length = ce.buf.length + (encOf x).size := by
    have := congrArg List.length hvl
    simpa [alloc.vec.Vec.length] using this
  have hbl : ce.buf.len.val = ce.buf.length := by simp
  have hvl2 : v.len.val = v.length := by simp
  step as ⟨ written, hw ⟩
  have hwv : written.val = (encOf x).size := by rw [hw, hvl2, hbl, hvlen]; omega
  simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
  have hsl : v.slice.length = v.length := rfl
  step with copy_within.spec v.slice ce.buf.len written ce.fixed_cursor
    (by rw [hwv, hcur, hbl, hlen]; omega)
    (by rw [hsl, hbl, hwv, hvlen]) as ⟨ s1, hs1 ⟩
  step as ⟨ v2, hv2 ⟩
  step as ⟨ i1, hi1 ⟩
  refine ⟨⟨?_, hst, ?_, hF, by simp; omega⟩, by simp⟩
  · have hmapped := congrArg (List.map byte) hs1
    simp only [List.map_append, List.map_take, List.map_drop] at hmapped
    have hs1l : s1.val.length = v.length := by
      rw [hs1]; simp [hwv, hbl, hcur, hvlen, hlen, alloc.vec.Vec.length] at *; omega
    rw [hv2]
    simp only [List.resize, ge_iff_le, Nat.zero_le, ↓reduceIte]
    have hlv : List.map byte v.slice.val =
        L0 ++ head ++ List.replicate (F - head.length) 0 ++ body ++ (encOf x).toList := by
      rw [show v.slice.val = v.val from rfl, hvl, hb]
    change List.map byte (List.take ce.buf.len.val s1.val ++
      List.replicate (ce.buf.len.val - s1.val.length) 0#u8) = _
    rw [show ce.buf.len.val - s1.val.length = 0 by rw [hs1l, hbl, hvlen]; omega, List.replicate_zero,
      List.append_nil, List.map_take, hmapped, hcur, hbl, hlen, hwv]
    have := fixed_patch L0 head body (encOf x).toList 0 F (by simpa using hfit) _ hlv
    simpa using this
  · simp [hi1, hcur, hwv]; omega

/-- **`append_variable`**: writes the body's offset into the fixed part (with `as u32`, which
`uintBytes 4` also truncates to 32 bits) and appends the body at the end. -/
theorem append_variable.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (ce : encode.ContainerEncoder) (x : T) (L0 : List UInt8) (F : Nat) (head body : List UInt8)
    (hinv : EncInv ce L0 F head body) (hfit : head.length + 4 ≤ F)
    (hmax : ce.buf.length + (encOf x).size ≤ Usize.max) :
    encode.ContainerEncoder.append_variable inst ce x ⦃ ce' back =>
      EncInv ce' L0 F (head ++ (uintBytes 4 (F + body.length)).toList)
        (body ++ (encOf x).toList) ∧ ∀ c, (back c).buf = c.buf ⦄ := by
  obtain ⟨hb, hst, hcur, hF, hhF⟩ := hinv
  have hlen := (show EncInv ce L0 F head body from ⟨hb, hst, hcur, hF, hhF⟩).length
  unfold encode.ContainerEncoder.append_variable
  simp only [step_simps, BYTES_PER_LENGTH_OFFSET]
  have hbl : ce.buf.len.val = ce.buf.length := by simp
  step as ⟨ off, hoff ⟩
  have hoffv : off.val = F + body.length := by rw [hoff, hbl, hlen, hst]; omega
  step as ⟨ i1, hi1 ⟩
  step as ⟨ sl, back, hsl, hsll, hback ⟩
  simp only [lift, bind_ok, Array.to_slice]
  step as ⟨ s2, hs2 ⟩
  have hs2v : s2.val.map byte = (uintBytes 4 off.val).toList := by
    rw [hs2, Slice.from_val]
    simp only [core.num.U32.to_le_bytes, Array.from_val]
    have := bytes_toLEBytes 4 (UScalar.cast UScalarTy.U32 off).bv (by rfl)
    have h2 := congrArg Array.toList this
    simp only [bytes, List.toList_toArray] at h2
    rw [h2]
    have hc : (UScalar.cast UScalarTy.U32 off).bv.toNat = off.val % 2 ^ 32 := by
      have := UScalar.cast_val_eq UScalarTy.U32 off
      rw [UScalarTy.U32_numBits_eq] at this
      exact this
    rw [hc, uintBytes_mod32]
  have hs2l : s2.val.length = 4 := by
    have := congrArg List.length hs2v; simp [uintBytes_size] at this; simpa using this
  set U := (uintBytes 4 off.val).toList with hU
  have hUl : U.length = 4 := by simp [hU, uintBytes_size]
  have hpre : (L0 ++ head).length = ce.fixed_cursor.val := by simp [hcur]
  have hb1 : (back s2).val.map byte =
      L0 ++ head ++ U ++ List.replicate (F - head.length - 4) 0 ++ body := by
    have hbl2 : ce.fixed_cursor.val + s2.val.length ≤ ce.buf.val.length := by
      rw [hs2l]; simp only [alloc.vec.Vec.length] at hlen; omega
    rw [hback, vec_setSlice_val, map_setSlice! _ _ _ _ hbl2,
      setSlice!_eq _ _ _ (by simpa using hbl2), hb, hs2v, hUl]
    rw [show F - head.length = 4 + (F - head.length - 4) by omega, List.replicate_add]
    rw [show L0 ++ head ++ (List.replicate 4 (0 : UInt8) ++
        List.replicate (F - head.length - 4) 0) ++ body =
        (L0 ++ head) ++ (List.replicate 4 (0 : UInt8) ++
        (List.replicate (F - head.length - 4) 0 ++ body)) by simp only [List.append_assoc]]
    rw [List.take_left' hpre, ← List.drop_drop, List.drop_left' hpre,
      List.drop_left' (by simp)]
    simp only [List.append_assoc, Nat.add_sub_cancel_left]
  have hb1l : (back s2).length = ce.buf.length := by
    have := congrArg List.length hb1
    simp only [List.length_map] at this
    simp only [alloc.vec.Vec.length, this, List.length_append, List.length_replicate, hUl]
    simp only [alloc.vec.Vec.length] at hlen
    omega
  step with helem x (back s2) (by rw [hb1l]; exact hmax) as ⟨ v1, hv1 ⟩
  refine ⟨⟨?_, hst, ?_, hF, by simp [uintBytes_size]; omega⟩, by simp⟩
  · have := congrArg Array.toList hv1
    simp only [bytes, List.toList_toArray, Array.toList_append] at this
    rw [this, hb1, ← hoffv]
    simp only [List.length_append, List.append_assoc, Nat.sub_add_eq, hU, Array.length_toList,
      uintBytes_size]
  · simp [hi1, hcur, uintBytes_size]; omega

/-- **`finalize`**: if the fixed part is complete, the buffer is what was there before, the
fixed part and the bodies. (`finalize` is a `debug_assert`, which Charon translates as
`massert`.) -/
theorem finalize.spec (ce : encode.ContainerEncoder) (L0 : List UInt8) (F : Nat)
    (head body : List UInt8) (hinv : EncInv ce L0 F head body) (hfull : head.length = F) :
    encode.ContainerEncoder.finalize ce ⦃ ce' => ce'.buf.val.map byte = L0 ++ head ++ body ⦄ := by
  obtain ⟨hb, hst, hcur, hF, hhF⟩ := hinv
  unfold encode.ContainerEncoder.finalize
  step as ⟨ rv, hrv ⟩
  step
  simp only [hb, hfull, Nat.sub_self, List.replicate_zero, List.append_nil]

/-! ## What each field type of the example appends -/

theorem U64.ssz_append.bytes_spec (x : Std.U64) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (uintBytes 8 x.val).size ≤ Usize.max) :
    U64.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ uintBytes 8 x.val ⦄ := by
  rw [uintBytes_size] at h
  apply WP.spec_mono (Libssz.Proofs.U64.ssz_append.spec x buf h)
  rintro buf' ⟨enc, henc, hb⟩
  have hs : serialize Desc.uint64 (.uint x.val) = .ok (uintBytes 8 x.val) := by
    have := x.hBounds
    simp [serialize, Desc.uint64]
    scalar_tac
  rw [hs] at henc
  cases henc
  exact hb

/-- The SSZ bytes of a `Vec<u16>`: the 2 bytes of each element. -/
def u16sBytes (w : alloc.vec.Vec Std.U16) : Bytes :=
  concatParts (w.val.map fun x => uintBytes 2 x.val)

theorem u16sBytes_size (w : alloc.vec.Vec Std.U16) : (u16sBytes w).size = 2 * w.length := by
  have hsz : ∀ p ∈ w.val.map (fun x => uintBytes 2 x.val), p.size = 2 := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨x, _, rfl⟩ := hp
    exact uintBytes_size _ _
  rw [u16sBytes, concatParts_size 2 _ hsz]
  simp [alloc.vec.Vec.length, Nat.mul_comm]

theorem VecU16.ssz_append.bytes_spec (w : alloc.vec.Vec Std.U16) (b : alloc.vec.Vec Std.U8)
    (h : b.length + (u16sBytes w).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U16.Insts.LibsszEncodeSszEncode w b
      ⦃ b' => bytes b'.val = bytes b.val ++ u16sBytes w ⦄ := by
  rw [u16sBytes_size] at h
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U16.Insts.LibsszEncodeSszEncode, U16.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U16.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps]
  step as ⟨ n, hn ⟩
  · simp [alloc.vec.Vec.deref, alloc.vec.Vec.length] at *; scalar_tac
  simp only [alloc.vec.Vec.reserve, bind_ok]
  apply WP.spec_mono (U16.encode_loop.spec (alloc.vec.Vec.deref w) b 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref, alloc.vec.Vec.length] at *; scalar_tac))
  intro b' hb'
  rw [hb', u16sBytes]
  simp [alloc.vec.Vec.deref]

theorem VecU16.serialize (w : alloc.vec.Vec Std.U16) (hw : (u16sBytes w).size < 2 ^ 32) :
    serialize (.list Desc.uint16 core.num.Usize.MAX.val) (.seq (w.val.map fun x => .uint x.val)) =
      .ok (u16sBytes w) := by
  rw [u16sBytes_size] at hw
  have hfit : ∀ n ∈ w.val.map (·.val), n < 2 ^ (8 * 2) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 2 core.num.Usize.MAX.val (w.val.map (·.val)) hfit
    (by simp [alloc.vec.Vec.length] at *) (by simpa [alloc.vec.Vec.length] using hw)
  simp only [List.map_map] at this
  rw [show Desc.uint16 = .uint 2 from rfl]
  convert this using 2 <;> simp [u16sBytes, Function.comp_def]

/-! ## EthLib on the example container -/

@[simp] theorem ex_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem ex_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

def exFields : List Desc :=
  [Desc.uint64, .list Desc.uint8 core.num.Usize.MAX.val, .bool, .list Desc.uint16 core.num.Usize.MAX.val]

theorem exFields_fixedSize : Desc.fieldsFixedSize exFields = none := by
  simp [exFields, Desc.fieldsFixedSize, Desc.fixedSize, Desc.uint64]
theorem exFields_leading : Desc.leadingWidth exFields = 17 := by
  simp [exFields, Desc.leadingWidth, Desc.fixedSize, Desc.uint64, bytesPerOffset]

theorem eth_decode (names : List String) (data : Bytes) (hsz : data.size < 2 ^ 32) :
    deserialize (.container names exFields) data =
      if data.size < 17 then .error (.scopeTooSmall 17 data.size) else
      match deserialize .bool (data.extract 12 13) with
      | .error e => .error e
      | .ok _ =>
        if readUint data 8 4 ≠ 17 then .error (.firstOffset 17 (readUint data 8 4)) else
        if readUint data 13 4 < 17 then .error .offsetUnordered else
        if data.size < readUint data 13 4 then .error .offsetPastScope else
        (do
          let a ← deserialize Desc.uint64 (data.extract 0 8)
          let b ← deserialize (.list Desc.uint8 core.num.Usize.MAX.val) (data.extract 17 (readUint data 13 4))
          let c ← deserialize .bool (data.extract 12 13)
          let d ← deserialize (.list Desc.uint16 core.num.Usize.MAX.val)
            (data.extract (readUint data 13 4) data.size)
          return .seq [a, b, c, d]) := by
  conv_lhs => rw [deserialize]
  conv_lhs => rw [deserializeStruct]
  simp only [structSlots, show ¬ (data.size ≥ 2 ^ (8 * bytesPerOffset)) by simp [bytesPerOffset]; omega,
    ↓reduceIte, structBudget, exFields_fixedSize,
    exFields_leading]
  by_cases h17 : data.size < 17
  · simp [h17]
  have hrs : readSlots exFields data 0 = .ok ([.inline (data.extract 0 8), .body (readUint data 8 4),
      .inline (data.extract 12 13), .body (readUint data 13 4)], 17) := by
    simp only [exFields, readSlots, Desc.fixedSize, Desc.uint64, bytesPerOffset]
    simp [show ¬ (0 + 8 > data.size) by omega, show ¬ (8 + 4 > data.size) by omega,
      show ¬ (12 + 1 > data.size) by omega, show ¬ (13 + 4 > data.size) by omega]
  simp only [h17, ↓reduceIte, hrs, ex_ok_bind, bodyStarts, List.isEmpty_cons, Bool.not_false]
  simp only [exFields]
  rw [checkInline, checkInline, checkInline, checkInline, checkInline]
  have hu : deserialize Desc.uint64 (data.extract 0 8) = .ok (.uint (readUint (data.extract 0 8) 0 8)) := by
    have : (data.extract 0 8).size = 8 := by simp; omega
    rw [deserialize.eq_def]; simp only [Desc.uint64, this, bne_self_eq_false]; rfl
  simp only [hu, ex_ok_bind]
  generalize hb : deserialize .bool (data.extract 12 13) = rb
  cases rb with
  | error e => rfl
  | ok vb =>
    simp only [ex_ok_bind, structBodies]
    simp only [bodyStarts, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.headD_cons, List.head?_cons, Option.getD_some]
    by_cases ho1 : readUint data 8 4 = 17
    · simp only [ho1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
      simp only [offsetSpans, offsetSpansFrom]
      by_cases ho2 : readUint data 13 4 < 17
      · simp [ho2]
      by_cases ho3 : data.size < readUint data 13 4
      · simp [ho2, ho3]
      simp only [ho2, ho3, ↓reduceIte, ex_ok_bind, List.reverse_cons, List.reverse_nil]
      simp only [List.nil_append, List.cons_append, takeSlots, ex_ok_bind, Slot.held, pure,
        Except.pure]
      rw [show 17 + (readUint data 13 4 - 17) = readUint data 13 4 by omega,
        show readUint data 13 4 + (data.size - readUint data 13 4) = data.size by omega]
      rw [deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields]
      simp only [hu, hb, ex_ok_bind]
      generalize deserialize (Desc.uint8.list core.num.Usize.MAX.val) (data.extract 17 (readUint data 13 4)) = r1
      cases r1 <;> simp only [ex_error_bind, ex_ok_bind]
      generalize deserialize (Desc.uint16.list core.num.Usize.MAX.val)
        (data.extract (readUint data 13 4) data.size) = r2
      cases r2 <;> rfl
    · have : (readUint data 8 4 != 17) = true := by simpa using ho1
      simp only [this, ↓reduceIte, ne_eq, ho1, not_false_eq_true]
      rfl

/-- The encoding of the example, built from its four parts. -/
def exLayout (pa pb pc pd : Bytes) : Bytes :=
  pa ++ uintBytes 4 17 ++ pc ++ uintBytes 4 (17 + pb.size) ++ pb ++ pd

theorem eth_encode (names : List String) (va vb vc vd : Value) (pa pb pc pd : Bytes)
    (ha : serialize Desc.uint64 va = .ok pa) (hb : serialize (.list Desc.uint8 core.num.Usize.MAX.val) vb = .ok pb)
    (hc : serialize .bool vc = .ok pc) (hd : serialize (.list Desc.uint16 core.num.Usize.MAX.val) vd = .ok pd)
    (hpa : pa.size = 8) (hpc : pc.size = 1) :
    serialize (.container names exFields) (.seq [va, vb, vc, vd]) =
      if (exLayout pa pb pc pd).size ≥ 2 ^ 32 then .error (.offsetOverflow (exLayout pa pb pc pd).size)
      else .ok (exLayout pa pb pc pd) := by
  rw [serialize]
  simp only [serializeStruct, exFields]
  rw [serializeFields]
  simp only [ha, ex_ok_bind]
  rw [serializeFieldsFrom, hb, ex_ok_bind, serializeFieldsFrom, hc, ex_ok_bind, serializeFieldsFrom, hd,
    ex_ok_bind, serializeFieldsFrom]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, ex_ok_bind]
  have hf : [Desc.uint64, Desc.list Desc.uint8 core.num.Usize.MAX.val, Desc.bool,
      Desc.list Desc.uint16 core.num.Usize.MAX.val].map Desc.isFixed = [true, false, true, false] := by decide
  rw [hf, assemble]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, headWidth, headWidthFrom, bodyWidth,
    bodyWidthFrom, headOf, headOfFrom, bodiesOf, bodiesOfFrom, hpa, hpc, ↓reduceIte, bytesPerOffset,
    Bool.false_eq_true]
  have hsz : (exLayout pa pb pc pd).size = 17 + (pb.size + pd.size) := by
    simp [exLayout, uintBytes_size, hpa, hpc]; omega
  rw [hsz, show 0 + 8 + 4 + 1 + 4 + (0 + pb.size + pd.size) = 17 + (pb.size + pd.size) by omega,
    show 0 + 8 + 4 + 1 + 4 = 17 from rfl, show 2 ^ (8 * 4) = 2 ^ 32 from rfl]
  split
  · rfl
  · simp only [exLayout, Array.empty_append, Array.append_assoc]; rfl

/-! ## The example container: encode -/

def exToV (x : verif_example.Example) : Value :=
  .seq [.uint x.a.val, .seq (x.b.val.map fun y => .uint y.val), .bool x.c,
    .seq (x.d.val.map fun y => .uint y.val)]

/-- What libssz writes for the example: the fixed part (`a`, the offset of `b`, `c`, the
offset of `d`) and then the bodies of `b` and `d`. -/
def exEnc (x : verif_example.Example) : Bytes :=
  exLayout (uintBytes 8 x.a.val) (u8sBytes x.b) (boolByte x.c) (u16sBytes x.d)

theorem exEnc_size (x : verif_example.Example) :
    (exEnc x).size = 17 + x.b.length + 2 * x.d.length := by
  simp [exEnc, exLayout, uintBytes_size, u8sBytes_size, u16sBytes_size, boolByte]
  omega

theorem Example.encoded_len.spec (x : verif_example.Example)
    (h : 17 + x.b.length + 2 * x.d.length ≤ Usize.max) :
    verif_example.Example.Insts.LibsszEncodeSszEncode.encoded_len x ⦃ n =>
      n.val = 17 + x.b.length + 2 * x.d.length ⦄ := by
  unfold verif_example.Example.Insts.LibsszEncodeSszEncode.encoded_len
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.encoded_len
  simp only [U64.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.fixed_size,
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.is_fixed_size, U8.Insts.LibsszEncodeSszEncode,
    U8.Insts.LibsszEncodeSszEncode.is_fixed_size, U8.Insts.LibsszEncodeSszEncode.fixed_size,
    Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size,
    U16.Insts.LibsszEncodeSszEncode, U16.Insts.LibsszEncodeSszEncode.is_fixed_size,
    U16.Insts.LibsszEncodeSszEncode.fixed_size, bind_ok, ↓reduceIte, Bool.false_eq_true]
  have hb : x.b.len.val = x.b.length := by simp
  have hd : x.d.len.val = x.d.length := by simp
  step*
  all_goals scalar_tac

/-- **`Example::ssz_append`** appends `exEnc x`, for any size. If the body of `b` reaches
2³² − 17 bytes, the offset of `d` is truncated (`uintBytes 4` truncates too). The hypothesis
on `usize` leaves room for the 8 bytes of `a`, which `append_fixed` appends at the end of the
buffer before moving them into the fixed part. -/
theorem Example.ssz_append.bytes_spec (x : verif_example.Example) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (exEnc x).size + 8 ≤ Usize.max) :
    verif_example.Example.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ exEnc x ⦄ := by
  rw [exEnc_size] at h
  unfold verif_example.Example.Insts.LibsszEncodeSszEncode.ssz_append
    verif_example.Example.Insts.LibsszEncodeSszEncode.is_fixed_size
  simp only [U64.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.fixed_size,
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.is_fixed_size,
    Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size,
    bind_ok, ↓reduceIte, Bool.false_eq_true]
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i3, hi3 ⟩
  step as ⟨ i5, hi5 ⟩
  step as ⟨ fpl, hfpl ⟩
  have hF : fpl.val = 17 := by scalar_tac
  step with Example.encoded_len.spec x (by scalar_tac) as ⟨ tot, htot ⟩
  step with with_capacity.spec buf fpl tot (by scalar_tac) as ⟨ e0, back0, hinv0, hback0 ⟩
  rw [hF] at hinv0
  have hL0 : (buf.val.map byte).length = buf.length := by simp [alloc.vec.Vec.length]
  have hbv : buf.val.length = buf.length := rfl
  step with append_fixed.spec U64.Insts.LibsszEncodeSszEncode (fun a => uintBytes 8 a.val)
    (fun a b hb => U64.ssz_append.bytes_spec a b hb) e0 x.a _ 17 [] [] hinv0
    (by simp [uintBytes_size]) (by rw [hinv0.length]; simp [uintBytes_size]; scalar_tac)
    as ⟨ p1, hinv1, hbk1 ⟩
  rcases p1 with ⟨ e1, bk1 ⟩
  simp only [step_simps]
  step with append_variable.spec
    (alloc.vec.Vec.Insts.LibsszEncodeSszEncode U8.Insts.LibsszEncodeSszEncode) u8sBytes (fun w b hb => VecU8.ssz_append.bytes_spec w b hb)
    { buf := e1.buf, start := e1.start, fixed_cursor := e1.fixed_cursor,
      fixed_part_len := e1.fixed_part_len } x.b _ 17 _ [] hinv1
    (by simp [uintBytes_size])
    (by rw [hinv1.length]; simp [u8sBytes_size]; scalar_tac)
    as ⟨ p2, hinv2, hbk2 ⟩
  rcases p2 with ⟨ e2, bk2 ⟩
  simp only [step_simps]
  step with append_fixed.spec Bool.Insts.LibsszEncodeSszEncode boolByte
    (fun a b hb => Bool.ssz_append.bytes_spec a b (by simp [boolByte] at hb; omega))
    { buf := e2.buf, start := e2.start, fixed_cursor := e2.fixed_cursor,
      fixed_part_len := e2.fixed_part_len } x.c _ 17 _ _ hinv2
    (by simp [uintBytes_size, boolByte])
    (by rw [hinv2.length]; simp [u8sBytes_size, boolByte]; scalar_tac)
    as ⟨ p3, hinv3, hbk3 ⟩
  rcases p3 with ⟨ e3, bk3 ⟩
  simp only [step_simps]
  step with append_variable.spec
    (alloc.vec.Vec.Insts.LibsszEncodeSszEncode U16.Insts.LibsszEncodeSszEncode) u16sBytes (fun w b hb => VecU16.ssz_append.bytes_spec w b hb)
    { buf := e3.buf, start := e3.start, fixed_cursor := e3.fixed_cursor,
      fixed_part_len := e3.fixed_part_len } x.d _ 17 _ _ hinv3
    (by simp [uintBytes_size, boolByte])
    (by rw [hinv3.length]; simp [u8sBytes_size, u16sBytes_size, boolByte]; scalar_tac)
    as ⟨ p4, hinv4, hbk4 ⟩
  rcases p4 with ⟨ e4, bk4 ⟩
  simp only [step_simps]
  step with (finalize.spec _ _ 17 _ _ hinv4 (by simp [uintBytes_size, boolByte])) as ⟨ ce, hce ⟩
  dsimp only at hbk1 hbk2 hbk3 hbk4
  simp only [hback0, hbk1, hbk2, hbk3, hbk4]
  apply Array.toList_inj.mp
  simp only [bytes, Array.toList_append, hce, exEnc, exLayout, List.toList_toArray]
  simp [uintBytes_size, u8sBytes_size, alloc.vec.Vec.length]

/-- What EthLib gives for the example, if each list is shorter than 2³²: the same encoding,
or `offsetOverflow` if the total does not fit in 32 bits. -/
theorem Example.ethlib_encode (names : List String) (x : verif_example.Example)
    (hb : x.b.length < 2 ^ 32) (hd : 2 * x.d.length < 2 ^ 32) :
    serialize (.container names exFields) (exToV x) =
      if (exEnc x).size ≥ 2 ^ 32 then .error (.offsetOverflow (exEnc x).size)
      else .ok (exEnc x) := by
  have ha : serialize Desc.uint64 (.uint x.a.val) = .ok (uintBytes 8 x.a.val) := by
    have := x.a.hBounds
    simp [serialize, Desc.uint64]
    scalar_tac
  have hc : serialize .bool (.bool x.c) = .ok (boolByte x.c) := by
    cases x.c <;> simp [serialize, boolByte]
  exact eth_encode names _ _ _ _ _ _ _ _ ha (VecU8.serialize x.b (by rw [u8sBytes_size]; exact hb))
    hc (VecU16.serialize x.d (by rw [u16sBytes_size]; exact hd)) (uintBytes_size _ _) rfl

/-- **Container encode ≡ EthLib** (total < 2³²): `Example::ssz_append` appends exactly the
EthLib encoding. -/
theorem Example.encode.agrees (names : List String) (x : verif_example.Example)
    (buf : alloc.vec.Vec Std.U8) (hsz : (exEnc x).size < 2 ^ 32)
    (hmax : buf.length + (exEnc x).size + 8 ≤ Usize.max) :
    verif_example.Example.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.container names exFields) (exToV x) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (Example.ssz_append.bytes_spec x buf hmax)
  intro buf' h
  refine ⟨_, ?_, h⟩
  have := exEnc_size x
  rw [Example.ethlib_encode names x (by omega) (by omega)]
  simp only [show ¬ ((exEnc x).size ≥ 2 ^ 32) by omega, ↓reduceIte]

/-- **The offset-overflow divergence in `ContainerEncoder`** (`var_offset as u32` in
`append_variable`, `encode.rs`): with `b` and `d` shorter than 4 GiB each but a total of
4 GiB or more, EthLib rejects (`offsetOverflow`) and libssz writes `exEnc x` without an error.
If the body of `b` reaches 2³² − 17 bytes, the offset of `d` in that encoding is truncated. -/
theorem Example.encode.diverges (names : List String) (x : verif_example.Example)
    (buf : alloc.vec.Vec Std.U8) (hb : x.b.length < 2 ^ 32) (hd : 2 * x.d.length < 2 ^ 32)
    (hbig : (exEnc x).size ≥ 2 ^ 32)
    (hmax : buf.length + (exEnc x).size + 8 ≤ Usize.max) :
    verif_example.Example.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ exEnc x ∧
      serialize (.container names exFields) (exToV x) =
        .error (.offsetOverflow (exEnc x).size) ⦄ := by
  apply WP.spec_mono (Example.ssz_append.bytes_spec x buf hmax)
  intro buf' h
  refine ⟨h, ?_⟩
  rw [Example.ethlib_encode names x hb hd]
  simp only [hbig, ↓reduceIte]

/-! ## `ContainerDecoder` -/

/-- The state of a `ContainerDecoder`: the input `s`, the length `F` of the fixed part, the
cursor position in the fixed part, the offsets read so far and how many bodies have been
decoded. -/
def DecInv (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat) (offs : List Nat)
    (vi : Nat) : Prop :=
  dc.bytes = s ∧ dc.fixed_part_len.val = F ∧ dc.cursor.val = cur ∧
  dc.offsets.val.map (·.val) = offs ∧ dc.variable_index.val = vi

theorem bytes_slice (l : List Std.U8) (a b : Nat) :
    bytes (l.slice a b) = (bytes l).extract a b := by
  rw [bytes_extract]; rfl

theorem new.spec (s : Slice Std.U8) (F : Std.Usize) :
    decode.ContainerDecoder.new s F ⦃ r =>
      match r with
      | .Ok dc => F.val ≤ s.length ∧ DecInv dc s F.val 0 [] 0
      | .Err e => s.length < F.val ∧ e = .InvalidByteLength F s.len ⦄ := by
  unfold decode.ContainerDecoder.new
  have hl := Slice.len_val s
  simp only [step_simps]
  split
  · simp only [WP.spec_ok]; constructor <;> scalar_tac
  · simp only [WP.spec_ok]
    refine ⟨by scalar_tac, rfl, rfl, by simp, by simp [alloc.vec.Vec.new], by simp⟩

theorem decode_fixed.spec {T : Type} (inst : decode.SszDecode T) (dsc : Desc) (toV : T → Value)
    (w : Std.Usize) (hw : inst.fixed_size = ok w)
    (hdec : ∀ s' : Slice Std.U8, inst.from_ssz_bytes s' ⦃ r =>
      Agrees toV r (deserialize dsc (bytes s'.val)) ⦄)
    (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat) (offs : List Nat) (vi : Nat)
    (hinv : DecInv dc s F cur offs vi) (hfit : cur + w.val ≤ s.length) :
    decode.ContainerDecoder.decode_fixed inst dc ⦃ r dc' =>
      Agrees toV r (deserialize dsc ((bytes s.val).extract cur (cur + w.val))) ∧
      (∀ v, r = .Ok v → DecInv dc' s F (cur + w.val) offs vi) ⦄ := by
  obtain ⟨hb, hF, hc, ho, hv⟩ := hinv
  subst hb
  unfold decode.ContainerDecoder.decode_fixed
  simp only [hw, bind_ok]
  have hl := Slice.len_val dc.bytes
  step as ⟨ e, he ⟩
  simp only [show ¬ (e > dc.bytes.len) by scalar_tac, ↓reduceIte]
  step as ⟨ s1, hs1 ⟩
  step with hdec s1 as ⟨ r, hr ⟩
  have hext : bytes s1.val = (bytes dc.bytes.val).extract cur (cur + w.val) := by
    rw [hs1, bytes_slice, he, hc]
  rw [hext] at hr
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, bind_ok, WP.spec_ok]
    exact ⟨hr, fun v h => by cases h⟩
  | Ok v =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    refine ⟨hr, fun v' _ => ⟨rfl, hF, by rw [he, hc], ho, hv⟩⟩

/-- **The first offset** must be the length of the fixed part. -/
theorem read_first_offset.spec (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur vi : Nat)
    (hinv : DecInv dc s F cur [] vi) (hF : F ≤ s.length) (hfit : cur + 4 ≤ s.length) :
    decode.ContainerDecoder.read_variable_offset dc ⦃ r dc' =>
      match r with
      | .Ok _ => readUint (bytes s.val) cur 4 = F ∧ DecInv dc' s F (cur + 4) [F] vi
      | .Err e => readUint (bytes s.val) cur 4 ≠ F ∧
          ∃ g : Std.Usize, g.val = readUint (bytes s.val) cur 4 ∧
            e = .InvalidFirstOffset dc.fixed_part_len g ⦄ := by
  obtain ⟨hb, hFv, hc, ho, hv⟩ := hinv
  subst hb
  unfold decode.ContainerDecoder.read_variable_offset
  step with read_offset.spec dc.bytes dc.cursor (by rw [hc]; exact hfit) as ⟨ r, hr ⟩
  rcases r with o | e
  · simp only [hc] at hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hemp : dc.offsets.val = [] := by simpa using ho
    step as ⟨ b, hb ⟩
    have hbt : b = true := by simpa [alloc.vec.Vec.is_empty, hemp] using hb
    simp only [hbt, ↓reduceIte]
    by_cases hne : o = dc.fixed_part_len
    · have hne' : ¬ (o != dc.fixed_part_len) = true := by simp [hne]
      simp only [hne', Bool.false_eq_true, ↓reduceIte]
      have hl := Slice.len_val dc.bytes
      simp only [show ¬ (o > dc.bytes.len) by scalar_tac, ↓reduceIte]
      step as ⟨ v, hv' ⟩
      simp only [BYTES_PER_LENGTH_OFFSET]
      step as ⟨ i1, hi1 ⟩
      refine ⟨by rw [← hr, hne, hFv], rfl, hFv, by rw [hi1, hc], ?_, hv⟩
      simp [hv', hemp, hne, hFv]
    · have hne' : (o != dc.fixed_part_len) = true := by simpa using hne
      simp only [hne', ↓reduceIte, WP.spec_ok]
      refine ⟨by rw [← hr, ← hFv]; exact fun h => hne (UScalar.eq_of_val_eq h), o, hr, rfl⟩
  · simp only at hr

/-- **The following offsets**: they can neither decrease nor go past the length. -/
theorem read_next_offset.spec (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat)
    (offs : List Nat) (vi : Nat) (hinv : DecInv dc s F cur offs vi) (hne : offs ≠ [])
    (hfit : cur + 4 ≤ s.length) (hcap : offs.length < Usize.max) :
    decode.ContainerDecoder.read_variable_offset dc ⦃ r dc' =>
      match r with
      | .Ok _ => offs.getLast hne ≤ readUint (bytes s.val) cur 4 ∧
          readUint (bytes s.val) cur 4 ≤ s.length ∧
          DecInv dc' s F (cur + 4) (offs ++ [readUint (bytes s.val) cur 4]) vi
      | .Err e => (readUint (bytes s.val) cur 4 < offs.getLast hne ∧
            e = .OffsetsAreNotMonotonicallyIncreasing) ∨
          (offs.getLast hne ≤ readUint (bytes s.val) cur 4 ∧
            s.length < readUint (bytes s.val) cur 4 ∧ ∃ a b, e = .OffsetOutOfBounds a b) ⦄ := by
  obtain ⟨hb, hFv, hc, ho, hv⟩ := hinv
  subst hb
  unfold decode.ContainerDecoder.read_variable_offset
  step with read_offset.spec dc.bytes dc.cursor (by rw [hc]; exact hfit) as ⟨ r, hr ⟩
  rcases r with o | e
  · simp only [hc] at hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hnemp : dc.offsets.val ≠ [] := by
      intro h; apply hne; rw [← ho, h]; rfl
    step as ⟨ b, hb ⟩
    have hbf : b = false := by simpa [alloc.vec.Vec.is_empty, hnemp] using hb
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    have hlen : dc.offsets.length = offs.length := by
      rw [← ho]; simp [alloc.vec.Vec.length]
    have hpos : 0 < offs.length := List.length_pos_iff.mpr hne
    step as ⟨ i1, hi1 ⟩
    step as ⟨ i2, hi2 ⟩
    have hlast : i2.val = offs.getLast hne := by
      rw [hi2, List.getLast_eq_getElem]
      simp only [← ho, List.getElem_map]
      congr 1
      simp [hi1, alloc.vec.Vec.length] at *
    have hl := Slice.len_val dc.bytes
    by_cases hmono : o < i2
    · simp only [hmono, ↓reduceIte, WP.spec_ok]
      left
      refine ⟨?_, rfl⟩
      rw [← hr, ← hlast]; scalar_tac
    · simp only [hmono, ↓reduceIte]
      by_cases hoob : o > dc.bytes.len
      · simp only [hoob, ↓reduceIte, WP.spec_ok]
        right
        exact ⟨by rw [← hr, ← hlast]; scalar_tac, by rw [← hr]; scalar_tac, _, _, rfl⟩
      · simp only [hoob, ↓reduceIte]
        step as ⟨ v, hv' ⟩
        simp only [BYTES_PER_LENGTH_OFFSET]
        step as ⟨ i4, hi4 ⟩
        refine ⟨by rw [← hr, ← hlast]; scalar_tac, by rw [← hr]; scalar_tac, rfl, hFv,
          by rw [hi4, hc], ?_, hv⟩
        simp [hv', ho, hr]
  · simp only at hr

/-- **`decode_variable`**: decodes body number `vi`, between its offset and the next one
(or the end). -/
theorem decode_variable.spec {T : Type} (inst : decode.SszDecode T) (dsc : Desc) (toV : T → Value)
    (hdec : ∀ s' : Slice Std.U8, s'.length < 2 ^ 32 → inst.from_ssz_bytes s' ⦃ r =>
      Agrees toV r (deserialize dsc (bytes s'.val)) ⦄)
    (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat) (offs : List Nat) (vi : Nat)
    (hinv : DecInv dc s F cur offs vi) (hs : s.length < 2 ^ 32) (hvi : vi < offs.length)
    (stop : Nat) (hstop : stop = if h : vi + 1 < offs.length then offs[vi + 1] else s.length)
    (hle : offs[vi] ≤ stop) (hstopl : stop ≤ s.length) :
    decode.ContainerDecoder.decode_variable inst dc ⦃ r dc' =>
      Agrees toV r (deserialize dsc ((bytes s.val).extract offs[vi] stop)) ∧
      DecInv dc' s F cur offs (vi + 1) ⦄ := by
  obtain ⟨hb, hFv, hc, ho, hv⟩ := hinv
  subst hb
  unfold decode.ContainerDecoder.decode_variable
  have hlen : dc.offsets.length = offs.length := by
    rw [← ho]; simp [alloc.vec.Vec.length]
  simp only [step_simps]
  simp only [show ¬ (dc.variable_index ≥ dc.offsets.len) by scalar_tac, ↓reduceIte]
  step as ⟨ st, hst ⟩
  have hstv : st.val = offs[vi] := by
    rw [hst]; simp only [← ho, List.getElem_map]; simp [hv]
  step as ⟨ i1, hi1 ⟩
  have hl := Slice.len_val dc.bytes
  have hend : (if i1 < dc.offsets.len then dc.offsets.index_usize i1
      else ok dc.bytes.len) ⦃ en => en.val = stop ⦄ := by
    split
    · rename_i hlt
      have hlt' : vi + 1 < offs.length := by scalar_tac
      step as ⟨ en, hen ⟩
      rw [hen, hstop, dif_pos hlt']
      simp only [← ho, List.getElem_map]; simp [hi1, hv]
    · rename_i hge
      have hge' : ¬ (vi + 1 < offs.length) := by scalar_tac
      simp only [WP.spec_ok, hstop, hge', hl]
      simp
  step with hend as ⟨ en, hen ⟩
  step as ⟨ s1, hs1 ⟩
  step with hdec s1 (by simp [Slice.length] at *; scalar_tac) as ⟨ r, hr ⟩
  refine ⟨?_, rfl, hFv, hc, ho, by rw [hi1, hv]⟩
  rw [hs1, bytes_slice, hstv, hen] at hr
  exact hr

/-! ## The per-field steps of `ssz-derive` (`decode_fixed_part`, `decode_variable_part`) -/

/-- A **fixed-size** field in the fixed-part pass: it is `decode_fixed`, with `some`. -/
theorem decode_fixed_part.fixed_spec {T : Type} (inst : decode.SszDecode T) (dsc : Desc)
    (toV : T → Value) (w : Std.Usize) (hfix : inst.is_fixed_size = ok true)
    (hw : inst.fixed_size = ok w)
    (hdec : ∀ s' : Slice Std.U8, inst.from_ssz_bytes s' ⦃ r =>
      Agrees toV r (deserialize dsc (bytes s'.val)) ⦄)
    (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat) (offs : List Nat) (vi : Nat)
    (hinv : DecInv dc s F cur offs vi) (hfit : cur + w.val ≤ s.length) :
    decode.ContainerDecoder.decode_fixed_part inst dc ⦃ r dc' =>
      (∀ e, r = .Err e → Agrees toV (.Err e) (deserialize dsc ((bytes s.val).extract cur (cur + w.val)))) ∧
      (∀ o, r = .Ok o → ∃ v, o = some v ∧
        Agrees toV (.Ok v) (deserialize dsc ((bytes s.val).extract cur (cur + w.val))) ∧
        DecInv dc' s F (cur + w.val) offs vi) ⦄ := by
  unfold decode.ContainerDecoder.decode_fixed_part
  simp only [hfix, bind_ok, ↓reduceIte]
  step with decode_fixed.spec inst dsc toV w hw hdec dc s F cur offs vi hinv hfit
    as ⟨ r, dc1, hr, hdc1 ⟩
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok, WP.uncurry']
    refine ⟨fun e h => by simp at h, fun o h => ?_⟩
    simp only [core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨v, rfl, hr, hdc1 v rfl⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry']
    refine ⟨fun e' h => ?_, fun o h => by simp at h⟩
    simp only [core.result.Result.Err.injEq] at h
    subst h
    exact hr

/-- A **variable-size** field in the fixed-part pass, if it is the first: the first offset. -/
theorem decode_fixed_part.first_spec {T : Type} (inst : decode.SszDecode T)
    (hvar : inst.is_fixed_size = ok false)
    (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur vi : Nat)
    (hinv : DecInv dc s F cur [] vi) (hF : F ≤ s.length) (hfit : cur + 4 ≤ s.length) :
    decode.ContainerDecoder.decode_fixed_part inst dc ⦃ r dc' =>
      match r with
      | .Ok o => o = none ∧ readUint (bytes s.val) cur 4 = F ∧ DecInv dc' s F (cur + 4) [F] vi
      | .Err e => readUint (bytes s.val) cur 4 ≠ F ∧
          ∃ g : Std.Usize, g.val = readUint (bytes s.val) cur 4 ∧
            e = .InvalidFirstOffset dc.fixed_part_len g ⦄ := by
  unfold decode.ContainerDecoder.decode_fixed_part
  simp only [hvar, bind_ok, Bool.false_eq_true, ↓reduceIte]
  step with read_first_offset.spec dc s F cur vi hinv hF hfit as ⟨ r, dc1, hr ⟩
  rcases r with u | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    exact ⟨rfl, hr⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact hr

/-- A **variable-size** field in the fixed-part pass, if it is not the first. -/
theorem decode_fixed_part.next_spec {T : Type} (inst : decode.SszDecode T)
    (hvar : inst.is_fixed_size = ok false)
    (dc : decode.ContainerDecoder) (s : Slice Std.U8) (F cur : Nat)
    (offs : List Nat) (vi : Nat) (hinv : DecInv dc s F cur offs vi) (hne : offs ≠ [])
    (hfit : cur + 4 ≤ s.length) (hcap : offs.length < Usize.max) :
    decode.ContainerDecoder.decode_fixed_part inst dc ⦃ r dc' =>
      match r with
      | .Ok o => o = none ∧ offs.getLast hne ≤ readUint (bytes s.val) cur 4 ∧
          readUint (bytes s.val) cur 4 ≤ s.length ∧
          DecInv dc' s F (cur + 4) (offs ++ [readUint (bytes s.val) cur 4]) vi
      | .Err e => (readUint (bytes s.val) cur 4 < offs.getLast hne ∧
            e = .OffsetsAreNotMonotonicallyIncreasing) ∨
          (offs.getLast hne ≤ readUint (bytes s.val) cur 4 ∧
            s.length < readUint (bytes s.val) cur 4 ∧ ∃ a b, e = .OffsetOutOfBounds a b) ⦄ := by
  unfold decode.ContainerDecoder.decode_fixed_part
  simp only [hvar, bind_ok, Bool.false_eq_true, ↓reduceIte]
  step with read_next_offset.spec dc s F cur offs vi hinv hne hfit hcap as ⟨ r, dc1, hr ⟩
  rcases r with u | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    exact ⟨rfl, hr⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact hr

/-- A **fixed-size** field in the variable-part pass: the value already decoded. -/
theorem decode_variable_part.fixed_spec {T : Type} (inst : decode.SszDecode T)
    (hfix : inst.is_fixed_size = ok true) (dc : decode.ContainerDecoder) (v : T) :
    decode.ContainerDecoder.decode_variable_part inst dc (some v) ⦃ r dc' =>
      r = .Ok v ∧ dc' = dc ⦄ := by
  unfold decode.ContainerDecoder.decode_variable_part
  simp only [hfix, bind_ok, ↓reduceIte, core.option.Option.unwrap, ofOption, WP.spec_ok]
  exact ⟨rfl, rfl⟩

/-- A **variable-size** field in the variable-part pass: it is `decode_variable`. -/
theorem decode_variable_part.var_spec {T : Type} (inst : decode.SszDecode T) (dsc : Desc)
    (toV : T → Value) (hvar : inst.is_fixed_size = ok false)
    (hdec : ∀ s' : Slice Std.U8, s'.length < 2 ^ 32 → inst.from_ssz_bytes s' ⦃ r =>
      Agrees toV r (deserialize dsc (bytes s'.val)) ⦄)
    (dc : decode.ContainerDecoder) (fixed : Option T) (s : Slice Std.U8) (F cur : Nat)
    (offs : List Nat) (vi : Nat)
    (hinv : DecInv dc s F cur offs vi) (hs : s.length < 2 ^ 32) (hvi : vi < offs.length)
    (stop : Nat) (hstop : stop = if h : vi + 1 < offs.length then offs[vi + 1] else s.length)
    (hle : offs[vi] ≤ stop) (hstopl : stop ≤ s.length) :
    decode.ContainerDecoder.decode_variable_part inst dc fixed ⦃ r dc' =>
      Agrees toV r (deserialize dsc ((bytes s.val).extract offs[vi] stop)) ∧
      DecInv dc' s F cur offs (vi + 1) ⦄ := by
  unfold decode.ContainerDecoder.decode_variable_part
  simp only [hvar, bind_ok, Bool.false_eq_true, ↓reduceIte]
  exact decode_variable.spec inst dsc toV hdec dc s F cur offs vi hinv hs hvi stop hstop hle hstopl

/-! ## The example container: decode -/

/-- `Agrees` with a different relation between the errors. -/
def AgreesBy {α : Type} (R : libssz.error.DecodeError → Err → Prop) (toV : α → Value) :
    core.result.Result α libssz.error.DecodeError → Except Err Value → Prop
  | .Ok a, .ok v => toV a = v
  | .Err e, .error e' => R e e'
  | _, _ => False

/-- The errors of a container decode: those of `ErrMatch`, plus **one ordering case**.
EthLib decodes all fixed-size fields before looking at the first offset (`checkInline`);
libssz goes field by field. If a fixed-size field that comes *after* the first variable-size
field is invalid (in the example, `c` with a byte that is neither 0 nor 1) and the first
offset is also wrong, libssz rejects because of the offset and EthLib because of the
field. -/
inductive ErrMatchC : libssz.error.DecodeError → Err → Prop
  | base {e : libssz.error.DecodeError} {e' : Err} : ErrMatch e e' → ErrMatchC e e'
  | inlineFirst (e g : Std.Usize) (b : Nat) : ErrMatchC (.InvalidFirstOffset e g) (.notABit b)

theorem Agrees.ok_eq {α : Type} {toV : α → Value} {a : α} {r : Except Err Value}
    (h : Agrees toV (.Ok a) r) : r = .ok (toV a) := by
  cases r <;> simp_all [Agrees]

theorem Agrees.err_eq {α : Type} {toV : α → Value} {e : libssz.error.DecodeError}
    {r : Except Err Value} (h : Agrees toV (.Err e) r) : ∃ e', r = .error e' ∧ ErrMatch e e' := by
  cases r with
  | error e' => exact ⟨e', rfl, h⟩
  | ok v => simp [Agrees] at h

/-- A one-byte `bool` that does not decode is `notABit`. -/
theorem deserialize_bool_err (data : Bytes) (hd : data.size = 1) (e : Err)
    (h : deserialize .bool data = .error e) : ∃ b, e = .notABit b := by
  rw [deserialize.eq_def] at h
  simp only [hd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · cases h
  · exact ⟨_, (Except.error.inj h).symm⟩

/-- **Container decode ≡ EthLib.** For every input shorter than 2³² bytes,
`Example::from_ssz_bytes` and EthLib's `deserialize` accept the same inputs, with the same
value, and reject the same ones, with corresponding errors (`ErrMatchC`). -/
theorem Example.from_ssz_bytes.spec (names : List String) (s : Slice Std.U8)
    (hs : s.length < 2 ^ 32) :
    verif_example.Example.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      AgreesBy ErrMatchC exToV r (deserialize (.container names exFields) (bytes s.val)) ⦄ := by
  rw [eth_decode names (bytes s.val) (by rw [bytes_size]; exact hs)]
  simp only [bytes_size]
  unfold verif_example.Example.Insts.LibsszDecodeSszDecode.from_ssz_bytes
    verif_example.Example.Insts.LibsszDecodeSszDecode.is_fixed_size
  simp only [U64.Insts.LibsszDecodeSszDecode.is_fixed_size, U64.Insts.LibsszDecodeSszDecode.fixed_size,
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.is_fixed_size,
    Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size,
    bind_ok, ↓reduceIte, Bool.false_eq_true]
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i3, hi3 ⟩
  step as ⟨ i5, hi5 ⟩
  step as ⟨ fpl, hfpl ⟩
  have hF : fpl.val = 17 := by scalar_tac
  step with new.spec s fpl as ⟨ r0, hr0 ⟩
  have hsl : s.val.length = s.length := rfl
  have hl := Slice.len_val s
  rw [hsl]
  rcases r0 with cd | e0
  · -- the input is long enough for the fixed part
    obtain ⟨hF17, hinv0⟩ := hr0
    rw [hF] at hF17 hinv0
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      show ¬ (s.length < 17) by omega, ↓reduceIte]
    -- `a`: always decodes
    step with decode_fixed_part.fixed_spec U64.Insts.LibsszDecodeSszDecode Desc.uint64
      (fun x => .uint x.val) 8#usize rfl rfl (fun s' => U64.from_ssz_bytes.spec s') cd s 17 0 [] 0
      hinv0 (by simp; omega) as ⟨ r1, d1, hr1e, hr1o ⟩
    rw [show (0:Nat) + 8 = 8 from rfl] at hr1e hr1o
    have hu : deserialize Desc.uint64 ((bytes s.val).extract 0 8) =
        .ok (.uint (readUint ((bytes s.val).extract 0 8) 0 8)) := by
      have : ((bytes s.val).extract 0 8).size = 8 := by simp [bytes_size]; omega
      rw [deserialize.eq_def]; simp only [Desc.uint64, this, bne_self_eq_false]; rfl
    rcases r1 with o1 | e1
    swap
    · have := hr1e e1 rfl; rw [hu] at this; simp [Agrees] at this
    obtain ⟨a, rfl, ha', hinv1⟩ := hr1o _ rfl
    have ha : (Value.uint a.val) = .uint (readUint ((bytes s.val).extract 0 8) 0 8) := by
      rw [hu] at ha'; exact ha'
    have hfp1 : d1.fixed_part_len.val = 17 := hinv1.2.1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    -- `b`: the first offset
    step with decode_fixed_part.first_spec
      (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U8.Insts.LibsszDecodeSszDecode) rfl
      d1 s 17 8 0 hinv1 (by omega) (by omega) as ⟨ r2, d2, hr2 ⟩
    rcases r2 with o2 | e2
    · obtain ⟨rfl, ho1, hinv2⟩ := hr2
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [show (8:Nat) + 4 = 12 from rfl] at hinv2
      -- `c`
      step with decode_fixed_part.fixed_spec Bool.Insts.LibsszDecodeSszDecode .bool Value.bool
        1#usize rfl rfl (fun s' => Bool.from_ssz_bytes.spec s') d2 s 17 12 [17] 0 hinv2
        (by simp; omega) as ⟨ r3, d3, hr3e, hr3o ⟩
      rw [show (12:Nat) + 1 = 13 from rfl] at hr3e hr3o
      simp only [ho1, ne_eq, not_true_eq_false, ↓reduceIte]
      rcases r3 with o3 | e3
      swap
      · obtain ⟨e', he', hm⟩ := Agrees.err_eq (hr3e e3 rfl)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, he', AgreesBy]
        exact ErrMatchC.base hm
      obtain ⟨c, rfl, hc', hinv3⟩ := hr3o _ rfl
      have hc := Agrees.ok_eq hc'
      rw [hc]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      -- `d`: the second offset
      step with decode_fixed_part.next_spec
        (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U16.Insts.LibsszDecodeSszDecode) rfl
        d3 s 17 13 [17] 0 hinv3 (by simp) (by omega) (by simp; scalar_tac) as ⟨ r4, d4, hr4 ⟩
      rcases r4 with o4 | e4
      · obtain ⟨rfl, hmono, hle, hinv4⟩ := hr4
        simp only [List.getLast_singleton] at hmono
        simp only [show ¬ (readUint (bytes s.val) 13 4 < 17) by omega,
          show ¬ (s.length < readUint (bytes s.val) 13 4) by omega, ↓reduceIte,
          core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        simp only [show (13:Nat) + 4 = 17 from rfl, List.singleton_append] at hinv4
        simp only [hu, ex_ok_bind]
        have hUM : core.num.Usize.MAX.val = Usize.max := by simp
        rw [hUM]
        -- variable-part pass: `a` is already done
        step with decode_variable_part.fixed_spec U64.Insts.LibsszDecodeSszDecode rfl d4 a
          as ⟨ r5, d5, hr5, hd5 ⟩
        subst hr5 hd5
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        -- `b`: the body between the two offsets
        step with decode_variable_part.var_spec
          (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U8.Insts.LibsszDecodeSszDecode)
          (.list Desc.uint8 Usize.max)
          (fun v : alloc.vec.Vec Std.U8 => .seq (v.val.map fun x => .uint x.val)) rfl
          (fun s' hs' => by rw [← hUM]; exact U8.vec_from_ssz_bytes.spec s' hs') d5 none s 17 17
          [17, readUint (bytes s.val) 13 4] 0 hinv4 hs
          (by simp) (readUint (bytes s.val) 13 4) (by simp) (by simp; omega) (by omega)
          as ⟨ r6, d6, hr6, hinv6 ⟩
        simp only [List.getElem_cons_zero] at hr6
        rcases r6 with vb | e6
        swap
        · obtain ⟨e', he', hm⟩ := Agrees.err_eq hr6
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, he', ex_error_bind, AgreesBy]
          exact ErrMatchC.base hm
        have hvb := Agrees.ok_eq hr6
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hvb, ex_ok_bind]
        -- `c` is already done
        step with decode_variable_part.fixed_spec Bool.Insts.LibsszDecodeSszDecode rfl d6 c
          as ⟨ r7, d7, hr7, hd7 ⟩
        subst hr7 hd7
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        -- `d`: the body from the second offset to the end
        step with decode_variable_part.var_spec
          (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U16.Insts.LibsszDecodeSszDecode)
          (.list Desc.uint16 Usize.max)
          (fun v : alloc.vec.Vec Std.U16 => .seq (v.val.map fun x => .uint x.val)) rfl
          (fun s' hs' => by rw [← hUM]; exact U16.vec_from_ssz_bytes.spec s' hs') d7 none s 17 17
          [17, readUint (bytes s.val) 13 4] 1 hinv6 hs
          (by simp) s.length (by simp) (by simp; omega) (le_refl _) as ⟨ r8, d8, hr8, hinv8 ⟩
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hr8
        rcases r8 with vd | e8
        swap
        · obtain ⟨e', he', hm⟩ := Agrees.err_eq hr8
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, he', ex_error_bind, AgreesBy]
          exact ErrMatchC.base hm
        have hvd := Agrees.ok_eq hr8
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hvd, ex_ok_bind, WP.spec_ok,
          AgreesBy, Except.pure, exToV]
        rw [ha]
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        simp only [List.getLast_singleton] at hr4
        rcases hr4 with ⟨hlt, rfl⟩ | ⟨hge, hgt, a', b', rfl⟩
        · simp only [hlt, ↓reduceIte, AgreesBy]
          exact ErrMatchC.base (ErrMatch.offsetTable _ _ (Or.inl rfl) (Or.inl rfl))
        · simp only [show ¬ (readUint (bytes s.val) 13 4 < 17) by omega, hgt, ↓reduceIte, AgreesBy]
          exact ErrMatchC.base (ErrMatch.offsetTable _ _ (Or.inr ⟨_, _, rfl⟩) (Or.inr rfl))
    · -- the first offset is not 17
      obtain ⟨hne, g, hg, rfl⟩ := hr2
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      generalize hb : deserialize .bool ((bytes s.val).extract 12 13) = rb
      cases rb with
      | error e' =>
        obtain ⟨b, rfl⟩ := deserialize_bool_err _ (by simp [bytes_size]; omega) e' hb
        exact ErrMatchC.inlineFirst _ _ b
      | ok vb =>
        simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte, AgreesBy]
        have := ErrMatch.firstOffsetAt d1.fixed_part_len g
        rw [hfp1, hg] at this
        exact ErrMatchC.base this
  · -- the input is shorter than the fixed part
    obtain ⟨hlt, rfl⟩ := hr0
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, show s.length < 17 by omega, ↓reduceIte,
      AgreesBy]
    have := ErrMatch.fixedPart fpl s.len
    rw [hF, hl] at this
    exact ErrMatchC.base this

end Libssz.Proofs
