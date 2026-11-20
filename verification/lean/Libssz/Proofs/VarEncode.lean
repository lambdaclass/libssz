module
public import Libssz.Proofs.VarLists
-- To reason about `List.resize` (used by `Vec::resize`), whose body Aeneas does not expose.
import all Aeneas.Data.List.List
@[expose] public section

/-!
# Encode of lists of variable-size items, libssz ≡ EthLib

`encode_variable_length_items` (the `ssz_append` of a `Vec<T>` with variable-size `T`)
reserves the offset table filled with zeros, and on each iteration writes the offset of item
`i` (with `offset as u32`) and appends its body.

* `encode_var_loop.spec`: the loop invariant. After `i` iterations the buffer holds the
  prefix, the first `i` offsets, `4·(n − i)` zeros and the first `i` bodies.
* `vec_var_ssz_append.spec`: libssz **always** writes `varLayout P` (the table and the bodies),
  for any size. Since EthLib's `uintBytes 4` also keeps the low 32 bits (`uintBytes_mod32`),
  those bytes match what `assemble` builds even when it truncates.
* `encode_var_list.agrees`: if the total is shorter than 2³², libssz appends exactly the
  EthLib encoding.
* `encode_var_list.diverges`: **the offset-overflow divergence**. If each element is shorter
  than 2³² but the total is not, EthLib rejects (`offsetOverflow`) while libssz still writes
  the encoding, without an error, with truncated offsets.

All three are generic in the element type; `VecVecU8.encode.agrees` and
`VecVecU8.encode.diverges` instantiate them for `Vec<Vec<u8>>`.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
open Libssz.Proofs

namespace Libssz.Proofs

theorem setSlice!_eq {α : Type} (l s' : List α) (p : Nat) (h : p + s'.length ≤ l.length) :
    l.setSlice! p s' = l.take p ++ s' ++ l.drop (p + s'.length) := by
  simp only [List.setSlice!]
  have : min s'.length (l.length - p) = s'.length := by omega
  rw [this, List.take_length]

theorem map_setSlice! {α β : Type} (f : α → β) (l s' : List α) (p : Nat)
    (h : p + s'.length ≤ l.length) :
    (l.setSlice! p s').map f = (l.map f).setSlice! p (s'.map f) := by
  rw [setSlice!_eq _ _ _ h, setSlice!_eq _ _ _ (by simpa using h)]
  simp [List.map_take, List.map_drop]

/-- The bytes of the table written so far: offsets `0..i`. -/
def headPart (P : List Bytes) (i : Nat) : List UInt8 :=
  (concatParts ((List.range i).map fun k =>
    uintBytes 4 (P.length * 4 + (concatParts (P.take k)).size))).toList

theorem headPart_length (P : List Bytes) (i : Nat) : (headPart P i).length = 4 * i := by
  have : ∀ (f : Nat → Nat) (m : Nat),
      (concatParts ((List.range m).map fun k => uintBytes 4 (f k))).size = 4 * m := by
    intro f m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.map_append, concatParts_append]
      simp [concatParts, ih, uintBytes_size]; ring
  simp [headPart, this]

theorem headPart_succ (P : List Bytes) (i : Nat) :
    headPart P (i + 1) = headPart P i ++
      (uintBytes 4 (P.length * 4 + (concatParts (P.take i)).size)).toList := by
  simp [headPart, List.range_succ, concatParts_append, concatParts]

theorem concatParts_take_le (P : List Bytes) (k : Nat) :
    (concatParts (P.take k)).size ≤ (concatParts P).size := by
  conv_rhs => rw [← List.take_append_drop k P, concatParts_append]
  simp

theorem concatParts_take_succ (P : List Bytes) (k : Nat) (hk : k < P.length) :
    concatParts (P.take (k + 1)) = concatParts (P.take k) ++ P[k] := by
  rw [List.take_succ_eq_append_getElem hk, concatParts_append]
  simp [concatParts]

theorem vec_setSlice_val {α : Type} (v : alloc.vec.Vec α) (i : Nat) (s' : List α) :
    (alloc.vec.Vec.setSlice! v i s').val = v.val.setSlice! i s' := by
  change (Slice.setSlice! v.slice i s').val = v.val.setSlice! i s'
  rw [Slice.setSlice!_val]; rfl

theorem encode_var_loop.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (items : Slice T) (buf : alloc.vec.Vec Std.U8) (count start i : Std.Usize)
    (L0 : List UInt8) (hL0 : L0.length = start.val)
    (hcount : count.val = items.length) (hi : i.val ≤ count.val)
    (hbuf : buf.val.map byte = L0 ++ headPart (items.val.map encOf) i.val ++
      List.replicate (4 * (count.val - i.val)) 0 ++
      (concatParts ((items.val.map encOf).take i.val)).toList)
    (hmax : start.val + count.val * 4 + (concatParts (items.val.map encOf)).size ≤ Usize.max) :
    encode.encode_variable_length_items_loop inst items buf count start i ⦃ buf' =>
      buf'.val.map byte = L0 ++ (varLayout (items.val.map encOf)).toList ⦄ := by
  unfold encode.encode_variable_length_items_loop
  simp only [BYTES_PER_LENGTH_OFFSET]
  have hPl : (items.val.map encOf).length = count.val := by simp [hcount]
  have hlenb : buf.length = start.val + 4 * count.val +
      (concatParts ((items.val.map encOf).take i.val)).size := by
    have := congrArg List.length hbuf
    simp only [List.length_map, List.length_append, headPart_length, List.length_replicate,
      Array.length_toList, hL0] at this
    simp only [alloc.vec.Vec.length]
    have : 4 * i.val + 4 * (count.val - i.val) = 4 * count.val := by omega
    omega
  have hpre := concatParts_take_le (items.val.map encOf) i.val
  spec_split
  · have hlt : i.val < count.val := by scalar_tac
    step as ⟨ offset, hoff ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ pos, hpos ⟩
    step as ⟨ i3, hi3 ⟩
    step as ⟨ sl, back, hsl, hsll, hback ⟩
    simp only [lift, bind_ok, Array.to_slice]
    step as ⟨ s2, hs2 ⟩
    step as ⟨ t, ht ⟩
    have hbl : buf.len.val = buf.length := by simp
    have hoffv : offset.val = count.val * 4 +
        (concatParts ((items.val.map encOf).take i.val)).size := by
      rw [hoff, hbl, hlenb]; omega
    have hs2v : s2.val.map byte = (uintBytes 4 offset.val).toList := by
      rw [hs2, Slice.from_val]
      simp only [core.num.U32.to_le_bytes, Array.from_val]
      have := bytes_toLEBytes 4 (UScalar.cast UScalarTy.U32 offset).bv (by rfl)
      have h2 := congrArg Array.toList this
      simp only [bytes, List.toList_toArray] at h2
      rw [h2]
      have hc : (UScalar.cast UScalarTy.U32 offset).bv.toNat = offset.val % 2 ^ 32 := by
        have := UScalar.cast_val_eq UScalarTy.U32 offset
        rw [UScalarTy.U32_numBits_eq] at this
        exact this
      rw [hc, uintBytes_mod32]
    have hs2l : s2.val.length = 4 := by
      have := congrArg List.length hs2v; simp [uintBytes_size] at this; simpa using this
    set P := items.val.map encOf with hP
    clear_value P
    have hHl := headPart_length P i.val
    have hrep : 4 * (count.val - i.val) = 4 + 4 * (count.val - (i.val + 1)) := by omega
    have hlenL : (L0 ++ headPart P i.val).length = pos.val := by
      rw [List.length_append, hHl, hL0, hpos, hi2]; ring
    have hb1 : (back s2).val.map byte = L0 ++ headPart P i.val ++ (uintBytes 4 offset.val).toList ++
        List.replicate (4 * (count.val - (i.val + 1))) 0 ++ (concatParts (P.take i.val)).toList := by
      have hbl2 : pos.val + s2.val.length ≤ buf.val.length := by
        rw [hs2l]; simp [alloc.vec.Vec.length] at hlenb; scalar_tac
      rw [hback, vec_setSlice_val, map_setSlice! _ _ _ _ hbl2,
        setSlice!_eq _ _ _ (by simpa using hbl2), hbuf, hs2v, hrep, List.replicate_add,
        Array.length_toList, uintBytes_size]
      rw [show L0 ++ headPart P i.val ++ (List.replicate 4 (0 : UInt8) ++
          List.replicate (4 * (count.val - (i.val + 1))) 0) ++ (concatParts (P.take i.val)).toList =
          (L0 ++ headPart P i.val) ++ (List.replicate 4 (0 : UInt8) ++
          (List.replicate (4 * (count.val - (i.val + 1))) 0 ++ (concatParts (P.take i.val)).toList))
          by simp only [List.append_assoc]]
      rw [List.take_left' hlenL, ← List.drop_drop, List.drop_left' hlenL,
        List.drop_left' (by simp)]
      simp only [List.append_assoc]
    have hb1l : (back s2).length = buf.length := by
      have := congrArg List.length hb1
      simp only [List.length_map] at this
      simp only [alloc.vec.Vec.length, this, List.length_append, hHl, List.length_replicate,
        Array.length_toList, uintBytes_size, hL0]
      simp only [alloc.vec.Vec.length] at hlenb
      omega
    have hPi : (P[i.val]'(by rw [hPl]; exact hlt)) = encOf t := by simp [hP, ht]
    have htake := concatParts_take_succ P i.val (by rw [hPl]; exact hlt)
    have hle2 : (concatParts (P.take (i.val + 1))).size ≤ (concatParts P).size :=
      concatParts_take_le P (i.val + 1)
    step with helem t (back s2) (by
      rw [hb1l, hlenb]
      rw [htake, hPi, Array.size_append] at hle2
      omega) as ⟨ buf2, hbuf2 ⟩
    step as ⟨ i5, hi5 ⟩
    have hgoal := encode_var_loop.spec inst encOf helem items buf2 count start i5 L0 hL0 hcount
      (by scalar_tac)
    rw [← hP] at hgoal
    refine hgoal ?_ hmax
    have := congrArg Array.toList hbuf2
    simp only [bytes, List.toList_toArray, Array.toList_append] at this
    rw [this, hb1, hi5, headPart_succ, htake, hPi, Array.toList_append, hoffv, hPl]
    simp only [List.append_assoc]
  · simp only [WP.spec_ok]
    have : i.val = count.val := by scalar_tac
    rw [hbuf, this, Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil,
      List.take_of_length_le (by rw [hPl])]
    simp only [varLayout, Array.toList_append, runningOffsets_eq, hPl, headPart, List.append_assoc,
      List.map_map, Function.comp_def]
termination_by count.val - i.val
decreasing_by all_goals (simp only [show ((1#usize : Std.Usize).val) = 1 from rfl] at *; omega)

theorem encode_var_items.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (items : Slice T) (buf : alloc.vec.Vec Std.U8)
    (hmax : buf.length + items.length * 4 + (concatParts (items.val.map encOf)).size ≤ Usize.max) :
    encode.encode_variable_length_items inst items buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ varLayout (items.val.map encOf) ⦄ := by
  unfold encode.encode_variable_length_items
  simp only [step_simps, BYTES_PER_LENGTH_OFFSET]
  step as ⟨ fpl, hfpl ⟩
  step as ⟨ n, hn ⟩
  step as ⟨ buf1, hbuf1 ⟩
  have hbl : buf.len.val = buf.length := by simp
  have hil : items.len.val = items.length := by simp
  apply WP.spec_mono (encode_var_loop.spec inst encOf helem items buf1 items.len buf.len 0#usize
    (buf.val.map byte) (by simp [hbl]) hil (by simp) ?_ (by rw [hbl, hil]; exact hmax))
  · intro b h
    simp [bytes, h]
  · rw [hbuf1, hn, hfpl, hbl, hil]
    simp only [List.resize, List.take_of_length_le
      (show buf.val.length ≤ buf.length + items.length * 4 by simp [alloc.vec.Vec.length]),
      headPart]
    simp [concatParts, alloc.vec.Vec.length, Nat.mul_comm]
    exact Or.inr rfl

theorem vec_var_ssz_append.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (hvar : inst.is_fixed_size = ok false)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (v : alloc.vec.Vec T) (buf : alloc.vec.Vec Std.U8)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map encOf)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append inst v buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ varLayout (v.val.map encOf) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [hvar, bind_ok, Bool.false_eq_true, ↓reduceIte]
  have := encode_var_items.spec inst encOf helem (alloc.vec.Vec.deref v) buf
    (by simpa [alloc.vec.Vec.deref] using hmax)
  simpa [alloc.vec.Vec.deref] using this

theorem concatParts_mem_le (P : List Bytes) (p : Bytes) (hp : p ∈ P) :
    p.size ≤ (concatParts P).size := by
  induction P with
  | nil => simp at hp
  | cons q rest ih =>
    simp only [concatParts, Array.size_append]
    rcases List.mem_cons.mp hp with rfl | h
    · omega
    · have := ih h; omega

/-- **Encode of a list of variable-size items, for any element type.** libssz always writes
`varLayout` (the offset table and the bodies). If each element is shorter than 2³², EthLib
gives that same encoding when the total is shorter than 2³², and rejects it
(`offsetOverflow`) when it is not. -/
theorem encode_var_list.spec {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (d : Desc) (toV : T → Value) (hd : d.isFixed = false) (hvar : inst.is_fixed_size = ok false)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (hser : ∀ x, (encOf x).size < 2 ^ 32 → serialize d (toV x) = .ok (encOf x))
    (v : alloc.vec.Vec T) (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map encOf)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append inst v buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ varLayout (v.val.map encOf) ∧
      ((∀ x ∈ v.val, (encOf x).size < 2 ^ 32) →
        serialize (.list d limit) (.seq (v.val.map toV)) =
          if (varLayout (v.val.map encOf)).size ≥ 2 ^ 32 then
            .error (.offsetOverflow (varLayout (v.val.map encOf)).size)
          else .ok (varLayout (v.val.map encOf))) ⦄ := by
  apply WP.spec_mono (vec_var_ssz_append.spec inst encOf hvar helem v buf hmax)
  intro buf' h
  refine ⟨h, fun hsmall => ?_⟩
  apply serialize_list_var d hd limit _ _ _ (by simpa using hl)
  exact serializeEach_of d toV encOf v.val (fun x hx => hser x (hsmall x hx))

/-- **Equivalence** (total < 2³²): libssz appends exactly the EthLib encoding. -/
theorem encode_var_list.agrees {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (d : Desc) (toV : T → Value) (hd : d.isFixed = false) (hvar : inst.is_fixed_size = ok false)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (hser : ∀ x, (encOf x).size < 2 ^ 32 → serialize d (toV x) = .ok (encOf x))
    (v : alloc.vec.Vec T) (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : (varLayout (v.val.map encOf)).size < 2 ^ 32)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map encOf)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append inst v buf ⦃ buf' =>
      ∃ enc, serialize (.list d limit) (.seq (v.val.map toV)) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (encode_var_list.spec inst encOf d toV hd hvar helem hser v buf limit hl hmax)
  rintro buf' ⟨h1, h2⟩
  refine ⟨_, ?_, h1⟩
  have hsmall : ∀ x ∈ v.val, (encOf x).size < 2 ^ 32 := by
    intro x hx
    have := concatParts_mem_le (v.val.map encOf) (encOf x) (List.mem_map_of_mem hx)
    rw [varLayout_size] at hsz
    omega
  rw [h2 hsmall]
  simp only [show ¬ ((varLayout (v.val.map encOf)).size ≥ 2 ^ 32) by omega, ↓reduceIte]

/-- **The offset-overflow divergence.** If each element is shorter than 2³² but the total is
not, EthLib rejects the encoding (`offsetOverflow`) while libssz still writes it, without an
error: `varLayout` with offsets that `uintBytes 4` (like `offset as u32`) truncates to their
low 32 bits. -/
theorem encode_var_list.diverges {T : Type} (inst : encode.SszEncode T) (encOf : T → Bytes)
    (d : Desc) (toV : T → Value) (hd : d.isFixed = false) (hvar : inst.is_fixed_size = ok false)
    (helem : ∀ x (b : alloc.vec.Vec Std.U8), b.length + (encOf x).size ≤ Usize.max →
      inst.ssz_append x b ⦃ b' => bytes b'.val = bytes b.val ++ encOf x ⦄)
    (hser : ∀ x, (encOf x).size < 2 ^ 32 → serialize d (toV x) = .ok (encOf x))
    (v : alloc.vec.Vec T) (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hsmall : ∀ x ∈ v.val, (encOf x).size < 2 ^ 32)
    (hbig : (varLayout (v.val.map encOf)).size ≥ 2 ^ 32)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map encOf)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append inst v buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ varLayout (v.val.map encOf) ∧
      serialize (.list d limit) (.seq (v.val.map toV)) =
        .error (.offsetOverflow (varLayout (v.val.map encOf)).size) ⦄ := by
  apply WP.spec_mono (encode_var_list.spec inst encOf d toV hd hvar helem hser v buf limit hl hmax)
  rintro buf' ⟨h1, h2⟩
  exact ⟨h1, by rw [h2 hsmall]; simp only [hbig, ↓reduceIte]⟩

/-! ## `Vec<Vec<u8>>` -/

/-- The SSZ bytes of a `Vec<u8>`: the byte of each element. -/
def u8sBytes (w : alloc.vec.Vec Std.U8) : Bytes := concatParts (w.val.map fun x => uintBytes 1 x.val)

theorem u8sBytes_size (w : alloc.vec.Vec Std.U8) : (u8sBytes w).size = w.length := by
  have hsz : ∀ p ∈ w.val.map (fun x => uintBytes 1 x.val), p.size = 1 := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨x, _, rfl⟩ := hp
    exact uintBytes_size _ _
  rw [u8sBytes, concatParts_size 1 _ hsz]
  simp [alloc.vec.Vec.length]

theorem VecU8.ssz_append.bytes_spec (w b : alloc.vec.Vec Std.U8)
    (h : b.length + (u8sBytes w).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append U8.Insts.LibsszEncodeSszEncode w b
      ⦃ b' => bytes b'.val = bytes b.val ++ u8sBytes w ⦄ := by
  rw [u8sBytes_size] at h
  unfold alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [U8.Insts.LibsszEncodeSszEncode, U8.Insts.LibsszEncodeSszEncode.is_fixed_size,
    step_simps]
  unfold U8.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice
  simp only [↓reduceIte, step_simps, alloc.vec.Vec.reserve, bind_ok]
  apply WP.spec_mono (U8.encode_loop.spec (alloc.vec.Vec.deref w) b 0#usize (by simp)
    (by simp [alloc.vec.Vec.deref] at *; scalar_tac))
  intro b' hb'
  rw [hb', u8sBytes]
  simp [alloc.vec.Vec.deref]

theorem VecU8.serialize (w : alloc.vec.Vec Std.U8) (hw : (u8sBytes w).size < 2 ^ 32) :
    serialize (.list Desc.uint8 core.num.Usize.MAX.val) (.seq (w.val.map fun x => .uint x.val)) =
      .ok (u8sBytes w) := by
  rw [u8sBytes_size] at hw
  have hfit : ∀ n ∈ w.val.map (·.val), n < 2 ^ (8 * 1) := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨x, _, rfl⟩ := hn
    have := x.hBounds; simpa using this
  have := serialize_list_uint 1 core.num.Usize.MAX.val (w.val.map (·.val)) hfit
    (by simp [alloc.vec.Vec.length] at *) (by simpa [alloc.vec.Vec.length] using hw)
  simp only [List.map_map] at this
  rw [show Desc.uint8 = .uint 1 from rfl]
  convert this using 2 <;> simp [u8sBytes, Function.comp_def]

/-- **Encode `Vec<Vec<u8>>` ≡ EthLib**, if the encoding is shorter than 2³². -/
theorem VecVecU8.encode.agrees (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hsz : (varLayout (v.val.map u8sBytes)).size < 2 ^ 32)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map u8sBytes)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
      (alloc.vec.Vec.Insts.LibsszEncodeSszEncode U8.Insts.LibsszEncodeSszEncode) v buf ⦃ buf' =>
      ∃ enc, serialize (.list (.list Desc.uint8 core.num.Usize.MAX.val) limit)
          (.seq (v.val.map fun w => .seq (w.val.map fun x => .uint x.val))) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ :=
  encode_var_list.agrees _ u8sBytes _ _ rfl rfl
    (fun w b h => VecU8.ssz_append.bytes_spec w b h) (fun w hw => VecU8.serialize w hw)
    v buf limit hl hsz hmax

/-- **The offset-overflow divergence in `Vec<Vec<u8>>`**: with inner lists shorter than 4 GiB
each but a total of 4 GiB or more, libssz writes truncated offsets and EthLib rejects. -/
theorem VecVecU8.encode.diverges (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (buf : alloc.vec.Vec Std.U8) (limit : Nat) (hl : v.length ≤ limit)
    (hsmall : ∀ w ∈ v.val, w.length < 2 ^ 32)
    (hbig : (varLayout (v.val.map u8sBytes)).size ≥ 2 ^ 32)
    (hmax : buf.length + v.length * 4 + (concatParts (v.val.map u8sBytes)).size ≤ Usize.max) :
    alloc.vec.Vec.Insts.LibsszEncodeSszEncode.ssz_append
      (alloc.vec.Vec.Insts.LibsszEncodeSszEncode U8.Insts.LibsszEncodeSszEncode) v buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ varLayout (v.val.map u8sBytes) ∧
      serialize (.list (.list Desc.uint8 core.num.Usize.MAX.val) limit)
          (.seq (v.val.map fun w => .seq (w.val.map fun x => .uint x.val))) =
        .error (.offsetOverflow (varLayout (v.val.map u8sBytes)).size) ⦄ :=
  encode_var_list.diverges _ u8sBytes _ _ rfl rfl
    (fun w b h => VecU8.ssz_append.bytes_spec w b h) (fun w hw => VecU8.serialize w hw)
    v buf limit hl (fun w hw => by rw [u8sBytes_size]; exact hsmall w hw) hbig hmax

end Libssz.Proofs
