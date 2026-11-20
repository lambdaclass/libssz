module
public import Libssz.Proofs.Lists
public import Libssz.Proofs.OffsetSpec
@[expose] public section

/-!
# Lists of variable-size items, libssz ≡ EthLib

The pieces on the Rust side:

* `read_offset.spec`: reading 4 bytes at `pos` is EthLib's `readUint` at `pos`.
* `read_item_offsets_loop.spec`: the loop that reads the offset table returns `Ok` (the table
  plus the total length) if and only if the table is valid (`Mono` and `Bounded`); otherwise,
  `Err` with `OffsetsAreNotMonotonicallyIncreasing` or `OffsetOutOfBounds`.
* `decode_items_loop.spec`: the loop that decodes each body walks the same slices as EthLib's
  `deserializeEach`, **for any element type** whose decode matches EthLib (the hypothesis
  `helem`).

The theorem that puts them together is `decode_var_list.spec`, at the end.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
open Libssz.Proofs

namespace Libssz.Proofs

theorem read_offset.spec (s : Slice Std.U8) (pos : Std.Usize) (h : pos.val + 4 ≤ s.length) :
    decode.read_offset s pos ⦃ r =>
      match r with
      | .Ok v => v.val = readUint (bytes s.val) pos.val 4
      | .Err _ => False ⦄ := by
  unfold decode.read_offset
  simp only [step_simps, BYTES_PER_LENGTH_OFFSET]
  step as ⟨ i, hi ⟩
  have hlen := Slice.len_val s
  have hle : ¬ (i > s.len) := by scalar_tac
  simp only [hle, ↓reduceIte]
  step as ⟨ b, back, hb, hback ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ s1, hs1, hs1l ⟩
  step as ⟨ s2, hs2 ⟩
  step as ⟨ x, hx ⟩
  step as ⟨ y, hy ⟩
  have hlen4 : s1.val.length = 4 := by simp [Slice.length] at hs1l; scalar_tac
  have hback4 : (back s2).val = s1.val := by
    rw [hback, hs2]; exact Array.from_slice_val _ _ (by simpa using hlen4)
  have hxv : x.val = leValue UScalar.val ((s.val.drop pos.val).take 4) := by
    have : x.val = (BitVec.fromLEBytes (List.map U8.bv (back s2).val)).toNat := by
      simp [UScalar.val, hx]
    rw [this, toNat_fromLEBytes, leValue_map, hback4, hs1, List.slice, hi2,
      Nat.add_sub_cancel_left]
    rfl
  have hxb : x.val < 2 ^ 32 := by have := x.hBounds; simpa using this
  have hyv : y.val = x.val := by
    rw [hy, UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have : 32 ≤ UScalarTy.Usize.numBits := by
      simp [UScalarTy.numBits]
    exact lt_of_lt_of_le hxb (Nat.pow_le_pow_right (by norm_num) this)
  rw [hyv, hxv, readUint_bytes_at _ _ _ h]

/-- Offset `j` of the table at the start of `s`. -/
def offAt (s : Slice Std.U8) (j : Nat) : Nat := readUint (bytes s.val) (j * 4) 4

theorem mono_succ (f : Nat → Nat) (i : Nat) (h : Mono f i) (h' : 0 < i → f (i - 1) ≤ f i) :
    Mono f (i + 1) := by
  intro j hj
  rcases Nat.lt_or_ge (j + 1) i with hlt | hge
  · exact h j hlt
  · have : j + 1 = i := by omega
    subst this; simpa using h' (by omega)

theorem bounded_succ (f : Nat → Nat) (i s : Nat) (h : Bounded f i s) (h' : f i ≤ s) :
    Bounded f (i + 1) s := by
  intro j hj
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact h j hlt
  · rw [show j = i by omega]; exact h'

theorem read_item_offsets_loop.spec (s : Slice Std.U8) (n : Std.Usize)
    (offsets : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (hn : n.val * 4 ≤ s.length) (hi : i.val ≤ n.val)
    (hoff : offsets.val.map (·.val) = (List.range i.val).map (offAt s))
    (hv : Mono (offAt s) i.val ∧ Bounded (offAt s) i.val s.length) :
    decode.read_item_offsets_loop s n offsets i ⦃ r =>
      match r with
      | .Ok v => v.val.map (·.val) = (List.range n.val).map (offAt s) ++ [s.length] ∧
          Mono (offAt s) n.val ∧ Bounded (offAt s) n.val s.length
      | .Err e => ¬ (Mono (offAt s) n.val ∧ Bounded (offAt s) n.val s.length) ∧
          (e = .OffsetsAreNotMonotonicallyIncreasing ∨ ∃ o l, e = .OffsetOutOfBounds o l) ⦄ := by
  unfold decode.read_item_offsets_loop
  have hlen := Slice.len_val s
  have hol : offsets.length = i.val := by
    have := congrArg List.length hoff; simp at this; simpa using this
  simp only [BYTES_PER_LENGTH_OFFSET]
  spec_split
  · have hlt : i.val < n.val := by scalar_tac
    step as ⟨ i1, hi1 ⟩
    step with read_offset.spec s i1 (by rw [hi1]; nlinarith) as ⟨ r, hr ⟩
    cases r with
    | Err e => exact hr.elim
    | Ok v =>
      have hvv : v.val = offAt s i.val := by rw [hr, offAt, hi1]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hmono := hv.1
      have hbnd := hv.2
      have hget : ∀ k (hk : k < offsets.val.length), (offsets.val[k]).val = offAt s k := by
        intro k hk
        have h1 := List.getElem_of_eq hoff (i := k) (by simpa using hk)
        simpa using h1
      split
      · -- i > 0: compare with the previous offset
        rename_i hpos
        have hpos' : 0 < i.val := by scalar_tac
        step as ⟨ i2, hi2 ⟩
        step as ⟨ i3, hi3 ⟩
        have hi3v : i3.val = offAt s (i.val - 1) := by
          rw [hi3]; rw [hget _ (by simp [hol, hi2]; omega)]; rw [hi2]
        split
        · rename_i hlt2
          simp only [WP.spec_ok]
          refine ⟨fun ⟨hm, _⟩ => ?_, by simp⟩
          have := hm (i.val - 1) (by omega)
          rw [show i.val - 1 + 1 = i.val by omega] at this
          have : v.val < i3.val := by scalar_tac
          omega
        · rename_i hge2
          split
          · rename_i hgt
            simp only [WP.spec_ok]
            refine ⟨fun ⟨_, hb⟩ => ?_, by simp⟩
            have := hb i.val hlt
            have : v.val > s.length := by scalar_tac
            omega
          · rename_i hle
            step as ⟨ o1, ho1 ⟩
            step as ⟨ i5, hi5 ⟩
            apply read_item_offsets_loop.spec s n o1 i5 hn (by scalar_tac)
            · rw [ho1, List.map_append, hoff, hi5, List.range_succ, List.map_append]; simp [hvv]
            · rw [hi5]
              refine ⟨mono_succ _ _ hmono (fun _ => ?_), bounded_succ _ _ _ hbnd ?_⟩
              · have : ¬ v.val < i3.val := by scalar_tac
                omega
              · have : ¬ v.val > s.length := by scalar_tac
                omega
      · -- i = 0
        rename_i hz
        have hz' : i.val = 0 := by scalar_tac
        split
        · simp only [WP.spec_ok]
          refine ⟨fun ⟨_, hb⟩ => ?_, by simp⟩
          have := hb i.val hlt
          have : v.val > s.length := by scalar_tac
          omega
        · step as ⟨ o1, ho1 ⟩
          step as ⟨ i5, hi5 ⟩
          apply read_item_offsets_loop.spec s n o1 i5 hn (by scalar_tac)
          · rw [ho1, List.map_append, hoff, hi5, List.range_succ, List.map_append]; simp [hvv]
          · rw [hi5]
            refine ⟨mono_succ _ _ hmono (fun h => absurd h (by omega)), bounded_succ _ _ _ hbnd ?_⟩
            have : ¬ v.val > s.length := by scalar_tac
            omega
  · step as ⟨ o1, ho1 ⟩
    have : i.val = n.val := by scalar_tac
    rw [← this]
    refine ⟨?_, hv⟩
    rw [ho1, List.map_append, hoff]
    simp [hlen]
termination_by n.val - i.val
decreasing_by all_goals (simp at *; omega)

theorem decode_items_loop.spec {T : Type} (inst : decode.SszDecode T) (d : Desc) (toV : T → Value)
    (helem : ∀ s : Slice Std.U8, s.length < 2 ^ 32 →
      inst.from_ssz_bytes s ⦃ r => Agrees toV r (deserialize d (bytes s.val)) ⦄)
    (src : Slice Std.U8) (hs : src.length < 2 ^ 32) (offsets : Slice Std.Usize) (n : Std.Usize)
    (result : alloc.vec.Vec T) (j : Std.Usize) (O : List Nat)
    (hO : offsets.val.map (·.val) = O) (hOl : O.length = n.val + 1)
    (hsorted : ∀ k, k < n.val → O[k]! ≤ O[k + 1]!) (hbnd : ∀ k, k ≤ n.val → O[k]! ≤ src.length)
    (hj : j.val ≤ n.val) (hrl : result.length = j.val) :
    decode.decode_items_loop inst src offsets n result j ⦃ r =>
      Agrees (fun v : alloc.vec.Vec T => .seq (v.val.map toV)) r
        ((fun vs => .seq (result.val.map toV ++ vs)) <$>
          deserializeEach d ((List.range' j.val (n.val - j.val)).map
            fun k => (bytes src.val).extract O[k]! O[k + 1]!)) ⦄ := by
  unfold decode.decode_items_loop
  have hget : ∀ k (hk : k < offsets.val.length), (offsets.val[k]).val = O[k]! := by
    intro k hk
    have h1 := List.getElem_of_eq hO (i := k) (by simpa using hk)
    simp only [List.getElem_map] at h1
    rw [h1, getElem!_pos]
  have hol : offsets.val.length = n.val + 1 := by
    have := congrArg List.length hO; simp at this; omega
  spec_split
  · have hlt : j.val < n.val := by scalar_tac
    step as ⟨ a, ha ⟩
    step as ⟨ j1, hj1 ⟩
    step as ⟨ b, hb ⟩
    have hav : a.val = O[j.val]! := by rw [ha]; exact hget _ (by simp [Slice.length] at *; omega)
    have hbv : b.val = O[j.val + 1]! := by
      rw [hb, hget _ (by simp [Slice.length] at *; omega), hj1]
    have hab : a.val ≤ b.val := by rw [hav, hbv]; exact hsorted _ hlt
    have hbl : b.val ≤ src.length := by rw [hbv]; exact hbnd _ (by omega)
    step as ⟨ sl, hsl, hsll ⟩
    have hslen : sl.length < 2 ^ 32 := by rw [hsll]; omega
    step with helem sl hslen as ⟨ r, hr ⟩
    have hslv : bytes sl.val = (bytes src.val).extract O[j.val]! O[j.val + 1]! := by
      rw [hsl, List.slice, bytes_extract, hav, hbv]
    rw [hslv] at hr
    rw [show n.val - j.val = (n.val - (j.val + 1)) + 1 by omega, List.range'_succ, List.map_cons,
      deserializeEach_cons]
    generalize deserialize d ((bytes src.val).extract O[j.val]! O[j.val + 1]!) = e at hr ⊢
    cases r with
    | Ok x =>
      cases e with
      | error e => exact hr.elim
      | ok w =>
        simp only [Agrees] at hr
        subst hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨ result1, hr1 ⟩
        apply WP.spec_mono (decode_items_loop.spec inst d toV helem src hs offsets n result1 j1 O
          hO hOl hsorted hbnd (by scalar_tac) (by simp [hr1, hrl]; scalar_tac))
        intro r' h'
        rw [hj1] at h'
        generalize deserializeEach d ((List.range' (j.val + 1) (n.val - (j.val + 1))).map
          fun k => (bytes src.val).extract O[k]! O[k + 1]!) = e2 at h' ⊢
        cases e2 with
        | error e => exact h'
        | ok ts =>
          simp only [hr1, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h'
          exact h'
    | Err err =>
      cases e with
      | ok w => exact hr.elim
      | error e' =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [bind_tc_ok, WP.spec_ok]
        exact hr
  · simp only [WP.spec_ok]
    have : j.val = n.val := by scalar_tac
    rw [this, Nat.sub_self, List.range'_zero, List.map_nil, deserializeEach_nil]
    simp [Agrees]
termination_by n.val - j.val
decreasing_by scalar_decr_tac


/-! ## The list theorem -/

theorem tbl_get (f : Nat → Nat) (n s k : Nat) (hk : k < n) :
    ((List.range n).map f ++ [s])[k]! = f k := by
  rw [getElem!_pos _ k (by simp; omega), List.getElem_append_left (by simpa using hk)]
  simp

theorem tbl_last (f : Nat → Nat) (n s : Nat) : ((List.range n).map f ++ [s])[n]! = s := by
  rw [getElem!_pos _ n (by simp), List.getElem_append_right (by simp)]
  simp

/-- `decode_variable_length_items_with_max` against `deserialize (.list d max)`, for non-empty
inputs shorter than 2³² bytes and any variable-size element whose decode matches. -/
theorem decode_var_items.spec {T : Type} (inst : decode.SszDecode T) (d : Desc) (toV : T → Value)
    (hd : d.fixedSize = none)
    (helem : ∀ s : Slice Std.U8, s.length < 2 ^ 32 →
      inst.from_ssz_bytes s ⦃ r => Agrees toV r (deserialize d (bytes s.val)) ⦄)
    (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) (h0 : s.length ≠ 0) :
    decode.decode_variable_length_items_with_max inst s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec T => .seq (v.val.map toV)) r
        (deserialize (.list d max.val) (bytes s.val)) ⦄ := by
  have hlen := Slice.len_val s
  rw [deserialize]
  simp only [listSlices, bytes_size, hd, bytesPerOffset]
  have h32 : ¬ (↑s : List Std.U8).length ≥ 2 ^ (8 * 4) := by norm_num; exact hs
  have h0' : ((↑s : List Std.U8).length == 0) = false := by
    have : (↑s : List Std.U8).length ≠ 0 := h0
    simpa using this
  simp only [h32, h0', Bool.false_eq_true, ↓reduceIte]
  unfold decode.decode_variable_length_items_with_max
  simp only [step_simps, BYTES_PER_LENGTH_OFFSET]
  by_cases h4 : s.length < 4
  · have h4r : s.len < 4#usize := by scalar_tac
    have h4' : (↑s : List Std.U8).length < 4 := h4
    simp only [h4r, h4', ↓reduceIte, WP.spec_ok]
    have := ErrMatch.tooSmall s.len
    rw [hlen] at this
    exact this
  have h4r : ¬ (s.len < 4#usize) := by scalar_tac
  have h4' : ¬ ((↑s : List Std.U8).length < 4) := h4
  simp only [h4r, h4', ↓reduceIte]
  step with read_offset.spec s 0#usize (by simp; omega) as ⟨ r, hr ⟩
  cases r with
  | Err e => exact hr.elim
  | Ok first =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hF : first.val = readUint (bytes s.val) 0 4 := hr
  generalize hFv : readUint (bytes s.val) 0 4 = F at hF ⊢
  step as ⟨ m, hm ⟩
  by_cases hma : F % 4 = 0
  swap
  · -- the first offset is not a multiple of 4
    have hmr : (m != 0#usize) = true := by simp; scalar_tac
    simp only [hmr, ↓reduceIte, WP.spec_ok]
    by_cases hlow : F < 4
    · simp only [hlow, ↓reduceIte]
      exact ErrMatch.firstOffset _ _ _ (Or.inl rfl)
    · have hmod : (F % 4 != 0) = true := by simp; omega
      simp only [hlow, hmod, ↓reduceIte]
      exact ErrMatch.firstOffset _ _ _ (Or.inr rfl)
  have hmr : (m != 0#usize) = false := by simp; scalar_tac
  simp only [hmr, Bool.false_eq_true, ↓reduceIte]
  have hmod : (F % 4 != 0) = false := by simp [hma]
  by_cases hgt : F > s.length
  · -- the first offset is past the length
    have hgtr : first > s.len := by scalar_tac
    have hlow : ¬ F < 4 := by omega
    have hgt' : F > (↑s : List Std.U8).length := hgt
    simp only [hgtr, ↓reduceIte, WP.spec_ok, hlow, hmod, hgt', Bool.false_eq_true]
    exact ErrMatch.offsetTable _ _ (Or.inr ⟨_, _, rfl⟩) (Or.inr rfl)
  have hgtr : ¬ first > s.len := by scalar_tac
  have hgt' : ¬ F > (↑s : List Std.U8).length := hgt
  simp only [hgtr, ↓reduceIte, hgt']
  step as ⟨ num, hnum ⟩
  have hnumv : num.val = F / 4 := by rw [hnum, hF]
  by_cases hz : F = 0
  · have hzr : num = 0#usize := by scalar_tac
    have hlow : F < 4 := by omega
    simp only [hzr, ↓reduceIte, WP.spec_ok, hlow]
    exact ErrMatch.firstOffset _ _ _ (Or.inl rfl)
  have hzr : ¬ num = 0#usize := by intro h; rw [h] at hnumv; simp at hnumv; omega
  have hlow : ¬ F < 4 := by omega
  simp only [hzr, ↓reduceIte, hlow, hmod, Bool.false_eq_true]
  by_cases hcap : F / 4 > max.val
  · have hcapr : num > max := by scalar_tac
    simp only [hcapr, ↓reduceIte, WP.spec_ok, hcap]
    have := ErrMatch.overLimit max num
    rw [hnumv] at this
    exact this
  have hcapr : ¬ num > max := by scalar_tac
  simp only [hcapr, ↓reduceIte, hcap]
  unfold decode.read_item_offsets
  simp only [step_simps]
  step as ⟨ np1, hnp1 ⟩
  have hn4 : num.val * 4 ≤ s.length := by rw [hnumv]; omega
  have hnpos : 0 < num.val := by rw [hnumv]; omega
  step with read_item_offsets_loop.spec s num (alloc.vec.Vec.with_capacity Std.Usize np1) 0#usize
    hn4 (by simp) (by simp [alloc.vec.Vec.with_capacity])
    ⟨fun j hj => by simp at hj, fun j hj => by simp at hj⟩ as ⟨ r1, hr1 ⟩
  have hoffs : readOffsets (bytes s.val) (F / 4) = (List.range num.val).map (offAt s) := by
    rw [hnumv]; rfl
  rw [hoffs]
  have hne : (List.range num.val).map (offAt s) ≠ [] := by simp; omega
  cases r1 with
  | Ok v =>
    obtain ⟨hv, hmono, hbnd⟩ := hr1
    simp only [bind_ok]
    have hchain : ChainOK ((List.range num.val).map (offAt s)) s.length :=
      (chainOK_iff _ _ _ hnpos).mpr ⟨hmono, hbnd⟩
    simp only [offsetSpans, offsetSpansFrom_ok _ _ [] hne hchain, List.reverse_nil, List.nil_append]
    show decode.decode_items inst s v.deref num ⦃ r =>
      Agrees (fun v : alloc.vec.Vec T => Value.seq (v.val.map toV)) r (do
        let xs ← deserializeEach d (List.zipWith
          (fun start span => (bytes s.val).extract start (start + span))
          ((List.range num.val).map (offAt s)) (diffs ((List.range num.val).map (offAt s)) s.length))
        Except.pure (Value.seq xs)) ⦄
    rw [slices_eq _ _ _ hchain]
    unfold decode.decode_items
    simp only [step_simps]
    have hsorted : ∀ k, k < num.val →
        ((List.range num.val).map (offAt s) ++ [s.length])[k]! ≤
          ((List.range num.val).map (offAt s) ++ [s.length])[k + 1]! := by
      intro k hk
      rw [tbl_get _ _ _ _ hk]
      rcases Nat.lt_or_ge (k + 1) num.val with h1 | h1
      · rw [tbl_get _ _ _ _ h1]; exact hmono k h1
      · rw [show k + 1 = num.val by omega, tbl_last]; exact hbnd k hk
    have hbnd' : ∀ k, k ≤ num.val →
        ((List.range num.val).map (offAt s) ++ [s.length])[k]! ≤ s.length := by
      intro k hk
      rcases Nat.lt_or_ge k num.val with h1 | h1
      · rw [tbl_get _ _ _ _ h1]; exact hbnd k h1
      · rw [show k = num.val by omega, tbl_last]
    apply WP.spec_mono (decode_items_loop.spec inst d toV helem s hs v.deref num
      (alloc.vec.Vec.with_capacity T num) 0#usize _ (by simpa [alloc.vec.Vec.deref] using hv)
      (by simp) hsorted hbnd' (by simp) (by simp [alloc.vec.Vec.with_capacity]))
    intro r h
    rw [List.length_map, List.length_range]
    rw [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero, ← List.range_eq_range'] at h
    revert h
    generalize deserializeEach d ((List.range num.val).map fun k =>
      (bytes s.val).extract ((List.range num.val).map (offAt s) ++ [s.length])[k]!
        ((List.range num.val).map (offAt s) ++ [s.length])[k + 1]!) = e
    intro h
    cases e <;> (simp [alloc.vec.Vec.with_capacity] at h; exact h)
  | Err e =>
    obtain ⟨hnot, he⟩ := hr1
    have hnc : ¬ ChainOK ((List.range num.val).map (offAt s)) s.length :=
      fun h => hnot ((chainOK_iff _ _ _ hnpos).mp h)
    obtain ⟨e', he', he'k⟩ := offsetSpansFrom_err _ _ [] hne hnc
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp only [bind_tc_ok, WP.spec_ok, offsetSpans, he']
    exact ErrMatch.offsetTable e e' he he'k

/-- **Decode of a list of variable-size items, for any element type.** If the decode of each
element matches `deserialize d` (`helem`), the decode of the list matches
`deserialize (.list d max)`. -/
theorem decode_var_list.spec {T : Type} (inst : decode.SszDecode T) (d : Desc) (toV : T → Value)
    (hd : d.fixedSize = none) (hvar : inst.is_fixed_size = ok false)
    (helem : ∀ s : Slice Std.U8, s.length < 2 ^ 32 →
      inst.from_ssz_bytes s ⦃ r => Agrees toV r (deserialize d (bytes s.val)) ⦄)
    (s : Slice Std.U8) (max : Std.Usize) (hs : s.length < 2 ^ 32) :
    decode.decode_list_with_max inst s max ⦃ r =>
      Agrees (fun v : alloc.vec.Vec T => .seq (v.val.map toV)) r
        (deserialize (.list d max.val) (bytes s.val)) ⦄ := by
  unfold decode.decode_list_with_max
  step as ⟨ b, hb ⟩
  by_cases h0 : s.length = 0
  · have hb' : b = true := by simpa [h0] using hb
    have hd0 : deserialize (.list d max.val) (bytes s.val) = .ok (.seq []) := by
      rw [deserialize]
      have h0' : (↑s : List Std.U8).length = 0 := h0
      simp only [listSlices, bytes_size, h0',
        show ¬ (0 ≥ 2 ^ (8 * bytesPerOffset)) by norm_num [bytesPerOffset], ↓reduceIte,
        beq_self_eq_true, pure_bind]
      rw [deserializeEach_nil]
      rfl
    simp only [hb', ↓reduceIte, WP.spec_ok, hd0, Agrees]
    rfl
  have hb' : b = false := by simpa [h0] using hb
  simp only [hb', Bool.false_eq_true, ↓reduceIte, hvar, bind_ok]
  exact decode_var_items.spec inst d toV hd helem s max hs h0

/-- `Vec<Vec<u8>>::from_ssz_bytes`, built from `Vec<u8>`. -/
theorem VecU8.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
      (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U8.Insts.LibsszDecodeSszDecode) s ⦃ r =>
      Agrees (fun v : alloc.vec.Vec (alloc.vec.Vec Std.U8) =>
          .seq (v.val.map fun w => .seq (w.val.map fun x => .uint x.val))) r
        (deserialize (.list (.list Desc.uint8 core.num.Usize.MAX.val) core.num.Usize.MAX.val)
          (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact decode_var_list.spec _ _ _ rfl rfl (fun s' hs' => U8.vec_from_ssz_bytes.spec s' hs') s _ hs

/-- `Vec<Vec<Vec<u8>>>::from_ssz_bytes`, built from the previous one: the theorem composes. -/
theorem VecVecU8.vec_from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
      (alloc.vec.Vec.Insts.LibsszDecodeSszDecode
        (alloc.vec.Vec.Insts.LibsszDecodeSszDecode U8.Insts.LibsszDecodeSszDecode)) s ⦃ r =>
      Agrees (fun v : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Std.U8)) =>
          .seq (v.val.map fun w => .seq (w.val.map fun y => .seq (y.val.map fun x => .uint x.val)))) r
        (deserialize (.list (.list (.list Desc.uint8 core.num.Usize.MAX.val) core.num.Usize.MAX.val)
          core.num.Usize.MAX.val) (bytes s.val)) ⦄ := by
  unfold alloc.vec.Vec.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  exact decode_var_list.spec _ _ _ rfl rfl
    (fun s' hs' => VecU8.vec_from_ssz_bytes.spec s' hs') s _ hs

end Libssz.Proofs
