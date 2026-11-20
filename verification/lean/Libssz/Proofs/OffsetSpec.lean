module
public import Libssz.Proofs.ListSpec
public import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
@[expose] public section

/-!
# The offset table in EthLib

Lemmas about the specification (they do not mention the Rust code): when `offsetSpans`
accepts an offset table, with which errors it rejects it, and which slices it builds.

* `offsetSpansFrom_ok` / `offsetSpansFrom_err`: EthLib accepts the table if and only if
  `ChainOK` (increasing offsets and the last one within the length); otherwise it rejects with
  `offsetUnordered` or `offsetPastScope`.
* `chainOK_iff`: `ChainOK` is equivalent to what libssz checks offset by offset (`Mono`,
  increasing, and `Bounded`, each one within the length). They accept the same tables, although
  on a bad table they may reject with different errors (libssz first checks each offset
  against the length).
* `slices_eq`: body `k` goes from `offs[k]` to `offs[k+1]`, with `offs = table ++ [length]`.
-/

open Aeneas Aeneas.Std
open EthLib.Serialization.Ssz

namespace Libssz.Proofs

/-- The offset table EthLib accepts: increasing, and the last one does not exceed `s`. -/
def ChainOK : List Nat → Nat → Prop
  | [], _ => True
  | [a], s => a ≤ s
  | a :: b :: rest, s => a ≤ b ∧ ChainOK (b :: rest) s

/-- The width of each body: the distance to the next offset, or to `s` for the last one. -/
def diffs : List Nat → Nat → List Nat
  | [], _ => []
  | [a], s => [s - a]
  | a :: b :: rest, s => (b - a) :: diffs (b :: rest) s

theorem offsetSpansFrom_ok : ∀ (l : List Nat) (s : Nat) (done : List Nat), l ≠ [] →
    ChainOK l s → offsetSpansFrom l s done = .ok (done.reverse ++ diffs l s)
  | [], _, _, h, _ => absurd rfl h
  | [a], s, done, _, h => by
    simp only [ChainOK] at h
    simp [offsetSpansFrom, diffs, Nat.not_lt.mpr h]
  | a :: b :: rest, s, done, _, h => by
    simp only [ChainOK] at h
    simp only [offsetSpansFrom, show ¬ (b < a) from Nat.not_lt.mpr h.1, ↓reduceIte]
    rw [offsetSpansFrom_ok (b :: rest) s _ (List.cons_ne_nil _ _) h.2]
    simp [diffs]

theorem offsetSpansFrom_err : ∀ (l : List Nat) (s : Nat) (done : List Nat), l ≠ [] →
    ¬ ChainOK l s → ∃ e, offsetSpansFrom l s done = .error e ∧
      (e = .offsetUnordered ∨ e = .offsetPastScope)
  | [], _, _, h, _ => absurd rfl h
  | [a], s, done, _, h => by
    simp only [ChainOK, Nat.not_le] at h
    exact ⟨_, by simp [offsetSpansFrom, h], Or.inr rfl⟩
  | a :: b :: rest, s, done, _, h => by
    simp only [ChainOK, not_and_or, Nat.not_le] at h
    by_cases hab : b < a
    · exact ⟨_, by simp [offsetSpansFrom, hab], Or.inl rfl⟩
    · simp only [offsetSpansFrom, hab, ↓reduceIte]
      rcases h with h | h
      · omega
      · exact offsetSpansFrom_err (b :: rest) s _ (List.cons_ne_nil _ _) h

/-- Increasing offsets (what libssz checks between consecutive offsets). -/
def Mono (f : Nat → Nat) (n : Nat) : Prop := ∀ j, j + 1 < n → f j ≤ f (j + 1)

/-- All offsets within `s` (what libssz checks on each offset). -/
def Bounded (f : Nat → Nat) (n s : Nat) : Prop := ∀ j, j < n → f j ≤ s

theorem chainOK_range' (f : Nat → Nat) (s : Nat) : ∀ m k,
    ChainOK ((List.range' k (m + 1)).map f) s ↔
      (∀ j, k ≤ j → j + 1 < k + m + 1 → f j ≤ f (j + 1)) ∧ f (k + m) ≤ s := by
  intro m
  induction m with
  | zero => intro k; simp [List.range', ChainOK]; intro j h1 h2; omega
  | succ m ih =>
    intro k
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, List.range'_succ, List.map_cons,
      show (List.range' (k + 1) (m + 1)).map f = f (k + 1) :: (List.range' (k + 2) m).map f by
        rw [List.range'_succ]; rfl]
    simp only [ChainOK]
    rw [show f (k + 1) :: (List.range' (k + 2) m).map f = (List.range' (k + 1) (m + 1)).map f by
        rw [List.range'_succ]; rfl, ih (k + 1)]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun j hj1 hj2 => ?_, by rw [show k + (m + 1) = k + 1 + m by omega]; exact h2⟩
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · exact h0
      · exact h1 j (by omega) (by omega)
    · rintro ⟨h1, h2⟩
      exact ⟨h1 k le_rfl (by omega), fun j hj1 hj2 => h1 j (by omega) (by omega),
        by rw [show k + 1 + m = k + (m + 1) by omega]; exact h2⟩

theorem mono_le_last (f : Nat → Nat) (n : Nat) (h : Mono f n) :
    ∀ j, j < n → f j ≤ f (n - 1) := by
  have key : ∀ d j, j + d = n - 1 → j < n → f j ≤ f (n - 1) := by
    intro d
    induction d with
    | zero => intro j hj _; rw [show j = n - 1 by omega]
    | succ d ih =>
      intro j hj hjn
      exact le_trans (h j (by omega)) (ih (j + 1) (by omega) (by omega))
  intro j hj
  exact key (n - 1 - j) j (by omega) hj

/-- libssz accepts the table (increasing and each one within `s`) if and only if EthLib
accepts it (increasing and the last one within `s`). -/
theorem chainOK_iff (f : Nat → Nat) (n s : Nat) (hn : 0 < n) :
    ChainOK ((List.range n).map f) s ↔ Mono f n ∧ Bounded f n s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_eq_range', chainOK_range' f s m 0]
  constructor
  · rintro ⟨h1, h2⟩
    have hm : Mono f (m + 1) := fun j hj => h1 j (Nat.zero_le _) (by omega)
    refine ⟨hm, fun j hj => le_trans (mono_le_last f (m + 1) hm j hj) ?_⟩
    simpa using h2
  · rintro ⟨h1, h2⟩
    exact ⟨fun j _ hj => h1 j (by omega), by simpa using h2 m (by omega)⟩

theorem slices_pairs (data : Bytes) : ∀ (l : List Nat) (s : Nat), ChainOK l s →
    List.zipWith (fun start span => data.extract start (start + span)) l (diffs l s) =
      List.zipWith (fun a b => data.extract a b) l (l.tail ++ [s])
  | [], _, _ => rfl
  | [a], s, h => by
    simp only [ChainOK] at h
    simp [diffs, Nat.add_sub_cancel' h]
  | a :: b :: rest, s, h => by
    simp only [ChainOK] at h
    simp only [diffs, List.zipWith_cons_cons, List.tail_cons, List.cons_append]
    rw [Nat.add_sub_cancel' h.1, slices_pairs data (b :: rest) s h.2]
    rfl

/-- **The slices EthLib builds**: element `k` goes from `offs[k]` to `offs[k+1]`, where
`offs = l ++ [s]` (the last body ends at the total length). -/
theorem slices_eq (data : Bytes) (l : List Nat) (s : Nat) (h : ChainOK l s) :
    List.zipWith (fun start span => data.extract start (start + span)) l (diffs l s) =
      (List.range l.length).map fun k => data.extract ((l ++ [s])[k]!) ((l ++ [s])[k + 1]!) := by
  rw [slices_pairs data l s h]
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
  simp at h2
  have hk : k < (l ++ [s]).length := by simp; omega
  have hk1 : k + 1 < (l ++ [s]).length := by simp; omega
  rw [getElem!_pos (l ++ [s]) k hk, getElem!_pos (l ++ [s]) (k + 1) hk1]
  congr 1
  · rw [List.getElem_append_left h2]
  · cases l with
    | nil => simp at h2
    | cons a rest =>
      simp only [List.tail_cons, List.cons_append, List.getElem_cons_succ]

/-- Reading `w` little-endian bytes at position `pos` of Rust bytes. -/
theorem readUint_bytes_at (l : List Std.U8) (pos w : Nat) (h : pos + w ≤ l.length) :
    readUint (bytes l) pos w = leValue Aeneas.Std.UScalar.val ((l.drop pos).take w) := by
  have := readUint_extract (bytes l) pos (pos + w) 0 w (by omega) (by simpa using h)
  rw [Nat.add_zero] at this
  rw [← this, bytes_extract, Nat.add_sub_cancel_left]
  exact readUint_bytes_of_length _ w (by simp; omega)


/-! ## Encode: the table built by `assemble` -/

/-- The encoding of a list of variable parts: the offset table (each one, where its body
starts) and then the bodies. This is what EthLib's `assemble` builds. -/
def varLayout (P : List Bytes) : Bytes :=
  concatParts ((runningOffsets (P.length * 4) P).map (uintBytes 4)) ++ concatParts P

theorem varLayout_size (P : List Bytes) : (varLayout P).size = P.length * 4 + (concatParts P).size := by
  have : ∀ (s : Nat) (Q : List Bytes),
      (concatParts ((runningOffsets s Q).map (uintBytes 4))).size = Q.length * 4 := by
    intro s Q
    induction Q generalizing s with
    | nil => rfl
    | cons q rest ih => simp [runningOffsets, concatParts, ih, uintBytes_size]; ring
  simp [varLayout, this]

/-- **`Ssz.serialize` of a list of variable-size elements** whose encodings are `P`: the
`varLayout`, if it is shorter than 2³²; otherwise, `offsetOverflow`. -/
theorem serialize_list_var (d : Desc) (hd : d.isFixed = false) (limit : Nat) (vs : List Value)
    (P : List Bytes) (hP : serializeEach d vs = .ok P) (hl : vs.length ≤ limit) :
    serialize (.list d limit) (.seq vs) =
      if (varLayout P).size ≥ 2 ^ 32 then .error (.offsetOverflow (varLayout P).size)
      else .ok (varLayout P) := by
  rw [serialize]
  simp only [hl, ↓reduceIte, serializeSequence, hP]
  show assemble (P.map fun _ => d.isFixed) P = _
  rw [hd, assemble_eq]
  have hw := headWidth_offset P
  have hbw : bodyWidth (offsetSlots P) = (concatParts P).size := by
    rw [← bodiesOf_size, bodiesOf_offset]
  have hhead : headOf (headWidth (offsetSlots P)) (offsetSlots P) ++ bodiesOf (offsetSlots P) =
      varLayout P := by
    rw [hw, headOf_offsets, bodiesOf_offset, varLayout]
  have htot : headWidth (offsetSlots P) + bodyWidth (offsetSlots P) = (varLayout P).size := by
    rw [hw, hbw, varLayout_size]
  simp only [offsetSlots] at hhead htot
  simp only [htot, hhead, show 2 ^ (8 * bytesPerOffset) = 2 ^ 32 from rfl]
  split <;> rfl

theorem runningOffsets_eq : ∀ (s : Nat) (P : List Bytes),
    runningOffsets s P = (List.range P.length).map fun k => s + (concatParts (P.take k)).size
  | s, [] => rfl
  | s, p :: rest => by
    rw [runningOffsets, runningOffsets_eq (s + p.size) rest, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [concatParts, Function.comp_def, Nat.add_assoc]

/-- `uintBytes 4` keeps the 4 low bytes: it gives the same result with `n` and with
`n mod 2³²`. This is why libssz's `offset as u32` writes the same bytes as EthLib. -/
theorem uintBytes_mod32 (n : Nat) : uintBytes 4 (n % 2 ^ 32) = uintBytes 4 n := by
  simp only [uintBytes, EthLib.Base.uintToBytes]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  apply UInt8.toNat_inj.mp
  simp only [Nat.shiftRight_eq_div_pow]
  have h32 : (2 : Nat) ^ 32 = 2 ^ (8 * i) * 2 ^ (32 - 8 * i) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h32, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact ⟨2 ^ (32 - 8 * i - 8), by rw [← Nat.pow_add]; congr 1; omega⟩

theorem serializeEach_of {α : Type} (d : Desc) (toV : α → Value) (encOf : α → Bytes) :
    ∀ xs : List α, (∀ x ∈ xs, serialize d (toV x) = .ok (encOf x)) →
      serializeEach d (xs.map toV) = .ok (xs.map encOf)
  | [], _ => serializeEach_nil _
  | x :: rest, h => by
    rw [List.map_cons, serializeEach_cons, h x List.mem_cons_self,
      serializeEach_of d toV encOf rest (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

end Libssz.Proofs
