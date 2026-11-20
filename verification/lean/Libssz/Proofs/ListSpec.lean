module
public import Libssz.Proofs.Bytes
public import EthLib.Serialization.Proofs.Ssz.Codec.Table
@[expose] public section

/-!
# Lists of integers in EthLib

Lemmas about the specification (they do not mention the Rust code): what `Ssz.deserialize`
and `Ssz.serialize` return on lists of integers, in closed form.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz

namespace Libssz.Proofs

/-- Chunk `k` of `w` bytes of `l`, read as a little-endian number. -/
def chunkVal (w : Nat) (l : List Std.U8) (k : Nat) : Nat :=
  leValue UScalar.val ((l.drop (k * w)).take w)

theorem bytes_extract (l : List Std.U8) (a b : Nat) :
    (bytes l).extract a b = bytes ((l.drop a).take (b - a)) := by
  simp [bytes, List.map_drop, List.map_take]

theorem readUint_bytes_of_length (c : List Std.U8) (w : Nat) (h : c.length = w) :
    readUint (bytes c) 0 w = leValue UScalar.val c := by
  subst h; exact readUint_bytes c

theorem deserializeEach_uint (w : Nat) :
    ∀ (slices : List Bytes), (∀ s ∈ slices, s.size = w) →
      deserializeEach (.uint w) slices = .ok (slices.map fun s => .uint (readUint s 0 w)) := by
  intro slices h
  induction slices with
  | nil => exact deserializeEach_nil _
  | cons s rest ih =>
    rw [deserializeEach_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hs := h s List.mem_cons_self
    simp [deserialize, hs]

/-- **`Ssz.deserialize` of a list of `w`-byte integers**, in closed form, for every input
shorter than 2³² bytes: empty; rejection if the length is not a multiple of `w`; rejection if
it exceeds the limit; or the chunks read as little-endian. -/
theorem deserialize_list_uint (w cap : Nat) (l : List Std.U8) (hw : 0 < w)
    (hs : l.length < 2 ^ 32) :
    deserialize (.list (.uint w) cap) (bytes l) =
      if l.length = 0 then .ok (.seq [])
      else if l.length % w ≠ 0 then .error (.scopeUndivided l.length w)
      else if l.length / w > cap then .error (.overLimit cap (l.length / w))
      else .ok (.seq ((List.range (l.length / w)).map fun k => .uint (chunkVal w l k))) := by
  rw [deserialize]
  simp only [listSlices_eq, bytes_size, Desc.fixedSize, bytesPerOffset]
  have h32 : ¬ l.length ≥ 2 ^ (8 * 4) := by norm_num; omega
  have hw0 : (w == 0) = false := by simp; omega
  simp only [h32, ↓reduceIte, hw0, Bool.false_eq_true]
  by_cases h0 : l.length = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    show (Value.seq <$> deserializeEach (Desc.uint w) []) = _
    rw [deserializeEach_nil]; rfl
  by_cases hm : l.length % w = 0
  swap
  · simp [h0, hm]; rfl
  by_cases hc : l.length / w > cap
  · simp [h0, hm, hc]; rfl
  have h0' : (l.length == 0) = false := by simp [h0]
  have hm' : (l.length % w != 0) = false := by simp [hm]
  simp only [h0', hm', hc, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hsz : ∀ x ∈ (List.range (l.length / w)).map
      (fun i => Array.extract (bytes l) (i * w) ((i + 1) * w)), x.size = w := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have : (i + 1) * w ≤ l.length := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
      have : i + 1 ≤ l.length / w := hi
      nlinarith
    rw [Array.size_extract, bytes_size, Nat.min_eq_left this, Nat.add_mul, Nat.one_mul]
    omega
  rw [deserializeEach_uint w _ hsz, List.map_map]
  simp only [h0, hm, ne_eq, not_true_eq_false, ↓reduceIte]
  show Except.ok (Value.seq _) = Except.ok (Value.seq _)
  congr 2
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have hle : (i + 1) * w ≤ l.length := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
    have : i + 1 ≤ l.length / w := hi
    nlinarith
  rw [Nat.add_mul, Nat.one_mul] at hle
  have hw' : (i + 1) * w - i * w = w := by rw [Nat.add_mul, Nat.one_mul]; omega
  simp only [Function.comp, bytes_extract, hw']
  rw [readUint_bytes_of_length _ w (by simp; omega)]
  rfl

theorem serializeEach_uint (w : Nat) :
    ∀ ns : List Nat, (∀ n ∈ ns, n < 2 ^ (8 * w)) →
      serializeEach (.uint w) (ns.map .uint) = .ok (ns.map (uintBytes w)) := by
  intro ns h
  induction ns with
  | nil => exact serializeEach_nil _
  | cons n rest ih =>
    rw [List.map_cons, serializeEach_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hn := h n List.mem_cons_self
    simp [serialize, hn]
    rfl

/-- **`Ssz.serialize` of a list of `w`-byte integers**: the concatenation of each one. -/
theorem serialize_list_uint (w limit : Nat) (ns : List Nat) (hfit : ∀ n ∈ ns, n < 2 ^ (8 * w))
    (hl : ns.length ≤ limit) (hsz : w * ns.length < 2 ^ 32) :
    serialize (.list (.uint w) limit) (.seq (ns.map .uint)) =
      .ok (concatParts (ns.map (uintBytes w))) := by
  rw [serialize]
  simp only [List.length_map, hl, ↓reduceIte, serializeSequence]
  rw [serializeEach_uint w ns hfit]
  show assemble ((ns.map (uintBytes w)).map fun _ => (Desc.uint w).isFixed) (ns.map (uintBytes w)) = _
  rw [show (Desc.uint w).isFixed = true from rfl, assemble_inline_eq,
    concatParts_size w _ (by simp [uintBytes_size])]
  have : ¬ ((ns.map (uintBytes w)).length * w ≥ 2 ^ (8 * bytesPerOffset)) := by
    simp only [List.length_map, bytesPerOffset]; norm_num; rw [Nat.mul_comm]; omega
  simp only [this, ↓reduceIte]

/-! ## Lists of `byteVector w` -/

theorem deserializeEach_byteVector (w : Nat) (hw32 : w < 2 ^ 32) :
    ∀ (slices : List Bytes), (∀ s ∈ slices, s.size = w) →
      deserializeEach (.byteVector w) slices = .ok (slices.map .bytes) := by
  intro slices h
  induction slices with
  | nil => exact deserializeEach_nil _
  | cons s rest ih =>
    rw [deserializeEach_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hs := h s List.mem_cons_self
    have : ¬ (2 ^ (8 * bytesPerOffset) ≤ w) := by norm_num [bytesPerOffset]; exact hw32
    simp [deserialize, hs, this]

/-- **`Ssz.deserialize` of a list of `byteVector w`**, in closed form, for every input
shorter than 2³² bytes and `w > 0`. -/
theorem deserialize_list_byteVector (w cap : Nat) (l : List Std.U8) (hw : 0 < w)
    (hs : l.length < 2 ^ 32) :
    deserialize (.list (.byteVector w) cap) (bytes l) =
      if l.length = 0 then .ok (.seq [])
      else if l.length % w ≠ 0 then .error (.scopeUndivided l.length w)
      else if l.length / w > cap then .error (.overLimit cap (l.length / w))
      else .ok (.seq ((List.range (l.length / w)).map fun k => .bytes (bytes ((l.drop (k * w)).take w)))) := by
  rw [deserialize]
  simp only [listSlices_eq, bytes_size, Desc.fixedSize, bytesPerOffset]
  have h32 : ¬ l.length ≥ 2 ^ (8 * 4) := by norm_num; omega
  have hw0 : (w == 0) = false := by simp; omega
  simp only [h32, ↓reduceIte, hw0, Bool.false_eq_true]
  by_cases h0 : l.length = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    show (Value.seq <$> deserializeEach (Desc.byteVector w) []) = _
    rw [deserializeEach_nil]; rfl
  by_cases hm : l.length % w = 0
  swap
  · simp [h0, hm]; rfl
  by_cases hc : l.length / w > cap
  · simp [h0, hm, hc]; rfl
  have h0' : (l.length == 0) = false := by simp [h0]
  have hm' : (l.length % w != 0) = false := by simp [hm]
  simp only [h0', hm', hc, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hsz : ∀ x ∈ (List.range (l.length / w)).map
      (fun i => Array.extract (bytes l) (i * w) ((i + 1) * w)), x.size = w := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have : (i + 1) * w ≤ l.length := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
      have : i + 1 ≤ l.length / w := hi
      nlinarith
    rw [Array.size_extract, bytes_size, Nat.min_eq_left this, Nat.add_mul, Nat.one_mul]
    omega
  have hw32 : w < 2 ^ 32 := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
    have : 1 ≤ l.length / w := Nat.one_le_iff_ne_zero.mpr (by intro h; rw [h] at this; omega)
    nlinarith
  rw [deserializeEach_byteVector w hw32 _ hsz, List.map_map]
  simp only [h0, hm, ne_eq, not_true_eq_false, ↓reduceIte]
  show Except.ok (Value.seq _) = Except.ok (Value.seq _)
  congr 2
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have hle : (i + 1) * w ≤ l.length := by
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
    have : i + 1 ≤ l.length / w := hi
    nlinarith
  rw [Nat.add_mul, Nat.one_mul] at hle
  have hw' : (i + 1) * w - i * w = w := by rw [Nat.add_mul, Nat.one_mul]; omega
  simp only [Function.comp, bytes_extract, hw']

theorem serializeEach_byteVector (w : Nat) (hw32 : w < 2 ^ 32) :
    ∀ ds : List Bytes, (∀ d ∈ ds, d.size = w) →
      serializeEach (.byteVector w) (ds.map .bytes) = .ok ds := by
  intro ds h
  induction ds with
  | nil => exact serializeEach_nil _
  | cons d rest ih =>
    rw [List.map_cons, serializeEach_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hd := h d List.mem_cons_self
    have : ¬ (2 ^ (8 * bytesPerOffset) ≤ w) := by norm_num [bytesPerOffset]; exact hw32
    simp [serialize, hd, this]

/-- **`Ssz.serialize` of a list of `byteVector w`**: the concatenation of the elements. -/
theorem serialize_list_byteVector (w limit : Nat) (ds : List Bytes) (hd : ∀ d ∈ ds, d.size = w)
    (hw32 : w < 2 ^ 32) (hl : ds.length ≤ limit) (hsz : w * ds.length < 2 ^ 32) :
    serialize (.list (.byteVector w) limit) (.seq (ds.map .bytes)) = .ok (concatParts ds) := by
  rw [serialize]
  simp only [List.length_map, hl, ↓reduceIte, serializeSequence]
  rw [serializeEach_byteVector w hw32 ds hd]
  show assemble (ds.map fun _ => (Desc.byteVector w).isFixed) ds = _
  rw [show (Desc.byteVector w).isFixed = true from rfl, assemble_inline_eq,
    concatParts_size w _ hd]
  have : ¬ (ds.length * w ≥ 2 ^ (8 * bytesPerOffset)) := by
    simp only [bytesPerOffset]; norm_num; rw [Nat.mul_comm]; omega
  simp only [this, ↓reduceIte]


/-! ## Lists of `bool` -/

/-- The one-byte slices of `bytes l` are the bytes of `l`, one at a time. -/
theorem single_slices (l : List Std.U8) :
    (List.range l.length).map (fun i => (bytes l).extract (i * 1) ((i + 1) * 1)) =
      l.map fun b => bytes [b] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Nat.mul_one, bytes_extract,
    Nat.add_sub_cancel_left]
  congr 1
  simp at h2
  rw [List.take_one, List.drop_eq_getElem_cons h2]
  rfl

/-- **`Ssz.deserialize` of a list of `bool`**: validate the length and decode each byte. -/
theorem deserialize_list_bool (cap : Nat) (l : List Std.U8) (hs : l.length < 2 ^ 32) :
    deserialize (.list .bool cap) (bytes l) =
      if l.length = 0 then .ok (.seq [])
      else if l.length > cap then .error (.overLimit cap l.length)
      else Value.seq <$> deserializeEach .bool (l.map fun b => bytes [b]) := by
  rw [deserialize]
  simp only [listSlices_eq, bytes_size, Desc.fixedSize, bytesPerOffset]
  have h32 : ¬ l.length ≥ 2 ^ (8 * 4) := by norm_num; omega
  simp only [h32, ↓reduceIte]
  by_cases h0 : l.length = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    show (Value.seq <$> deserializeEach Desc.bool []) = _
    rw [deserializeEach_nil]; rfl
  have h0' : (l.length == 0) = false := by simp [h0]
  simp only [h0', h0, Bool.false_eq_true, ↓reduceIte, Nat.mod_one, Nat.div_one]
  by_cases hc : l.length > cap
  · simp [hc]; rfl
  simp only [hc, ↓reduceIte, show ((1 : Nat) == 0) = false from rfl,
    show ((0 : Nat) != 0) = false from rfl, Bool.false_eq_true, pure_bind, single_slices]
  rfl

/-- The byte of a `bool` in SSZ. -/
def boolByte (b : Bool) : Bytes := #[if b then 1 else 0]

theorem serializeEach_bool :
    ∀ bs : List Bool, serializeEach .bool (bs.map .bool) = .ok (bs.map boolByte) := by
  intro bs
  induction bs with
  | nil => exact serializeEach_nil _
  | cons b rest ih =>
    rw [List.map_cons, serializeEach_cons, ih]
    simp [serialize, boolByte]
    rfl

/-- **`Ssz.serialize` of a list of `bool`**: one byte `0` or `1` per element. -/
theorem serialize_list_bool (limit : Nat) (bs : List Bool) (hl : bs.length ≤ limit)
    (hsz : bs.length < 2 ^ 32) :
    serialize (.list .bool limit) (.seq (bs.map .bool)) = .ok (concatParts (bs.map boolByte)) := by
  rw [serialize]
  simp only [List.length_map, hl, ↓reduceIte, serializeSequence]
  rw [serializeEach_bool bs]
  show assemble ((bs.map boolByte).map fun _ => Desc.bool.isFixed) (bs.map boolByte) = _
  rw [show Desc.bool.isFixed = true from rfl, assemble_inline_eq,
    concatParts_size 1 _ (by intro p hp; simp only [List.mem_map] at hp; obtain ⟨b, _, rfl⟩ := hp; cases b <;> rfl)]
  have : ¬ ((bs.map boolByte).length * 1 ≥ 2 ^ (8 * bytesPerOffset)) := by
    simp only [List.length_map, bytesPerOffset, Nat.mul_one]; norm_num; omega
  simp only [this, ↓reduceIte]

end Libssz.Proofs
