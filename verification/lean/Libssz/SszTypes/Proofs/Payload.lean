module
public import Libssz.SszTypes.Proofs.Roots
@[expose] public section

/-!
# `ExecutionPayload` (capella): byte lists, lists of lists and lists of containers

`ExecutionPayload` has the three list cases that were still missing:

* bytes in `SszList<u8, N>` and `SszVector<u8, N>`: the specification's `ByteList[N]` and
  `ByteVector[N]` (`extra_data`, `logs_bloom`);
* a list of lists: `transactions`, `List[ByteList[2^30], 2^20]`;
* a list of containers: `withdrawals`, `List[Withdrawal, 16]`.

The last two require the item to implement `SszEncode` in Rust. In the extractions, the
`SszEncode` trait is the codec's (see `scripts/link.py`), and the one the macro derives for
`Withdrawal` uses `ContainerEncoder`, also from the codec. The list theorems do not use it.
-/

open Aeneas Aeneas.Std Result
open Libssz.Proofs (byte bytes leValue)
open EthLib.Serialization.Ssz
open Libssz.Merkle

namespace Libssz.SszTypes

/-! ## Bytes -/

/-- `basic_items_bytes` of `u8`: the same bytes. It is the default `ssz_fixed_slice_to_vec`,
with the `ssz_append_fixed_slice` of `u8`, which is an `extend_from_slice`. -/
theorem basic_items_bytes_u8.spec (items : Slice Std.U8) :
    libssz_merkle.basic_items_bytes libssz_types.U8.Insts.LibsszEncodeSszEncode items ⦃ out =>
      bytes out.val = bytes items.val ⦄ := by
  unfold libssz_merkle.basic_items_bytes
  simp only [libssz_types.U8.Insts.LibsszEncodeSszEncode, libssz_merkle.U8.Insts.LibsszEncodeSszEncode,
    libssz_codec.U8.Insts.LibsszEncodeSszEncode,
    libssz_codec.U8.Insts.LibsszEncodeSszEncode.is_fixed_size, bind_ok, ↓reduceIte,
    libssz_codec.U8.Insts.LibsszEncodeSszEncode.fixed_size,
    libssz_codec.U8.Insts.LibsszEncodeSszEncode.ssz_append_fixed_slice]
  step as ⟨ i2, hi2 ⟩
  step as ⟨ out, hout ⟩
  · simp [alloc.vec.Vec.with_capacity]
  rw [hout]
  simp [alloc.vec.Vec.with_capacity]

/-- **The root of a `ByteList[N]`** according to EthLib: the tree of the packed bytes, with
the capacity of `N` bytes, and the length mixed in on the right. -/
theorem hashTreeRoot_byteList (limit : Nat) (data : Bytes) (hl : data.size ≤ limit) :
    hashTreeRoot (.byteList limit) (.bytes data) =
      (merkleizeBoundedUnchecked (packBytes data) (some (chunksForBytes limit))).map
        (fun root => mixIn root (lengthWord data.size)) := by
  rw [hashTreeRoot_eq_nesting, show (Desc.byteList limit).nesting = 1 from rfl,
    hashTreeRootAt_succ]
  have hlay : merkleLayout (.byteList limit) (.bytes data) =
      .ok (MerkleLayout.packing (packBytes data) (some (chunksForBytes limit))
        (some (lengthWord data.size))) := by
    simp [merkleLayout, Nat.not_lt.mpr hl, Pure.pure, Except.pure]
  simp only [hlay, Bind.bind, Except.bind]
  simp only [layoutChunksAt_eq, MerkleLayout.packing, Leaves.count, Option.getD_none,
    Array.extract_size]
  cases hm : merkleizeBoundedUnchecked (packBytes data) (some (chunksForBytes limit)) <;>
    simp [hm, Pure.pure, Except.pure, Except.map]

section Bytes

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **`SszList<u8, N>`** (for example `extra_data`): the `hash_tree_root` is EthLib's for
`ByteList[N]`. -/
theorem SszListU8.hash_tree_root.spec {N : Std.Usize} (l : libssz_types.list.SszList Std.U8 N)
    (hlen : l.length ≤ N.val) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      libssz_types.U8.Insts.Libssz_merkleHashTreeRoot
      libssz_types.U8.Insts.LibsszEncodeSszEncode inst l h ⦃ r =>
      hashTreeRoot (.byteList N.val) (.bytes (bytes l.val)) = .ok (bytes r.val) ⦄ := by
  have h1 : (1#usize : Std.Usize).val = 1 := rfl
  have hlv : alloc.vec.Vec.length l = (l.val).length := rfl
  apply WP.spec_mono (SszList.basic_rust inst h hl _ _ rfl 1#usize rfl l (bytes l.val) ?_
    (by rw [h1, Nat.mul_one]; scalar_tac) (by simp [h1]; omega))
  · intro r hr
    rw [hashTreeRoot_byteList N.val _ (by simp; omega), Libssz.Proofs.bytes_size]
    rw [h1, Nat.mul_one] at hr
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    apply WP.spec_mono (basic_items_bytes_u8.spec (alloc.vec.Vec.deref l))
    intro out hout
    rw [hout]
    simp [alloc.vec.Vec.deref]

include hl in
/-- **`SszVector<u8, N>`** (for example `logs_bloom`): EthLib's for `ByteVector[N]`. -/
theorem SszVectorU8.hash_tree_root.spec {N : Std.Usize}
    (v : libssz_types.vector.SszVector Std.U8 N) (hlen : v.length = N.val) :
    libssz_types.vector.SszVector.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      libssz_types.U8.Insts.Libssz_merkleHashTreeRoot
      libssz_types.U8.Insts.LibsszEncodeSszEncode inst v h ⦃ r =>
      hashTreeRoot (.byteVector N.val) (.bytes (bytes v.val)) = .ok (bytes r.val) ⦄ := by
  have h1 : (1#usize : Std.Usize).val = 1 := rfl
  have hlv : alloc.vec.Vec.length v = (v.val).length := rfl
  have hs : (bytes v.val).size = N.val := by simp; omega
  apply WP.spec_mono (SszVector.basic_rust inst h hl _ _ rfl 1#usize rfl v (bytes v.val) ?_
    (by rw [h1, Nat.mul_one]; scalar_tac) (by simp [h1]; omega))
  · intro r hr
    rw [← hs, hashTreeRoot_byteVector]
    rw [h1, Nat.mul_one, show chunksForBytes N.val = (packBytes (bytes v.val)).size by
      rw [packBytes_size, hs]; rfl, merkleizeBounded_some_self, merkleizeBounded_none] at hr
    exact hr
  · rw [basic_items_bytes_eq _ rfl]
    apply WP.spec_mono (basic_items_bytes_u8.spec (alloc.vec.Vec.deref v))
    intro out hout
    rw [hout]
    simp [alloc.vec.Vec.deref]

include hl in
/-- The rows of `SszList<u8, M>` are the default ones: the root alone. They require the list's
invariant: that it has at most `M` bytes. -/
theorem SszListU8.rows {M : Std.Usize} :
    Rows inst h (libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot M
        libssz_types.U8.Insts.Libssz_merkleHashTreeRoot libssz_types.U8.Insts.LibsszEncodeSszEncode)
      (.byteList M.val) (fun x => .bytes (bytes x.val)) (fun x => x.length ≤ M.val) 0 :=
  Rows.of_default inst h _ _ _ _ rfl (fun _ _ => rfl)
    (fun x hx => SszListU8.hash_tree_root.spec inst h hl x hx)

include hl in
/-- **`SszList<SszList<u8, M>, N>`** (for example `transactions`): EthLib's for
`List[ByteList[M], N]`. It requires the invariants of both types: the list has at most `N`
items, and no item has more than `M` bytes. -/
theorem SszListByteList.hash_tree_root.spec {M N : Std.Usize}
    (l : libssz_types.list.SszList (libssz_types.list.SszList Std.U8 M) N)
    (hlen : l.length ≤ N.val) (hitems : ∀ x ∈ l.val, x.length ≤ M.val) :
    libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (libssz_types.list.SszList.Insts.Libssz_merkleHashTreeRoot M
        libssz_types.U8.Insts.Libssz_merkleHashTreeRoot libssz_types.U8.Insts.LibsszEncodeSszEncode)
      (libssz_types.list.SszList.Insts.LibsszEncodeSszEncode M
        libssz_types.U8.Insts.LibsszEncodeSszEncode) inst l h ⦃ r =>
      hashTreeRoot (.list (.byteList M.val) N.val) (.seq (l.val.map fun x => .bytes (bytes x.val)))
        = .ok (bytes r.val) ⦄ :=
  SszList.composite_root inst h hl _ _ rfl (.byteList M.val) rfl _ _ 0 (SszListU8.rows inst h hl)
    l hlen hitems

end Bytes

/-! ## `uint256` stored as 32 bytes -/

theorem leValue_lt (l : List Std.U8) : leValue UScalar.val l < 256 ^ l.length := by
  induction l with
  | nil => simp [leValue]
  | cons b rest ih =>
    have hb : b.val < 256 := by have := b.hBounds; scalar_tac
    simp only [leValue, List.foldr_cons, List.length_cons] at *
    rw [Nat.pow_succ]
    nlinarith

/-- The little-endian bytes of a number read from those same bytes. -/
theorem uintBytes_leValue (l : List Std.U8) : uintBytes l.length (leValue UScalar.val l) = bytes l := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    have hb : b.val < 256 := by have := b.hBounds; scalar_tac
    rw [List.length_cons, uintBytes_succ, Libssz.Proofs.bytes_cons]
    have hv : leValue UScalar.val (b :: rest) = b.val + 256 * leValue UScalar.val rest := rfl
    rw [hv, show (b.val + 256 * leValue UScalar.val rest) / 256 = leValue UScalar.val rest by omega,
      ih, show (b.val + 256 * leValue UScalar.val rest) % 256 = b.val by omega]
    congr 3
    apply UInt8.toNat_inj.mp
    simp [Nat.mod_eq_of_lt hb]

/-- **The root of a `uint256`** that Rust stores as its 32 little-endian bytes (like
`base_fee_per_gas`): those same bytes. -/
theorem hashTreeRoot_uint256 (a : Std.Array Std.U8 32#usize) :
    hashTreeRoot Desc.uint256 (.uint (leValue UScalar.val a.val)) = .ok (bytes a.val) := by
  have hl : a.val.length = 32 := by simp
  have hser : serialize Desc.uint256 (.uint (leValue UScalar.val a.val)) = .ok (bytes a.val) := by
    have hlt := leValue_lt a.val
    rw [hl] at hlt
    have hfit : uintFits 32 (leValue UScalar.val a.val) = true := by
      simp only [uintFits, beq_iff_eq, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by simpa using hlt)
    simp only [serialize, Desc.uint256, hfit, ↓reduceIte]
    have he := uintBytes_leValue a.val
    rw [hl] at he
    rw [he]
  rw [hashTreeRoot_leaf Desc.uint256 _ (bytes a.val) rfl rfl hser (by simp) (by simp)]
  simp

/-! ## `Withdrawal` and `ExecutionPayload` -/

def wdNames : List String := ["index", "validator_index", "address", "amount"]
def wdFields : List Desc := [Desc.uint64, Desc.uint64, .byteVector 20, Desc.uint64]
def wdV (x : libssz_types.verif_example.Withdrawal) : Value :=
  .seq [.uint x.index.val, .uint x.validator_index.val, .bytes (bytes x.address.val),
    .uint x.amount.val]

def epNames : List String :=
  ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom", "prev_randao",
    "block_number", "gas_limit", "gas_used", "timestamp", "extra_data", "base_fee_per_gas",
    "block_hash", "transactions", "withdrawals"]
def epFields : List Desc :=
  [.byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32, .byteVector 256,
    .byteVector 32, Desc.uint64, Desc.uint64, Desc.uint64, Desc.uint64, .byteList 32,
    Desc.uint256, .byteVector 32, .list (.byteList 1073741824) 1048576,
    .list (.container wdNames wdFields) 16]
def epV (x : libssz_types.verif_example.ExecutionPayload) : Value :=
  .seq [.bytes (bytes x.parent_hash.val), .bytes (bytes x.fee_recipient.val),
    .bytes (bytes x.state_root.val), .bytes (bytes x.receipts_root.val),
    .bytes (bytes x.logs_bloom.val), .bytes (bytes x.prev_randao.val),
    .uint x.block_number.val, .uint x.gas_limit.val, .uint x.gas_used.val, .uint x.timestamp.val,
    .bytes (bytes x.extra_data.val), .uint (leValue UScalar.val x.base_fee_per_gas.val),
    .bytes (bytes x.block_hash.val),
    .seq (x.transactions.val.map fun t => .bytes (bytes t.val)),
    .seq (x.withdrawals.val.map wdV)]

section Payload

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

include hl in
/-- **`Withdrawal`**: the `hash_tree_root` that the macro generates is EthLib's. -/
theorem Withdrawal.hash_tree_root.spec (x : libssz_types.verif_example.Withdrawal) :
    libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container wdNames wdFields) (wdV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with U64.hash_tree_root.spec inst h x.index as ⟨ a0, h0 ⟩
  step with U64.hash_tree_root.spec inst h x.validator_index as ⟨ a1, h1 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.address as ⟨ a2, h2 ⟩
  step with U64.hash_tree_root.spec inst h x.amount as ⟨ a3, h3 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold wdV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
    (by simp only [wdFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind,
      Except.bind])]
  have hc : chunksOf (Array.make 4#usize [a0, a1, a2, a3] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] := by
    simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show wdFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val]).size
    from rfl, merkleizeBounded_some_self, ← hr]

include hl in
/-- **The rows of `Withdrawal`**: the roots of its 4 fields, the bottom level
of its tree. -/
theorem Withdrawal.rows :
    Rows inst h libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot (.container wdNames wdFields) wdV
      (fun x => True) 2 where
  small := by omega
  width := ⟨ 4#usize, rfl, rfl ⟩
  row x row hgood hlen := by
    simp only [libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot]
    unfold libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot.hash_tree_root_row
    simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
      libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root]
    have hlen' : row.val.length = 4 := hlen
    obtain ⟨ b0, b1, b2, b3, hrowv ⟩ := list_len4 row.val hlen'
    step with U64.hash_tree_root.spec inst h x.index as ⟨ a0, h0 ⟩
    step as ⟨ row1, hrow1 ⟩
    have hl1 : row1.length = 4 := by
      rw [hrow1]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hlen
    step with U64.hash_tree_root.spec inst h x.validator_index as ⟨ a1, h1 ⟩
    step as ⟨ row2, hrow2 ⟩
    have hl2 : row2.length = 4 := by
      rw [hrow2]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
    step with ArrayU8N.hash_tree_root.spec inst h hl x.address as ⟨ a2, h2 ⟩
    step as ⟨ row3, hrow3 ⟩
    have hl3 : row3.length = 4 := by
      rw [hrow3]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl2
    step with U64.hash_tree_root.spec inst h x.amount as ⟨ a3, h3 ⟩
    step as ⟨ row4, hrow4 ⟩
    have hl4 : row4.length = 4 := by
      rw [hrow4]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl3
    have hrv : row4.val = [a0, a1, a2, a3] := by
      rw [hrow4, hrow3, hrow2, hrow1]
      simp only [Slice.set_val_eq, hrowv]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    unfold RowRoot wdV
    rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val] rfl
      (by simp only [wdFields] at *; simp [h0, h1, h2, h3, Pure.pure, Except.pure, Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [a0, a1, a2, a3] 2 (by simp [depthFor])

include hl in
/-- **`ExecutionPayload` (capella)**: the `hash_tree_root` that the macro generates is EthLib's,
with the consensus-specs types (`base_fee_per_gas` is a `uint256`). It requires the
invariants of its lists and vectors. -/
theorem ExecutionPayload.hash_tree_root.spec (x : libssz_types.verif_example.ExecutionPayload)
    (hlb : x.logs_bloom.length = 256) (hed : x.extra_data.length ≤ 32)
    (htx : x.transactions.length ≤ 1048576)
    (htxs : ∀ t ∈ x.transactions.val, t.length ≤ 1073741824)
    (hwd : x.withdrawals.length ≤ 16) :
    libssz_types.verif_example.ExecutionPayload.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container epNames epFields) (epV x) = .ok (bytes r.val) ⦄ := by
  unfold libssz_types.verif_example.ExecutionPayload.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
  simp only [libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root,
    libssz_types.libssz_merkle.merkleize_in_place]
  step with ArrayU8N.hash_tree_root.spec inst h hl x.parent_hash as ⟨ a0, h0 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.fee_recipient as ⟨ a1, h1 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.state_root as ⟨ a2, h2 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.receipts_root as ⟨ a3, h3 ⟩
  step with SszVectorU8.hash_tree_root.spec inst h hl x.logs_bloom hlb as ⟨ a4, h4 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.prev_randao as ⟨ a5, h5 ⟩
  step with U64.hash_tree_root.spec inst h x.block_number as ⟨ a6, h6 ⟩
  step with U64.hash_tree_root.spec inst h x.gas_limit as ⟨ a7, h7 ⟩
  step with U64.hash_tree_root.spec inst h x.gas_used as ⟨ a8, h8 ⟩
  step with U64.hash_tree_root.spec inst h x.timestamp as ⟨ a9, h9 ⟩
  step with SszListU8.hash_tree_root.spec inst h hl x.extra_data hed as ⟨ a10, h10 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.base_fee_per_gas as ⟨ a11, h11 ⟩
  step with ArrayU8N.hash_tree_root.spec inst h hl x.block_hash as ⟨ a12, h12 ⟩
  step with SszListByteList.hash_tree_root.spec inst h hl x.transactions htx htxs as ⟨ a13, h13 ⟩
  step with SszList.composite_root inst h hl
    libssz_types.verif_example.Withdrawal.Insts.Libssz_merkleHashTreeRoot
    libssz_types.verif_example.Withdrawal.Insts.LibsszEncodeSszEncode rfl
    (.container wdNames wdFields) rfl wdV _ _ (Withdrawal.rows inst h hl)
    x.withdrawals hwd (fun _ _ => trivial) as ⟨ a14, h14 ⟩
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  have h11' : hashTreeRoot Desc.uint256 (.uint (leValue UScalar.val x.base_fee_per_gas.val)) =
      .ok (bytes a11.val) := by
    rw [hashTreeRoot_uint256]
    rw [hashTreeRoot_bytes32 _ (bytes_size32 _)] at h11
    exact h11
  unfold epV
  rw [hashTreeRoot_container _ _ _ [bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val,
    bytes a4.val, bytes a5.val, bytes a6.val, bytes a7.val, bytes a8.val, bytes a9.val,
    bytes a10.val, bytes a11.val, bytes a12.val, bytes a13.val, bytes a14.val] rfl
    (by simp only [epFields] at *; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11', h12,
      h13, h14, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make 15#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14] (by simp)).to_slice.val =
      #[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val, bytes a4.val, bytes a5.val,
        bytes a6.val, bytes a7.val, bytes a8.val, bytes a9.val, bytes a10.val, bytes a11.val,
        bytes a12.val, bytes a13.val, bytes a14.val] := by
    simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show epFields.length = (#[bytes a0.val, bytes a1.val, bytes a2.val, bytes a3.val,
    bytes a4.val, bytes a5.val, bytes a6.val, bytes a7.val, bytes a8.val, bytes a9.val,
    bytes a10.val, bytes a11.val, bytes a12.val, bytes a13.val, bytes a14.val]).size from rfl,
    merkleizeBounded_some_self, ← hr]

end Payload

end Libssz.SszTypes
