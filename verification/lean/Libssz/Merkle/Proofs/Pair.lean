module
public import Libssz.Merkle.Proofs.Rounds
public import EthLib.Cryptography.Proofs.Hash.Sha256
@[expose] public section

/-!
# SHA-256 of a 64-byte message

What EthLib's `Sha256.hash` does with the two nodes of a pair (64 bytes): two blocks. The
first is the two nodes; the second is always the same, the padding of a 512-bit message. No
Rust code appears here.
-/

namespace Libssz.Merkle

open EthLib.Cryptography.Hash.Sha256

/-! ## Words and blocks over byte lists -/

/-- The big-endian word that starts at byte `j`. -/
def wordAt (l : List UInt8) (j : Nat) : UInt32 :=
  big32 (l[j]?.getD 0) (l[j + 1]?.getD 0) (l[j + 2]?.getD 0) (l[j + 3]?.getD 0)

/-- The 16 words of the block that starts at byte `start`. -/
def windowAt (l : List UInt8) (start : Nat) : Window :=
  ⟨wordAt l start, wordAt l (start + 4), wordAt l (start + 8), wordAt l (start + 12),
    wordAt l (start + 16), wordAt l (start + 20), wordAt l (start + 24), wordAt l (start + 28),
    wordAt l (start + 32), wordAt l (start + 36), wordAt l (start + 40), wordAt l (start + 44),
    wordAt l (start + 48), wordAt l (start + 52), wordAt l (start + 56), wordAt l (start + 60)⟩

theorem wordAt_append_left (x t : List UInt8) (j : Nat) (h : j + 4 ≤ x.length) :
    wordAt (x ++ t) j = wordAt x j := by
  simp only [wordAt]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
    List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

theorem wordAt_append_right (x t : List UInt8) (j : Nat) :
    wordAt (x ++ t) (x.length + j) = wordAt t j := by
  simp only [wordAt]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
  congr <;> omega

theorem windowAt_append_left (x t : List UInt8) (h : 64 ≤ x.length) :
    windowAt (x ++ t) 0 = windowAt x 0 := by
  have hw : ∀ j, j + 4 ≤ 64 → wordAt (x ++ t) j = wordAt x j :=
    fun j hj => wordAt_append_left x t j (by omega)
  simp (disch := omega) only [windowAt, hw]

theorem windowAt_append_right (x t : List UInt8) :
    windowAt (x ++ t) x.length = windowAt t 0 := by
  have h0 := wordAt_append_right x t 0
  rw [Nat.add_zero] at h0
  simp only [windowAt, wordAt_append_right, h0, Nat.zero_add]

theorem ofBlock_eq (bytes : ByteArray) (start : Nat) (whole : start + 64 ≤ bytes.size) :
    Window.ofBlock bytes start whole = windowAt bytes.data.toList start := by
  have hs : bytes.data.size = bytes.size := rfl
  have get : ∀ (i : Nat) (h : i < bytes.size), bytes[i] = bytes.data.toList[i]?.getD 0 := by
    intro i h
    rw [List.getElem?_eq_getElem (by simpa using h)]
    rfl
  simp only [Window.ofBlock, windowAt, wordAt, get]
  rfl

/-! ## The padding -/

/-- What `pad` appends to a 64-byte message: `0x80`, 55 zeros and the length in bits (512) in
eight big-endian bytes. -/
def padTail : List UInt8 := 0x80 :: (List.replicate 55 0 ++ [0, 0, 0, 0, 0, 0, 2, 0])

theorem pad_toList (m : ByteArray) (hm : m.size = 64) :
    (pad m).data.toList = m.data.toList ++ padTail := by
  simp only [pad, hm, ByteArray.data_append, Array.toList_append, List.append_assoc]
  rfl

/-- The second block: the padding block. -/
def padW0 : Window := ⟨0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512⟩

theorem windowAt_padTail : windowAt padTail 0 = padW0 := by
  simp only [windowAt, padW0, Window.mk.injEq]
  decide

/-- The schedule of the padding block, four words at a time. -/
def padW : Nat → Window
  | 0 => padW0
  | q + 1 => next4 (padW q)

/-! ## The two blocks -/

/-- The hash value of a 64-byte message, given the 16 words of its first block. -/
def pairState (w : Window) : State :=
  let h1 := feed initial (rounds (Kfrom 0) w initial)
  feed h1 (rounds (Kfrom 0) (padW 0) h1)

theorem chain_two
    (step : State → (bytes : ByteArray) → (start : Nat) → start + 64 ≤ bytes.size → State)
    (bytes : ByteArray) (count : Nat) (whole : 0 + 64 * count ≤ bytes.size) (s : State)
    (hc : count = 2) :
    chain step bytes count 0 whole s
      = step (step s bytes 0 (by omega)) bytes 64 (by omega) := by
  subst hc
  rfl

/-- **SHA-256 of 64 bytes**, block by block. -/
theorem hash_block (m : ByteArray) (hm : m.size = 64) :
    EthLib.Cryptography.Hash.Sha256.hash m = digest (pairState (windowAt m.data.toList 0)) := by
  have hsize : (pad m).size = 128 := by rw [pad_size, hm]; rfl
  have hlen : m.data.toList.length = 64 := by simpa using hm
  show digest (chain compress (pad m) ((pad m).size / 64) 0 _ initial) = _
  rw [chain_two compress (pad m) _ _ _ (by rw [hsize])]
  simp only [compress_eq, ofBlock_eq, pad_toList m hm]
  rw [windowAt_append_left _ _ (by omega)]
  have h2 : windowAt (m.data.toList ++ padTail) 64 = padW0 := by
    rw [← hlen, windowAt_append_right, windowAt_padTail]
  rw [h2]
  rfl

end Libssz.Merkle
