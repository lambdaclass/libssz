module
import Libssz.Merkle.Code.Funs
import EthLib.Serialization.Ssz.Merkle.Tree

/-!
# Differential test of the SHA-NI core: the intrinsic models and the Aeneas model

The proofs in `Libssz/Merkle/Proofs/` are about the handwritten models in
`Libssz/Merkle/Intrinsics.lean`, not about the processor. This executable runs those
models (through `FunsExternal.lean`, so the glue for immediates and `i32`s is exercised too)
and the Aeneas model of `shani.rs`. The Rust test (`../difftest-merkle`) sends it inputs and
compares each answer with what the real instruction gives on the processor and with the
compiled Rust code.

Reads one operation per line from stdin and answers one line for each:

* `add A B`, `msg1 A B`, `msg2 A B`, `rnds2 A B K`, `shuffle <imm> A`, `alignr <imm> A B`:
  the resulting vector;
* `set E3 E2 E1 E0` (four `i32`s, in hex): the vector; `extract <imm> A`: the `i32`, in hex;
* `pair A B`: `hash_pair` from the Aeneas model and, separated by a tab, EthLib's
  `combine`;
* `pairs2 A0 B0 A1 B1`: the two nodes of `hash_pairs_x2`, separated by a comma;
* `pairs4 A0 B0 A1 B1 A2 B2 A3 B3`: the four nodes of `hash_pairs_x4`, separated by commas;
* `layer <0|1> ZERO BELOW LEVEL`: the `level` that `hash_layer` leaves (`-` if empty), or
  `PANIC`.

A vector is 16 bytes in hex as laid out in memory: lane 0 first, each lane little-endian.
A node is 32 bytes in hex; `BELOW` and `LEVEL` are concatenated nodes, or `-`.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Merkle (M128)

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

def toHex (l : List Nat) : String :=
  String.join (l.map fun b => String.ofList [hexDigit (b / 16), hexDigit (b % 16)])

def parseHex (s : String) : Option (List Nat) :=
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | a :: b :: rest => do
      let x ← digit a; let y ← digit b; let r ← go rest; some ((16 * x + y) :: r)
    | [_] => none
  go s.toList

def parseVec (s : String) : Option M128 := do
  let b ← parseHex s
  if b.length = 16 then
    some (Vector.ofFn fun l : Fin 4 => UInt32.ofNat
      (b[4 * l.val]! + 2 ^ 8 * b[4 * l.val + 1]! + 2 ^ 16 * b[4 * l.val + 2]! +
        2 ^ 24 * b[4 * l.val + 3]!))
  else none

def showVec (v : M128) : String :=
  toHex (v.toList.flatMap fun w =>
    [w.toNat % 256, w.toNat / 2 ^ 8 % 256, w.toNat / 2 ^ 16 % 256, w.toNat / 2 ^ 24])

/-- An `i32`: eight hex digits, most significant first. -/
def parseI32 (s : String) : Option Std.I32 := do
  let b ← parseHex s
  if b.length = 4 then
    some ⟨BitVec.ofNat 32 (2 ^ 24 * b[0]! + 2 ^ 16 * b[1]! + 2 ^ 8 * b[2]! + b[3]!)⟩
  else none

def showI32 (x : Std.I32) : String :=
  let n := x.bv.toNat
  toHex [n / 2 ^ 24, n / 2 ^ 16 % 256, n / 2 ^ 8 % 256, n % 256]

def parseImm (s : String) : Option Std.I32 := do
  let n ← s.toNat?
  some ⟨BitVec.ofNat 32 n⟩

abbrev Node := Array Std.U8 32#usize

def toNode (b : List Nat) : Option Node :=
  let l : List Std.U8 := b.map fun n => ⟨BitVec.ofNat 8 n⟩
  if h : l.length = (32#usize).val then some (Array.from l h) else none

def parseNode (s : String) : Option Node := do toNode (← parseHex s)

def showNode (n : Node) : String := toHex (n.val.map (·.val))

partial def chunks32 (b : List Nat) : List (List Nat) :=
  if b.isEmpty then [] else b.take 32 :: chunks32 (b.drop 32)

def parseNodes (s : String) : Option (Slice Node) := do
  let b ← if s = "-" then some [] else parseHex s
  let l ← (chunks32 b).mapM toNode
  if h : l.length ≤ Usize.max then some (Slice.from l h) else none

def showNodes (s : Slice Node) : String :=
  if s.val.isEmpty then "-" else String.join (s.val.map showNode)

def run {α : Type} (r : Result α) (f : α → String) : String :=
  match r.match with
  | .ok v => f v
  | .vis _ _ => "PANIC"
  | .div => "DIV"

/-- EthLib's `combine` on two nodes. -/
def spec (a b : Node) : String :=
  let bytes (n : Node) : EthLib.Serialization.Ssz.Bytes :=
    (n.val.map fun x => UInt8.ofNat x.val).toArray
  toHex ((EthLib.Serialization.Ssz.combine (bytes a) (bytes b)).toList.map (·.toNat))

def answer (line : String) : Option String :=
  match line.splitOn " " with
  | ["add", a, b] => do
    some (run (core.core_arch.x86.sse2._mm_add_epi32 (← parseVec a) (← parseVec b)) showVec)
  | ["msg1", a, b] => do
    some (run (core.core_arch.x86.sha._mm_sha256msg1_epu32 (← parseVec a) (← parseVec b))
      showVec)
  | ["msg2", a, b] => do
    some (run (core.core_arch.x86.sha._mm_sha256msg2_epu32 (← parseVec a) (← parseVec b))
      showVec)
  | ["rnds2", a, b, k] => do
    some (run (core.core_arch.x86.sha._mm_sha256rnds2_epu32 (← parseVec a) (← parseVec b)
      (← parseVec k)) showVec)
  | ["shuffle", imm, a] => do
    some (run (core.core_arch.x86.sse2._mm_shuffle_epi32 (← parseImm imm) (← parseVec a))
      showVec)
  | ["alignr", imm, a, b] => do
    some (run (core.core_arch.x86.ssse3._mm_alignr_epi8 (← parseImm imm) (← parseVec a)
      (← parseVec b)) showVec)
  | ["extract", imm, a] => do
    some (run (core.core_arch.x86.sse41._mm_extract_epi32 (← parseImm imm) (← parseVec a))
      showI32)
  | ["set", e3, e2, e1, e0] => do
    some (run (core.core_arch.x86.sse2._mm_set_epi32 (← parseI32 e3) (← parseI32 e2)
      (← parseI32 e1) (← parseI32 e0)) showVec)
  | ["pair", a, b] => do
    let a ← parseNode a
    let b ← parseNode b
    some (run (shani.hash_pair a b) showNode ++ "\t" ++ spec a b)
  | ["pairs2", a0, b0, a1, b1] => do
    some (run (shani.hash_pairs_x2 (← parseNode a0) (← parseNode b0) (← parseNode a1)
      (← parseNode b1)) fun (x, y) => showNode x ++ "," ++ showNode y)
  | ["pairs4", a0, b0, a1, b1, a2, b2, a3, b3] => do
    some (run (shani.hash_pairs_x4 (← parseNode a0) (← parseNode b0) (← parseNode a1)
      (← parseNode b1) (← parseNode a2) (← parseNode b2) (← parseNode a3) (← parseNode b3))
      fun (x, y, z, w) => showNode x ++ "," ++ showNode y ++ "," ++ showNode z ++ "," ++
        showNode w)
  | ["layer", inPlace, zero, below, level] => do
    let inPlace ← if inPlace = "1" then some true else if inPlace = "0" then some false else none
    some (run (shani.hash_layer (← parseNodes below) (← parseNodes level) inPlace
      (← parseNode zero)) showNodes)
  | _ => none

public def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := String.ofList (line.toList.filter fun ch => ch ≠ '\n' ∧ ch ≠ '\r')
    stdout.putStrLn ((answer line).getD "BAD_INPUT")
  stdout.flush
