module
import Libssz.Code.Funs
import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# Differential test: the Lean model of libssz, executed

Reads lines `<type> <hex>` from stdin and, for each one, prints a line with four tab-separated
fields:

1. the decode of the **Aeneas model** (`from_ssz_bytes`), in Rust's `Debug` format:
   `Ok(5)`, `Ok([1, 2])`, `Err(InvalidFixedLength { expected: 8, got: 3 })`, or `PANIC`;
2. if the decode gave `Ok(v)`, the model's encoding, in hex; otherwise `-`. The encoding is
   computed in two ways, `to_ssz` and `ssz_append` onto a buffer that already holds three
   bytes, and both must agree (otherwise the field says so and the test fails);
3. the decode of **EthLib** (`Ssz.deserialize`), in the same format. EthLib errors that
   correspond to a libssz error (`ErrMatch`) are written as the libssz one; the rest as
   `Err(EthLib:<code>)`;
4. if the EthLib decode gave `.ok v`, `Ssz.serialize` of `v`, in hex; otherwise `-`.

The Rust test (`../difftest`) generates the inputs, runs this executable and compares each
field with what the compiled Rust code gives.
-/

open Aeneas Aeneas.Std Result
open libssz
open EthLib.Serialization.Ssz

/-- A libssz type with its model instances, how to print its values, and its EthLib
`Desc`. -/
structure Codec where
  T : Type
  dec : decode.SszDecode T
  enc : encode.SszEncode T
  fmt : T → String
  desc : Desc
  /-- How to print the EthLib value (by default, as a list). -/
  showV : Option (Value → String) := none

def showList {α : Type} (f : α → String) (l : List α) : String :=
  "[" ++ ", ".intercalate (l.map f) ++ "]"

partial def showValue : Value → String
  | .bool b => toString b
  | .uint n => toString n
  | .bytes d => showList (fun b : UInt8 => toString b.toNat) d.toList
  | .bits d => showList toString d.toList
  | .seq vs => showList showValue vs
  | .union s v => s!"Union({s}, {showValue v})"

def u (ty : UScalarTy) (x : UScalar ty) : String := toString x.val

def bigLimit : Nat := 2 ^ 64

def boolC : Codec := { T := Bool, dec := Bool.Insts.LibsszDecodeSszDecode, enc := Bool.Insts.LibsszEncodeSszEncode, fmt := toString, desc := .bool }
def u8C : Codec := { T := Std.U8, dec := U8.Insts.LibsszDecodeSszDecode, enc := U8.Insts.LibsszEncodeSszEncode, fmt := u _, desc := .uint 1 }
def u16C : Codec := { T := Std.U16, dec := U16.Insts.LibsszDecodeSszDecode, enc := U16.Insts.LibsszEncodeSszEncode, fmt := u _, desc := .uint 2 }
def u32C : Codec := { T := Std.U32, dec := U32.Insts.LibsszDecodeSszDecode, enc := U32.Insts.LibsszEncodeSszEncode, fmt := u _, desc := .uint 4 }
def u64C : Codec := { T := Std.U64, dec := U64.Insts.LibsszDecodeSszDecode, enc := U64.Insts.LibsszEncodeSszEncode, fmt := u _, desc := .uint 8 }
def u128C : Codec := { T := Std.U128, dec := U128.Insts.LibsszDecodeSszDecode, enc := U128.Insts.LibsszEncodeSszEncode, fmt := u _, desc := .uint 16 }

def bytesC (n : Nat) : Codec :=
  let N : Std.Usize := ⟨BitVec.ofNat _ n⟩
  { T := Array Std.U8 N, dec := ArrayU8N.Insts.LibsszDecodeSszDecode N,
    enc := ArrayU8N.Insts.LibsszEncodeSszEncode N, fmt := fun a => showList (u _) a.val,
    desc := .byteVector n }

/-- `Vec<T>`, which in EthLib is a list with no practical limit (libssz sets none). -/
def vecC (c : Codec) : Codec :=
  { T := alloc.vec.Vec c.T, dec := alloc.vec.Vec.Insts.LibsszDecodeSszDecode c.dec,
    enc := alloc.vec.Vec.Insts.LibsszEncodeSszEncode c.enc, fmt := fun v => showList c.fmt v.val,
    desc := .list c.desc bigLimit }

/-- The example container. Rust prints it as the tuple `(a, b, c, d)`. -/
def exC : Codec :=
  { T := verif_example.Example, dec := verif_example.Example.Insts.LibsszDecodeSszDecode,
    enc := verif_example.Example.Insts.LibsszEncodeSszEncode,
    fmt := fun x => s!"({x.a.val}, {showList (u _) x.b.val}, {x.c}, {showList (u _) x.d.val})",
    desc := .container ["a", "b", "c", "d"] [.uint 8, .list (.uint 1) bigLimit, .bool,
      .list (.uint 2) bigLimit],
    showV := some fun
      | .seq [a, b, c, d] => s!"({showValue a}, {showValue b}, {showValue c}, {showValue d})"
      | v => showValue v }

/-! Fixed-size consensus-layer containers. Rust prints them as tuples, with nested ones also
as tuples. -/

/-- An EthLib fixed-size container value as a tuple (they contain no lists). -/
partial def tupV : Value → String
  | .seq vs => "(" ++ ", ".intercalate (vs.map tupV) ++ ")"
  | v => showValue v

def arr {N : Std.Usize} (a : Array Std.U8 N) : String := showList (u _) a.val

def fmtCp (x : verif_example.Checkpoint) : String := s!"({x.epoch.val}, {arr x.root})"

def cpDesc : Desc := .container ["epoch", "root"] [.uint 8, .byteVector 32]

def cpC : Codec :=
  { T := verif_example.Checkpoint, dec := verif_example.Checkpoint.Insts.LibsszDecodeSszDecode,
    enc := verif_example.Checkpoint.Insts.LibsszEncodeSszEncode, fmt := fmtCp, desc := cpDesc,
    showV := some tupV }

def forkC : Codec :=
  { T := verif_example.Fork, dec := verif_example.Fork.Insts.LibsszDecodeSszDecode,
    enc := verif_example.Fork.Insts.LibsszEncodeSszEncode,
    fmt := fun x => s!"({arr x.previous_version}, {arr x.current_version}, {x.epoch.val})",
    desc := .container ["previous_version", "current_version", "epoch"]
      [.byteVector 4, .byteVector 4, .uint 8],
    showV := some tupV }

def bbhC : Codec :=
  { T := verif_example.BeaconBlockHeader,
    dec := verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode,
    enc := verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode,
    fmt := fun x => s!"({x.slot.val}, {x.proposer_index.val}, {arr x.parent_root}, " ++
      s!"{arr x.state_root}, {arr x.body_root})",
    desc := .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
      [.uint 8, .uint 8, .byteVector 32, .byteVector 32, .byteVector 32],
    showV := some tupV }

def valC : Codec :=
  { T := verif_example.Validator, dec := verif_example.Validator.Insts.LibsszDecodeSszDecode,
    enc := verif_example.Validator.Insts.LibsszEncodeSszEncode,
    fmt := fun x => s!"({arr x.pubkey}, {arr x.withdrawal_credentials}, " ++
      s!"{x.effective_balance.val}, {x.slashed}, {x.activation_eligibility_epoch.val}, " ++
      s!"{x.activation_epoch.val}, {x.exit_epoch.val}, {x.withdrawable_epoch.val})",
    desc := .container ["pubkey", "withdrawal_credentials", "effective_balance", "slashed",
        "activation_eligibility_epoch", "activation_epoch", "exit_epoch", "withdrawable_epoch"]
      [.byteVector 48, .byteVector 32, .uint 8, .bool, .uint 8, .uint 8, .uint 8, .uint 8],
    showV := some tupV }

def adC : Codec :=
  { T := verif_example.AttestationData,
    dec := verif_example.AttestationData.Insts.LibsszDecodeSszDecode,
    enc := verif_example.AttestationData.Insts.LibsszEncodeSszEncode,
    fmt := fun x => s!"({x.slot.val}, {x.index.val}, {arr x.beacon_block_root}, " ++
      s!"{fmtCp x.source}, {fmtCp x.target})",
    desc := .container ["slot", "index", "beacon_block_root", "source", "target"]
      [.uint 8, .uint 8, .byteVector 32, cpDesc, cpDesc],
    showV := some tupV }

/-- `Vec<S>` with `S` a fixed-size container: a list of tuples. -/
def vecTupC (c : Codec) : Codec :=
  { vecC c with showV := some fun
      | .seq vs => showList tupV vs
      | v => showValue v }

def codecs : List (String × Codec) :=
  [("bool", boolC), ("u8", u8C), ("u16", u16C), ("u32", u32C), ("u64", u64C), ("u128", u128C),
   ("b4", bytesC 4),
   ("b32", bytesC 32),
   ("vbool", vecC boolC), ("vu8", vecC u8C), ("vu16", vecC u16C), ("vu32", vecC u32C),
   ("vu64", vecC u64C), ("vu128", vecC u128C), ("vb4", vecC (bytesC 4)),
   ("vb32", vecC (bytesC 32)), ("vb48", vecC (bytesC 48)),
   ("vvu8", vecC (vecC u8C)), ("vvu64", vecC (vecC u64C)), ("vvvu8", vecC (vecC (vecC u8C))),
   ("ex", exC), ("cp", cpC), ("fork", forkC), ("bbh", bbhC), ("val", valC), ("ad", adC),
   ("vcp", vecTupC cpC), ("vval", vecTupC valC), ("vad", vecTupC adC)]

/-! ## Rust `Debug` format -/

def showErr : error.DecodeError → String
  | .InvalidByteLength e g => s!"InvalidByteLength \{ expected: {e.val}, got: {g.val} }"
  | .InvalidFixedLength e g => s!"InvalidFixedLength \{ expected: {e.val}, got: {g.val} }"
  | .OffsetOutOfBounds o l => s!"OffsetOutOfBounds \{ offset: {o.val}, length: {l.val} }"
  | .OffsetsAreNotMonotonicallyIncreasing => "OffsetsAreNotMonotonicallyIncreasing"
  | .InvalidFirstOffset e g => s!"InvalidFirstOffset \{ expected: {e.val}, got: {g.val} }"
  | .InvalidBooleanByte b => s!"InvalidBooleanByte({b.val})"
  | .ExtraBytesRemaining n => s!"ExtraBytesRemaining({n.val})"
  | .EmptyInput => "EmptyInput"
  | .InvalidUnionSelector b => s!"InvalidUnionSelector({b.val})"
  | .ExcessBitsNotZero => "ExcessBitsNotZero"
  | .MissingDelimiterBit => "MissingDelimiterBit"
  | .AdditionalBytes e g => s!"AdditionalBytes \{ expected: {e.val}, got: {g.val} }"

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

/-! ## Aeneas model -/

/-- The bytes already in the buffer to which `model` appends the encoding. -/
def prefixBytes : List Std.U8 := [0x5a#u8, 0xa5#u8, 0x00#u8]

/-- Aeneas's `Result` is an interaction tree (`ITree`): `Result.match` says whether it ended
in `ok`, in a panic (`vis (.fail _)`), or diverges.

The encoding is computed with `to_ssz` and with `ssz_append` onto a buffer that already holds
`prefixBytes`: the latter must give those bytes followed by the former. -/
def model (c : Codec) (input : List Nat) : String × String :=
  let l : List Std.U8 := input.map fun b => ⟨BitVec.ofNat 8 b⟩
  let run (r : Result (alloc.vec.Vec Std.U8)) : String :=
    match r.match with
    | .ok buf => toHex (buf.val.map (·.val))
    | .vis _ _ => "PANIC"
    | .div => "DIV"
  if h : l.length ≤ Usize.max then
    if hp : prefixBytes.length ≤ Usize.max then
      match (c.dec.from_ssz_bytes (Slice.from l h)).match with
      | .ok (.Ok v) =>
        let t := run (c.enc.to_ssz v)
        let a := run (c.enc.ssz_append v (alloc.vec.Vec.from prefixBytes hp))
        let re :=
          if a == toHex (prefixBytes.map fun (b : Std.U8) => b.val) ++ t then t
          else s!"to_ssz={t} ssz_append={a}"
        (s!"Ok({c.fmt v})", re)
      | .ok (.Err e) => (s!"Err({showErr e})", "-")
      | .vis _ _ => ("PANIC", "-")
      | .div => ("DIV", "-")
    else ("TOO_LONG", "-")
  else ("TOO_LONG", "-")

/-! ## EthLib -/

def showEthErr : Err → String
  | .scope e g => s!"InvalidFixedLength \{ expected: {e}, got: {g} }"
  | .notABit b => s!"InvalidBooleanByte({b})"
  | e => s!"EthLib:{e.reason}"

def spec (c : Codec) (input : List Nat) : String × String :=
  match deserialize c.desc (input.map UInt8.ofNat).toArray with
  | .ok v =>
    let re := match serialize c.desc v with
      | .ok b => toHex (b.toList.map (·.toNat))
      | .error e => s!"Err({showEthErr e})"
    (s!"Ok({(c.showV.getD showValue) v})", re)
  | .error e => (s!"Err({showEthErr e})", "-")

public def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := String.ofList (line.toList.filter fun ch => ch ≠ '\n' ∧ ch ≠ '\r')
    match line.splitOn " " with
    | [ty, hex] =>
      match codecs.lookup ty, parseHex hex with
      | some c, some input =>
        let (md, me) := model c input
        let (sd, se) := spec c input
        stdout.putStrLn s!"{md}\t{me}\t{sd}\t{se}"
      | _, _ => stdout.putStrLn s!"BAD_INPUT\t-\t-\t-"
    | _ => stdout.putStrLn s!"BAD_INPUT\t-\t-\t-"
  stdout.flush
