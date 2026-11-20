module
public import Libssz.Code.Funs
public import Libssz.Proofs.Bytes
@[expose] public section

/-!
# Error bridge: libssz ↔ EthLib

Relates the libssz error type, `DecodeError`, to the EthLib one. `ErrMatch` and `Agrees`,
together with `byte`/`bytes` (`Libssz/Proofs/Bytes.lean`) and the statements in `Bool.lean`
and `Uint.lean`, are what one has to read to believe the result: if they were wrong, the
theorems would say something else.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz

namespace Libssz.Proofs

open Libssz.Proofs

/-- Which libssz error corresponds to which EthLib error.

The two error types are not required to be equal (they are not); instead, every Rust failure
must be the failure EthLib describes, with the same data. Constructors are added as more types
are covered. -/
inductive ErrMatch : libssz_codec.error.DecodeError → Err → Prop
  /-- Wrong length for a fixed-size type. -/
  | fixedLength (expected got : Std.Usize) :
      ErrMatch (.InvalidFixedLength expected got) (.scope expected.val got.val)
  /-- A `bool` that is neither `0` nor `1`. -/
  | booleanByte (b : Std.U8) :
      ErrMatch (.InvalidBooleanByte b) (.notABit b.val)
  /-- A list of `w`-byte elements whose length is not a multiple of `w`. -/
  | undivided (w got : Std.Usize) :
      ErrMatch (.InvalidByteLength w got) (.scopeUndivided got.val w.val)
  /-- A list with more elements than its limit. -/
  | overLimit (max count : Std.Usize) :
      ErrMatch (.InvalidByteLength max count) (.overLimit max.val count.val)
  /-- A list of variable-size items shorter than 4 bytes: not even the first offset fits. -/
  | tooSmall (got : Std.Usize) :
      ErrMatch (.InvalidByteLength 4#usize got) (.scopeTooSmall 4 got.val)
  /-- A variable-size container smaller than its fixed part (`ContainerDecoder::new`). -/
  | fixedPart (w got : Std.Usize) :
      ErrMatch (.InvalidByteLength w got) (.scopeTooSmall w.val got.val)
  /-- In a container, the first offset is not the length of the fixed part. -/
  | firstOffsetAt (e g : Std.Usize) :
      ErrMatch (.InvalidFirstOffset e g) (.firstOffset e.val g.val)
  /-- **The first offset is invalid** (not a multiple of 4, or less than 4). The two sides
  check in a different order, so we only require that both reject because of the first offset. -/
  | firstOffset (e g : Std.Usize) (e' : Err) (h : e' = .offsetBelowTable ∨ e' = .offsetUnaligned) :
      ErrMatch (.InvalidFirstOffset e g) e'
  /-- **The offset table is invalid** (not increasing, or past the length). libssz checks
  each offset against the length as it reads it; EthLib only checks that they increase and
  that the last one is not past the end. They accept the same tables, but on a bad one they may
  reject with different errors, so we only require that both reject because of the table. -/
  | offsetTable (e : libssz_codec.error.DecodeError) (e' : Err)
      (he : e = .OffsetsAreNotMonotonicallyIncreasing ∨ ∃ o l, e = .OffsetOutOfBounds o l)
      (he' : e' = .offsetUnordered ∨ e' = .offsetPastScope) :
      ErrMatch e e'
  /-- A bitvector with a padding bit set (`SszBitvector`). -/
  | paddingBits : ErrMatch .ExcessBitsNotZero .paddingBits
  /-- A bitlist without a delimiter: empty, or with the last byte zero (`SszBitlist`). EthLib
  distinguishes three cases (empty, all zero, trailing zeros); libssz merges them into one.
  Only those three EthLib errors are about bitlists, so the other types are unchanged. -/
  | noDelimiter (e' : Err) (h : e' = .emptyEncoding ∨ e' = .noDelimiter ∨ e' = .trailingZeros) :
      ErrMatch .MissingDelimiterBit e'

/-- The result of a Rust decode matches the EthLib one: both accept and give the same value,
or both reject with corresponding errors. -/
def Agrees {α : Type} (toV : α → Value) :
    core.result.Result α libssz_codec.error.DecodeError → Except Err Value → Prop
  | .Ok a, .ok v => toV a = v
  | .Err e, .error e' => ErrMatch e e'
  | _, _ => False

end Libssz.Proofs
