/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Bool RLP complete-result controls

Library `EthConformance`. Two model, two exact encoding and 48 complete wire
outcomes retain every constructor, payload and diagnostic.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpBoolGuards
open STFSpec.Codec STFSpec.Codec.Rlp

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

private def leafEquals (x : RlpItem) (b : ByteArray) : Bool :=
  match x with
  | .bytes a => a == b
  | .list _ => false

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- B-M01/M02 observe the complete model constructor and every byte.
#guard leafEquals (RlpEncode.toRlp false) ByteArray.empty
#guard leafEquals (RlpEncode.toRlp true) ⟨#[1]⟩
-- B-E01/E02 retain both exact wires.
#guard encodeOf false = ⟨#[128]⟩
#guard encodeOf true = ⟨#[1]⟩

-- B-W01
#guard decodeTo (α := Bool) (ByteArray.mk (([[128]] : List (List UInt8)).flatten.toArray)) =
  (.ok false : Except RlpError Bool)

-- B-W02
#guard decodeTo (α := Bool) (ByteArray.mk (([[1]] : List (List UInt8)).flatten.toArray)) =
  (.ok true : Except RlpError Bool)

-- B-W03
#guard decodeTo (α := Bool) (ByteArray.mk (([[0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W04
#guard decodeTo (α := Bool) (ByteArray.mk (([[2]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W05
#guard decodeTo (α := Bool) (ByteArray.mk (([[127]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W06
#guard decodeTo (α := Bool) (ByteArray.mk (([[129, 128]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W07
#guard decodeTo (α := Bool) (ByteArray.mk (([[129, 255]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W08
#guard decodeTo (α := Bool) (ByteArray.mk (([[130, 0, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W09
#guard decodeTo (α := Bool) (ByteArray.mk (([[130, 1, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W10
#guard decodeTo (α := Bool) (ByteArray.mk (([[130, 1, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W11
#guard decodeTo (α := Bool) (ByteArray.mk (([[183, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W12
#guard decodeTo (α := Bool) (ByteArray.mk (([[184, 56, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W13
#guard decodeTo (α := Bool) (ByteArray.mk (([[185, 1, 0, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115], [115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115], [115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115], [115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115, 115], [115, 115, 115]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W14
#guard decodeTo (α := Bool) (ByteArray.mk (([[192]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W15
#guard decodeTo (α := Bool) (ByteArray.mk (([[193, 128]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W16
#guard decodeTo (α := Bool) (ByteArray.mk (([[193, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W17
#guard decodeTo (α := Bool) (ByteArray.mk (([[194, 193, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W18
#guard decodeTo (α := Bool) (ByteArray.mk (([[248, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128]] : List (List UInt8)).flatten.toArray)) =
  (.error (.shape "boolean") : Except RlpError Bool)

-- B-W19
#guard decodeTo (α := Bool) (ByteArray.mk (([] : List (List UInt8)).flatten.toArray)) =
  (.error (.empty) : Except RlpError Bool)

-- B-W20
#guard decodeTo (α := Bool) (ByteArray.mk (([[129]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W21
#guard decodeTo (α := Bool) (ByteArray.mk (([[130, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W22
#guard decodeTo (α := Bool) (ByteArray.mk (([[184]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W23
#guard decodeTo (α := Bool) (ByteArray.mk (([[185, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W24
#guard decodeTo (α := Bool) (ByteArray.mk (([[248]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W25
#guard decodeTo (α := Bool) (ByteArray.mk (([[249, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W26
#guard decodeTo (α := Bool) (ByteArray.mk (([[184, 56]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W27
#guard decodeTo (α := Bool) (ByteArray.mk (([[248, 56]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W28
#guard decodeTo (α := Bool) (ByteArray.mk (([[191, 255, 255, 255, 255, 255, 255, 255, 255]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W29
#guard decodeTo (α := Bool) (ByteArray.mk (([[255, 255, 255, 255, 255, 255, 255, 255, 255]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W30
#guard decodeTo (α := Bool) (ByteArray.mk (([[128, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.trailing) : Except RlpError Bool)

-- B-W31
#guard decodeTo (α := Bool) (ByteArray.mk (([[192, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.trailing) : Except RlpError Bool)

-- B-W32
#guard decodeTo (α := Bool) (ByteArray.mk (([[129, 128, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.trailing) : Except RlpError Bool)

-- B-W33
#guard decodeTo (α := Bool) (ByteArray.mk (([[193, 128, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.trailing) : Except RlpError Bool)

-- B-W34
#guard decodeTo (α := Bool) (ByteArray.mk (([[0, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "negative length") : Except RlpError Bool)

-- B-W35
#guard decodeTo (α := Bool) (ByteArray.mk (([[1, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "negative length") : Except RlpError Bool)

-- B-W36
#guard decodeTo (α := Bool) (ByteArray.mk (([[129, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Bool)

-- B-W37
#guard decodeTo (α := Bool) (ByteArray.mk (([[129, 127]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Bool)

-- B-W38
#guard decodeTo (α := Bool) (ByteArray.mk (([[184, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "leading zero length") : Except RlpError Bool)

-- B-W39
#guard decodeTo (α := Bool) (ByteArray.mk (([[248, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "leading zero length") : Except RlpError Bool)

-- B-W40
#guard decodeTo (α := Bool) (ByteArray.mk (([[185, 0, 56]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "leading zero length") : Except RlpError Bool)

-- B-W41
#guard decodeTo (α := Bool) (ByteArray.mk (([[249, 0, 56]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "leading zero length") : Except RlpError Bool)

-- B-W42
#guard decodeTo (α := Bool) (ByteArray.mk (([[184, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Bool)

-- B-W43
#guard decodeTo (α := Bool) (ByteArray.mk (([[248, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Bool)

-- B-W44
#guard decodeTo (α := Bool) (ByteArray.mk (([[184, 55, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Bool)

-- B-W45
#guard decodeTo (α := Bool) (ByteArray.mk (([[248, 55, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Bool)

-- B-W46
#guard decodeTo (α := Bool) (ByteArray.mk (([[193, 129]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

-- B-W47
#guard decodeTo (α := Bool) (ByteArray.mk (([[194, 129, 0]] : List (List UInt8)).flatten.toArray)) =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Bool)

-- B-W48
#guard decodeTo (α := Bool) (ByteArray.mk (([[194, 184, 1]] : List (List UInt8)).flatten.toArray)) =
  (.error (.truncated) : Except RlpError Bool)

end STFSpec.Conformance.Codec.RlpBoolGuards
