/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Generic list RLP complete controls

Library `EthConformance`. Exactly104 handwritten whole outcomes in catalogue order.
Private independent callbacks test pure first-error values and class independence.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpListGuards
open STFSpec.Codec STFSpec.Codec.Rlp

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Complete prefix-delimited constructor/length/byte observation, no nested deriving.
private def observe : RlpItem → List Nat
  | .bytes b => 0 :: b.size :: b.data.toList.map UInt8.toNat
  | .list xs => 1 :: xs.length :: xs.flatMap observe

private structure Probe where
  value : Nat
private instance : DecidableEq Probe := by
  intro a b
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      simp only [Probe.mk.injEq]
      infer_instance

private abbrev accept : RlpDecode Probe := ⟨fun _ => .ok ⟨7⟩⟩
private abbrev reject : RlpDecode Probe := ⟨fun _ => .error (.shape "unreached")⟩
private abbrev callback (e f : RlpError) : RlpDecode Probe := ⟨fun item =>
  match item with
  | .bytes b =>
    if b == ⟨#[0]⟩ then .error e
    else if b == ⟨#[1]⟩ then .ok ⟨7⟩
    else if b == ⟨#[2]⟩ then .error f
    else .ok ⟨99⟩
  | .list _ => .ok ⟨99⟩⟩

private structure Fail where
  value : Nat
private instance : DecidableEq Fail := by
  intro a b
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      simp only [Fail.mk.injEq]
      infer_instance

private structure Const where
  value : Nat
private instance : DecidableEq Const := by
  intro a b
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      simp only [Const.mk.injEq]
      infer_instance

private structure Local where
  value : Nat
private instance : DecidableEq Local := by
  intro a b
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      simp only [Local.mk.injEq]
      infer_instance

private instance : RlpEncode Fail := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Fail := ⟨fun _ => .error (.shape "always")⟩
private instance : RlpEncode Const := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Const := ⟨fun _ => .ok ⟨0⟩⟩
private instance : RlpEncode Local := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Local := ⟨fun item => (toNat item).bind
  (fun n => if n = 0 then .ok ⟨0⟩ else .error (.shape "absent two"))⟩

-- S01-M
#guard observe (RlpEncode.toRlp ([] : List Nat)) = observe (.list [])

-- S01-I
#guard RlpDecode.ofRlp (α := List Nat) (.list []) = .ok ([] : List Nat)

-- S01-E
#guard encodeOf ([] : List Nat) = ⟨#[192]⟩

-- S01-D
#guard decodeTo (α := List Nat) ⟨#[192]⟩ = .ok ([] : List Nat)

-- S02-M
#guard observe (RlpEncode.toRlp ([0] : List Nat)) = observe (.list [(.bytes ⟨#[]⟩)])

-- S02-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[]⟩)]) = .ok ([0] : List Nat)

-- S02-E
#guard encodeOf ([0] : List Nat) = ⟨#[193, 128]⟩

-- S02-D
#guard decodeTo (α := List Nat) ⟨#[193, 128]⟩ = .ok ([0] : List Nat)

-- S03-M
#guard observe (RlpEncode.toRlp ([1] : List Nat)) = observe (.list [(.bytes ⟨#[1]⟩)])

-- S03-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[1]⟩)]) = .ok ([1] : List Nat)

-- S03-E
#guard encodeOf ([1] : List Nat) = ⟨#[193, 1]⟩

-- S03-D
#guard decodeTo (α := List Nat) ⟨#[193, 1]⟩ = .ok ([1] : List Nat)

-- S04-M
#guard observe (RlpEncode.toRlp ([0, 1, 0] : List Nat)) = observe (.list [(.bytes ⟨#[]⟩),
  (.bytes ⟨#[1]⟩), (.bytes ⟨#[]⟩)])

-- S04-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[1]⟩),
  (.bytes ⟨#[]⟩)]) = .ok ([0, 1, 0] : List Nat)

-- S04-E
#guard encodeOf ([0, 1, 0] : List Nat) = ⟨#[195, 128, 1, 128]⟩

-- S04-D
#guard decodeTo (α := List Nat) ⟨#[195, 128, 1, 128]⟩ = .ok ([0, 1, 0] : List Nat)

-- S05-M
#guard observe (RlpEncode.toRlp ([128, 255,
  256] : List Nat)) = observe (.list [(.bytes ⟨#[128]⟩), (.bytes ⟨#[255]⟩), (.bytes ⟨#[1, 0]⟩)])

-- S05-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[128]⟩), (.bytes ⟨#[255]⟩),
  (.bytes ⟨#[1, 0]⟩)]) = .ok ([128, 255, 256] : List Nat)

-- S05-E
#guard encodeOf ([128, 255, 256] : List Nat) = ⟨#[199, 129, 128, 129, 255, 130, 1, 0]⟩

-- S05-D
#guard decodeTo (α := List Nat) ⟨#[199, 129, 128, 129, 255, 130, 1, 0]⟩ = .ok ([128, 255,
  256] : List Nat)

-- S06-M
#guard observe (RlpEncode.toRlp ([256, 1, 256] : List Nat)) = observe (.list [(.bytes ⟨#[1,
  0]⟩), (.bytes ⟨#[1]⟩), (.bytes ⟨#[1, 0]⟩)])

-- S06-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[1, 0]⟩), (.bytes ⟨#[1]⟩),
  (.bytes ⟨#[1, 0]⟩)]) = .ok ([256, 1, 256] : List Nat)

-- S06-E
#guard encodeOf ([256, 1, 256] : List Nat) = ⟨#[199, 130, 1, 0, 1, 130, 1, 0]⟩

-- S06-D
#guard decodeTo (α := List Nat) ⟨#[199, 130, 1, 0, 1, 130, 1, 0]⟩ = .ok ([256, 1, 256] : List Nat)

-- S07-M
#guard observe (RlpEncode.toRlp ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0] : List Nat)) = observe (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩)])

-- S07-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩)]) = .ok ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0] : List Nat)

-- S07-E
#guard encodeOf ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0] : List Nat) = ⟨#[247, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128]⟩

-- S07-D
#guard decodeTo (α := List Nat) ⟨#[247, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128]⟩ = .ok ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0] : List Nat)

-- S08-M
#guard observe (RlpEncode.toRlp ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0] : List Nat)) = observe (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩)])

-- S08-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩),
  (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩)]) = .ok ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat)

-- S08-E
#guard encodeOf ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0] : List Nat) = ⟨#[248, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128]⟩

-- S08-D
#guard decodeTo (α := List Nat) ⟨#[248, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128]⟩ = .ok ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat)

-- T01-I
#guard RlpDecode.ofRlp (α := List Nat) (.bytes ⟨#[]⟩) =
  (.error (.shape "list") : Except RlpError (List Nat))

-- T01-D
#guard decodeTo (α := List Nat) ⟨#[128]⟩ = (.error (.shape "list") : Except RlpError (List Nat))

-- T02-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[0]⟩),
  (.list [])]) = (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T02-D
#guard decodeTo (α := List Nat) ⟨#[194, 0,
  192]⟩ = (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T03-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[0]⟩)]) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T03-D
#guard decodeTo (α := List Nat) ⟨#[193,
  0]⟩ = (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T04-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.list [])]) =
  (.error (.shape "integer") : Except RlpError (List Nat))

-- T04-D
#guard decodeTo (α := List Nat) ⟨#[193,
  192]⟩ = (.error (.shape "integer") : Except RlpError (List Nat))

-- T05-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[0]⟩),
  (.bytes ⟨#[]⟩)]) = (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T05-D
#guard decodeTo (α := List Nat) ⟨#[195, 128, 0,
  128]⟩ = (.error (.nonCanonical "integer leading zero") : Except RlpError (List Nat))

-- T06-I
#guard RlpDecode.ofRlp (α := List Nat) (.list [(.list []),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "integer") : Except RlpError (List Nat))

-- T06-D
#guard decodeTo (α := List Nat) ⟨#[194, 192,
  0]⟩ = (.error (.shape "integer") : Except RlpError (List Nat))

-- R01-N
#guard decodeTo (α := List Nat) ⟨#[]⟩ = (.error (.empty) : Except RlpError (List Nat))

-- R01-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError (List Probe))

-- R01-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError (List Probe))

-- R02-N
#guard decodeTo (α := List Nat) ⟨#[194, 192]⟩ = (.error (.truncated) : Except RlpError (List Nat))

-- R02-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[194,
  192]⟩ = (.error (.truncated) : Except RlpError (List Probe))

-- R02-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[194,
  192]⟩ = (.error (.truncated) : Except RlpError (List Probe))

-- R03-N
#guard decodeTo (α := List Nat) ⟨#[193, 0, 0]⟩ = (.error (.trailing) : Except RlpError (List Nat))

-- R03-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[193, 0,
  0]⟩ = (.error (.trailing) : Except RlpError (List Probe))

-- R03-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[193, 0,
  0]⟩ = (.error (.trailing) : Except RlpError (List Probe))

-- R04-N
#guard decodeTo (α := List Nat) ⟨#[194, 0,
  129]⟩ = (.error (.truncated) : Except RlpError (List Nat))

-- R04-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[194, 0,
  129]⟩ = (.error (.truncated) : Except RlpError (List Probe))

-- R04-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[194, 0,
  129]⟩ = (.error (.truncated) : Except RlpError (List Probe))

-- R05-N
#guard decodeTo (α := List Nat) ⟨#[195, 0, 129,
  1]⟩ = (.error (.nonCanonical "prefixed single byte") : Except RlpError (List Nat))

-- R05-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[195, 0, 129,
  1]⟩ = (.error (.nonCanonical "prefixed single byte") : Except RlpError (List Probe))

-- R05-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[195, 0, 129,
  1]⟩ = (.error (.nonCanonical "prefixed single byte") : Except RlpError (List Probe))

-- R06-N
#guard decodeTo (α := List Nat) ⟨#[248,
  0]⟩ = (.error (.nonCanonical "leading zero length") : Except RlpError (List Nat))

-- R06-A
#guard letI : RlpDecode Probe := accept; decodeTo (α := List Probe) ⟨#[248,
  0]⟩ = (.error (.nonCanonical "leading zero length") : Except RlpError (List Probe))

-- R06-F
#guard letI : RlpDecode Probe := reject; decodeTo (α := List Probe) ⟨#[248,
  0]⟩ = (.error (.nonCanonical "leading zero length") : Except RlpError (List Probe))

-- A01-H
#guard letI : RlpDecode Probe := callback (.empty) (.shape "later"); RlpDecode.ofRlp (α := List
  Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.empty) : Except RlpError (List Probe))

-- A01-L
#guard letI : RlpDecode Probe := callback (.empty) (.shape "later"); RlpDecode.ofRlp (α := List
  Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.empty) : Except RlpError (List Probe))

-- A01-B
#guard letI : RlpDecode Probe := callback (.empty) (.shape "later"); RlpDecode.ofRlp (α := List
  Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- A02-H
#guard letI : RlpDecode Probe := callback (.truncated) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.truncated) : Except RlpError (List Probe))

-- A02-L
#guard letI : RlpDecode Probe := callback (.truncated) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.truncated) : Except RlpError (List Probe))

-- A02-B
#guard letI : RlpDecode Probe := callback (.truncated) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- A03-H
#guard letI : RlpDecode Probe := callback (.trailing) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.trailing) : Except RlpError (List Probe))

-- A03-L
#guard letI : RlpDecode Probe := callback (.trailing) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.trailing) : Except RlpError (List Probe))

-- A03-B
#guard letI : RlpDecode Probe := callback (.trailing) (.shape "later"); RlpDecode.ofRlp (α :=
  List Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- A04-H
#guard letI : RlpDecode Probe := callback (.nonCanonical "") (.shape "later"); RlpDecode.ofRlp
  (α := List Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.nonCanonical "") : Except RlpError (List Probe))

-- A04-L
#guard letI : RlpDecode Probe := callback (.nonCanonical "") (.shape "later"); RlpDecode.ofRlp
  (α := List Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.nonCanonical "") : Except RlpError (List Probe))

-- A04-B
#guard letI : RlpDecode Probe := callback (.nonCanonical "") (.shape "later"); RlpDecode.ofRlp
  (α := List Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- A05-H
#guard letI : RlpDecode Probe := callback (.nonCanonical "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.nonCanonical "arbitrary context") : Except RlpError (List Probe))

-- A05-L
#guard letI : RlpDecode Probe := callback (.nonCanonical "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.nonCanonical "arbitrary context") : Except RlpError (List Probe))

-- A05-B
#guard letI : RlpDecode Probe := callback (.nonCanonical "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- A06-H
#guard letI : RlpDecode Probe := callback (.shape "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[0]⟩),
  (.bytes ⟨#[2]⟩)]) = (.error (.shape "arbitrary context") : Except RlpError (List Probe))

-- A06-L
#guard letI : RlpDecode Probe := callback (.shape "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "arbitrary context") : Except RlpError (List Probe))

-- A06-B
#guard letI : RlpDecode Probe := callback (.shape "arbitrary context") (.shape "later");
  RlpDecode.ofRlp (α := List Probe) (.list [(.bytes ⟨#[2]⟩),
  (.bytes ⟨#[0]⟩)]) = (.error (.shape "later") : Except RlpError (List Probe))

-- CM01
#guard encodeOf ([⟨0⟩] : List Fail) = ⟨#[193, 128]⟩

-- CM02
#guard RlpDecode.ofRlp (α := List Fail) (.list [(.bytes ⟨#[]⟩)]) =
  (.error (.shape "always") : Except RlpError (List Fail))

-- CM03
#guard decodeTo (α := List Fail) ⟨#[193, 128]⟩ = .error (.shape "always")

-- CM04
#guard RlpDecode.ofRlp (α := List Const) (.list [(.bytes ⟨#[1]⟩)]) = .ok [⟨0⟩]

-- CM05
#guard decodeTo (α := List Const) ⟨#[193, 1]⟩ = .ok [⟨0⟩]

-- CM06
#guard encodeOf ([⟨0⟩] : List Const) = ⟨#[193, 128]⟩ ∧ (⟨#[193, 128]⟩ : ByteArray) ≠ ⟨#[193, 1]⟩

-- CM07
#guard RlpDecode.ofRlp (α := List Local) (.list [(.bytes ⟨#[]⟩), (.bytes ⟨#[]⟩)]) = .ok [⟨0⟩,⟨0⟩]

-- CM08
#guard decodeTo (α := List Local) ⟨#[194, 128, 128]⟩ = .ok [⟨0⟩,⟨0⟩]

-- CM09
#guard RlpDecode.ofRlp (α := Local) (RlpEncode.toRlp (⟨2⟩ : Local)) = .error (.shape "absent two")

-- CM10
#guard encodeOf ([⟨0⟩,⟨0⟩] : List Local) = ⟨#[194, 128, 128]⟩

-- Z01
#guard RlpDecode.ofRlp (α := List Fail) (.list []) = .ok []

-- Z02
#guard decodeTo (α := List Fail) ⟨#[192]⟩ = .ok []

-- Z03
#guard RlpDecode.ofRlp (α := List Const) (.list []) = .ok []

-- Z04
#guard decodeTo (α := List Local) ⟨#[192]⟩ = .ok []

-- K01
#guard observe (RlpEncode.toRlp ([[0],[1,
  0]] : List (List Nat))) = observe (.list [(.list [(.bytes ⟨#[]⟩)]), (.list [(.bytes ⟨#[1]⟩),
  (.bytes ⟨#[]⟩)])])

-- K02
#guard RlpDecode.ofRlp (α := List (List Nat)) (.list [(.list [(.bytes ⟨#[]⟩)]),
  (.list [(.bytes ⟨#[1]⟩), (.bytes ⟨#[]⟩)])]) = .ok ([[0],[1,0]] : List (List Nat))

-- K03
#guard encodeOf ([[0],[1,0]] : List (List Nat)) = ⟨#[197, 193, 128, 194, 1, 128]⟩

-- K04
#guard decodeTo (α := List (List Nat)) ⟨#[197, 193, 128, 194, 1, 128]⟩ = .ok ([[0],[1,
  0]] : List (List Nat))

-- X01
#guard decodeTo (α := List ByteArray) ⟨#[193, 0]⟩ = .ok [⟨#[0]⟩]

-- X02
#guard decodeTo (α := List Nat) ⟨#[193, 0]⟩ = .error (.nonCanonical "integer leading zero")

-- X03
#guard decodeTo (α := Nat) ⟨#[193, 0]⟩ = .error (.shape "integer")

-- X04
#guard decodeTo (α := List Nat) ⟨#[128]⟩ = .error (.shape "list")

-- X05
#guard decodeTo (α := Nat) ⟨#[128]⟩ = .ok 0

-- X06
#guard decodeTo (α := List (List Nat)) ⟨#[193, 192]⟩ = .ok [[]]

end STFSpec.Conformance.Codec.RlpListGuards
