/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Typed RLP complete-result controls

Library `EthConformance`. WI290 catalog: N22 + Z22 + T10 + P21 + R90 + S3.
All 168 controls retain whole results and stable IDs. Source/host/handler
correspondence and callback effect traces are separate from these pure controls.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpDecodeOfGuards
open STFSpec.Codec STFSpec.Codec.Rlp

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private structure Accepted where
  code : Nat
  payload : List Nat
private local instance : DecidableEq Accepted := fun a b =>
  decidable_of_iff (a.code = b.code ∧ a.payload = b.payload) (by
    cases a
    cases b
    simp only [Accepted.mk.injEq])
private instance : RlpDecode Accepted where
  ofRlp _ := .ok ⟨777, [0,128,255]⟩
private structure Rejected where
private local instance : DecidableEq Rejected := fun a b =>
  isTrue (by cases a; cases b; rfl)
private instance : RlpDecode Rejected where
  ofRlp _ := .error (.shape "typed must not win")

-- N01
#guard decodeTo (α := Nat) ⟨#[128]⟩ =
  (.ok 0 : Except RlpError Nat)
-- Z01
#guard decodeTo (α := Nat) (encodeOf (0 : Nat)) =
  (.ok 0 : Except RlpError Nat)

-- N02
#guard decodeTo (α := Nat) ⟨#[1]⟩ =
  (.ok 1 : Except RlpError Nat)
-- Z02
#guard decodeTo (α := Nat) (encodeOf (1 : Nat)) =
  (.ok 1 : Except RlpError Nat)

-- N03
#guard decodeTo (α := Nat) ⟨#[2]⟩ =
  (.ok 2 : Except RlpError Nat)
-- Z03
#guard decodeTo (α := Nat) (encodeOf (2 : Nat)) =
  (.ok 2 : Except RlpError Nat)

-- N04
#guard decodeTo (α := Nat) ⟨#[127]⟩ =
  (.ok 127 : Except RlpError Nat)
-- Z04
#guard decodeTo (α := Nat) (encodeOf (127 : Nat)) =
  (.ok 127 : Except RlpError Nat)

-- N05
#guard decodeTo (α := Nat) ⟨#[129, 128]⟩ =
  (.ok 128 : Except RlpError Nat)
-- Z05
#guard decodeTo (α := Nat) (encodeOf (128 : Nat)) =
  (.ok 128 : Except RlpError Nat)

-- N06
#guard decodeTo (α := Nat) ⟨#[129, 129]⟩ =
  (.ok 129 : Except RlpError Nat)
-- Z06
#guard decodeTo (α := Nat) (encodeOf (129 : Nat)) =
  (.ok 129 : Except RlpError Nat)

-- N07
#guard decodeTo (α := Nat) ⟨#[129, 255]⟩ =
  (.ok 255 : Except RlpError Nat)
-- Z07
#guard decodeTo (α := Nat) (encodeOf (255 : Nat)) =
  (.ok 255 : Except RlpError Nat)

-- N08
#guard decodeTo (α := Nat) ⟨#[130, 1, 0]⟩ =
  (.ok 256 : Except RlpError Nat)
-- Z08
#guard decodeTo (α := Nat) (encodeOf (256 : Nat)) =
  (.ok 256 : Except RlpError Nat)

-- N09
#guard decodeTo (α := Nat) ⟨#[130, 1, 1]⟩ =
  (.ok 257 : Except RlpError Nat)
-- Z09
#guard decodeTo (α := Nat) (encodeOf (257 : Nat)) =
  (.ok 257 : Except RlpError Nat)

-- N10
#guard decodeTo (α := Nat) ⟨#[130, 4, 0]⟩ =
  (.ok 1024 : Except RlpError Nat)
-- Z10
#guard decodeTo (α := Nat) (encodeOf (1024 : Nat)) =
  (.ok 1024 : Except RlpError Nat)

-- N11
#guard decodeTo (α := Nat) ⟨#[132, 1, 0, 2, 3]⟩ =
  (.ok 16777731 : Except RlpError Nat)
-- Z11
#guard decodeTo (α := Nat) (encodeOf (16777731 : Nat)) =
  (.ok 16777731 : Except RlpError Nat)

-- N12
#guard decodeTo (α := Nat) ⟨#[136, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.ok (2^64-1) : Except RlpError Nat)
-- Z12
#guard decodeTo (α := Nat) (encodeOf ((2^64-1) : Nat)) =
  (.ok (2^64-1) : Except RlpError Nat)

-- N13
#guard decodeTo (α := Nat) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.ok (2^64) : Except RlpError Nat)
-- Z13
#guard decodeTo (α := Nat) (encodeOf ((2^64) : Nat)) =
  (.ok (2^64) : Except RlpError Nat)

-- N14
#guard decodeTo (α := Nat) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩ =
  (.ok (2^64+1) : Except RlpError Nat)
-- Z14
#guard decodeTo (α := Nat) (encodeOf ((2^64+1) : Nat)) =
  (.ok (2^64+1) : Except RlpError Nat)

-- N15
#guard decodeTo (α := Nat)
  ⟨#[
    160, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.ok (2^256-1) : Except RlpError Nat)
-- Z15
#guard decodeTo (α := Nat) (encodeOf ((2^256-1) : Nat)) =
  (.ok (2^256-1) : Except RlpError Nat)

-- N16
#guard decodeTo (α := Nat)
  ⟨#[
    161, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.ok (2^256) : Except RlpError Nat)
-- Z16
#guard decodeTo (α := Nat) (encodeOf ((2^256) : Nat)) =
  (.ok (2^256) : Except RlpError Nat)

-- N17
#guard decodeTo (α := Nat)
  ⟨#[
    161, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ =
  (.ok (2^256+1) : Except RlpError Nat)
-- Z17
#guard decodeTo (α := Nat) (encodeOf ((2^256+1) : Nat)) =
  (.ok (2^256+1) : Except RlpError Nat)

-- N18
#guard decodeTo (α := Nat)
  ⟨#[
    183, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3]⟩ =
  (.ok (2^(8*54)+0x010003) : Except RlpError Nat)
-- Z18
#guard decodeTo (α := Nat) (encodeOf ((2^(8*54)+0x010003) : Nat)) =
  (.ok (2^(8*54)+0x010003) : Except RlpError Nat)

-- N19
#guard decodeTo (α := Nat)
  ⟨#[
    184, 56, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3]⟩ =
  (.ok (2^(8*55)+0x010003) : Except RlpError Nat)
-- Z19
#guard decodeTo (α := Nat) (encodeOf ((2^(8*55)+0x010003) : Nat)) =
  (.ok (2^(8*55)+0x010003) : Except RlpError Nat)

-- N20
#guard decodeTo (α := Nat)
  ⟨#[
    184, 255, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3]⟩ =
  (.ok (2^(8*254)+0x010003) : Except RlpError Nat)
-- Z20
#guard decodeTo (α := Nat) (encodeOf ((2^(8*254)+0x010003) : Nat)) =
  (.ok (2^(8*254)+0x010003) : Except RlpError Nat)

-- N21
#guard decodeTo (α := Nat)
  ⟨#[
    185, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3]⟩ =
  (.ok (2^(8*255)+0x010003) : Except RlpError Nat)
-- Z21
#guard decodeTo (α := Nat) (encodeOf ((2^(8*255)+0x010003) : Nat)) =
  (.ok (2^(8*255)+0x010003) : Except RlpError Nat)

-- N22
#guard decodeTo (α := Nat)
  ⟨#[
    185, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3]⟩ =
  (.ok (2^(8*256)+0x010003) : Except RlpError Nat)
-- Z22
#guard decodeTo (α := Nat) (encodeOf ((2^(8*256)+0x010003) : Nat)) =
  (.ok (2^(8*256)+0x010003) : Except RlpError Nat)

-- T01
#guard decodeTo (α := Nat) ⟨#[192]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T02
#guard decodeTo (α := Nat) ⟨#[193, 128]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T03
#guard decodeTo (α := Nat) ⟨#[194, 193, 128]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T04
#guard decodeTo (α := Nat) ⟨#[195, 1, 2, 3]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T05
#guard decodeTo (α := Nat)
  ⟨#[
    248, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T06
#guard decodeTo (α := Nat)
  ⟨#[
    249, 1, 0, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128]⟩ =
  (.error (.shape "integer") : Except RlpError Nat)

-- T07
#guard decodeTo (α := Nat) ⟨#[0]⟩ =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- T08
#guard decodeTo (α := Nat) ⟨#[130, 0, 1]⟩ =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- T09
#guard decodeTo (α := Nat) ⟨#[131, 0, 0, 1]⟩ =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- T10
#guard decodeTo (α := Nat)
  ⟨#[
    184, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

section
private structure Sentinel0 where
private local instance : DecidableEq Sentinel0 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel0 where
  ofRlp _ := .error (.empty)
-- P01
#guard decodeTo (α := Sentinel0) ⟨#[128]⟩ =
  (.error (.empty) : Except RlpError Sentinel0)
-- P02
#guard decodeTo (α := Sentinel0) ⟨#[1]⟩ =
  (.error (.empty) : Except RlpError Sentinel0)
-- P03
#guard decodeTo (α := Sentinel0) ⟨#[192]⟩ =
  (.error (.empty) : Except RlpError Sentinel0)
end

section
private structure Sentinel1 where
private local instance : DecidableEq Sentinel1 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel1 where
  ofRlp _ := .error (.truncated)
-- P04
#guard decodeTo (α := Sentinel1) ⟨#[128]⟩ =
  (.error (.truncated) : Except RlpError Sentinel1)
-- P05
#guard decodeTo (α := Sentinel1) ⟨#[1]⟩ =
  (.error (.truncated) : Except RlpError Sentinel1)
-- P06
#guard decodeTo (α := Sentinel1) ⟨#[192]⟩ =
  (.error (.truncated) : Except RlpError Sentinel1)
end

section
private structure Sentinel2 where
private local instance : DecidableEq Sentinel2 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel2 where
  ofRlp _ := .error (.trailing)
-- P07
#guard decodeTo (α := Sentinel2) ⟨#[128]⟩ =
  (.error (.trailing) : Except RlpError Sentinel2)
-- P08
#guard decodeTo (α := Sentinel2) ⟨#[1]⟩ =
  (.error (.trailing) : Except RlpError Sentinel2)
-- P09
#guard decodeTo (α := Sentinel2) ⟨#[192]⟩ =
  (.error (.trailing) : Except RlpError Sentinel2)
end

section
private structure Sentinel3 where
private local instance : DecidableEq Sentinel3 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel3 where
  ofRlp _ := .error (.nonCanonical "")
-- P10
#guard decodeTo (α := Sentinel3) ⟨#[128]⟩ =
  (.error (.nonCanonical "") : Except RlpError Sentinel3)
-- P11
#guard decodeTo (α := Sentinel3) ⟨#[1]⟩ =
  (.error (.nonCanonical "") : Except RlpError Sentinel3)
-- P12
#guard decodeTo (α := Sentinel3) ⟨#[192]⟩ =
  (.error (.nonCanonical "") : Except RlpError Sentinel3)
end

section
private structure Sentinel4 where
private local instance : DecidableEq Sentinel4 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel4 where
  ofRlp _ := .error (.nonCanonical "custom.NonCanonical/unchanged")
-- P13
#guard decodeTo (α := Sentinel4) ⟨#[128]⟩ =
  (.error (.nonCanonical "custom.NonCanonical/unchanged") : Except RlpError Sentinel4)
-- P14
#guard decodeTo (α := Sentinel4) ⟨#[1]⟩ =
  (.error (.nonCanonical "custom.NonCanonical/unchanged") : Except RlpError Sentinel4)
-- P15
#guard decodeTo (α := Sentinel4) ⟨#[192]⟩ =
  (.error (.nonCanonical "custom.NonCanonical/unchanged") : Except RlpError Sentinel4)
end

section
private structure Sentinel5 where
private local instance : DecidableEq Sentinel5 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel5 where
  ofRlp _ := .error (.shape "")
-- P16
#guard decodeTo (α := Sentinel5) ⟨#[128]⟩ =
  (.error (.shape "") : Except RlpError Sentinel5)
-- P17
#guard decodeTo (α := Sentinel5) ⟨#[1]⟩ =
  (.error (.shape "") : Except RlpError Sentinel5)
-- P18
#guard decodeTo (α := Sentinel5) ⟨#[192]⟩ =
  (.error (.shape "") : Except RlpError Sentinel5)
end

section
private structure Sentinel6 where
private local instance : DecidableEq Sentinel6 := fun a b =>
  isTrue (by cases a; cases b; rfl)
private local instance : RlpDecode Sentinel6 where
  ofRlp _ := .error (.shape "custom.Shape/unchanged")
-- P19
#guard decodeTo (α := Sentinel6) ⟨#[128]⟩ =
  (.error (.shape "custom.Shape/unchanged") : Except RlpError Sentinel6)
-- P20
#guard decodeTo (α := Sentinel6) ⟨#[1]⟩ =
  (.error (.shape "custom.Shape/unchanged") : Except RlpError Sentinel6)
-- P21
#guard decodeTo (α := Sentinel6) ⟨#[192]⟩ =
  (.error (.shape "custom.Shape/unchanged") : Except RlpError Sentinel6)
end

-- R01-N
#guard decodeTo (α := Nat) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError Nat)

-- R01-A
#guard decodeTo (α := Accepted) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError Accepted)

-- R01-J
#guard decodeTo (α := Rejected) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError Rejected)

-- R02-N
#guard decodeTo (α := Nat) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R02-A
#guard decodeTo (α := Accepted) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R02-J
#guard decodeTo (α := Rejected) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R03-N
#guard decodeTo (α := Nat) ⟨#[130, 1]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R03-A
#guard decodeTo (α := Accepted) ⟨#[130, 1]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R03-J
#guard decodeTo (α := Rejected) ⟨#[130, 1]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R04-N
#guard decodeTo (α := Nat) ⟨#[184]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R04-A
#guard decodeTo (α := Accepted) ⟨#[184]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R04-J
#guard decodeTo (α := Rejected) ⟨#[184]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R05-N
#guard decodeTo (α := Nat) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R05-A
#guard decodeTo (α := Accepted) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R05-J
#guard decodeTo (α := Rejected) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R06-N
#guard decodeTo (α := Nat) ⟨#[248]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R06-A
#guard decodeTo (α := Accepted) ⟨#[248]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R06-J
#guard decodeTo (α := Rejected) ⟨#[248]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R07-N
#guard decodeTo (α := Nat) ⟨#[249, 0]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R07-A
#guard decodeTo (α := Accepted) ⟨#[249, 0]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R07-J
#guard decodeTo (α := Rejected) ⟨#[249, 0]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R08-N
#guard decodeTo (α := Nat) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R08-A
#guard decodeTo (α := Accepted) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R08-J
#guard decodeTo (α := Rejected) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R09-N
#guard decodeTo (α := Nat) ⟨#[248, 56]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R09-A
#guard decodeTo (α := Accepted) ⟨#[248, 56]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R09-J
#guard decodeTo (α := Rejected) ⟨#[248, 56]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R10-N
#guard decodeTo (α := Nat) ⟨#[191, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R10-A
#guard decodeTo (α := Accepted) ⟨#[191, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R10-J
#guard decodeTo (α := Rejected) ⟨#[191, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R11-N
#guard decodeTo (α := Nat) ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R11-A
#guard decodeTo (α := Accepted) ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R11-J
#guard decodeTo (α := Rejected) ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R12-N
#guard decodeTo (α := Nat) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError Nat)

-- R12-A
#guard decodeTo (α := Accepted) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError Accepted)

-- R12-J
#guard decodeTo (α := Rejected) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError Rejected)

-- R13-N
#guard decodeTo (α := Nat) ⟨#[192, 0]⟩ =
  (.error (.trailing) : Except RlpError Nat)

-- R13-A
#guard decodeTo (α := Accepted) ⟨#[192, 0]⟩ =
  (.error (.trailing) : Except RlpError Accepted)

-- R13-J
#guard decodeTo (α := Rejected) ⟨#[192, 0]⟩ =
  (.error (.trailing) : Except RlpError Rejected)

-- R14-N
#guard decodeTo (α := Nat) ⟨#[129, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Nat)

-- R14-A
#guard decodeTo (α := Accepted) ⟨#[129, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Accepted)

-- R14-J
#guard decodeTo (α := Rejected) ⟨#[129, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Rejected)

-- R15-N
#guard decodeTo (α := Nat) ⟨#[193, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Nat)

-- R15-A
#guard decodeTo (α := Accepted) ⟨#[193, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Accepted)

-- R15-J
#guard decodeTo (α := Rejected) ⟨#[193, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError Rejected)

-- R16-N
#guard decodeTo (α := Nat) ⟨#[0, 1]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Nat)

-- R16-A
#guard decodeTo (α := Accepted) ⟨#[0, 1]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Accepted)

-- R16-J
#guard decodeTo (α := Rejected) ⟨#[0, 1]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Rejected)

-- R17-N
#guard decodeTo (α := Nat) ⟨#[1, 0]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Nat)

-- R17-A
#guard decodeTo (α := Accepted) ⟨#[1, 0]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Accepted)

-- R17-J
#guard decodeTo (α := Rejected) ⟨#[1, 0]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError Rejected)

-- R18-N
#guard decodeTo (α := Nat) ⟨#[129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Nat)

-- R18-A
#guard decodeTo (α := Accepted) ⟨#[129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Accepted)

-- R18-J
#guard decodeTo (α := Rejected) ⟨#[129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Rejected)

-- R19-N
#guard decodeTo (α := Nat) ⟨#[129, 127]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Nat)

-- R19-A
#guard decodeTo (α := Accepted) ⟨#[129, 127]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Accepted)

-- R19-J
#guard decodeTo (α := Rejected) ⟨#[129, 127]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Rejected)

-- R20-N
#guard decodeTo (α := Nat) ⟨#[184, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Nat)

-- R20-A
#guard decodeTo (α := Accepted) ⟨#[184, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Accepted)

-- R20-J
#guard decodeTo (α := Rejected) ⟨#[184, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Rejected)

-- R21-N
#guard decodeTo (α := Nat) ⟨#[248, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Nat)

-- R21-A
#guard decodeTo (α := Accepted) ⟨#[248, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Accepted)

-- R21-J
#guard decodeTo (α := Rejected) ⟨#[248, 0]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Rejected)

-- R22-N
#guard decodeTo (α := Nat) ⟨#[185, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Nat)

-- R22-A
#guard decodeTo (α := Accepted) ⟨#[185, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Accepted)

-- R22-J
#guard decodeTo (α := Rejected) ⟨#[185, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Rejected)

-- R23-N
#guard decodeTo (α := Nat) ⟨#[249, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Nat)

-- R23-A
#guard decodeTo (α := Accepted) ⟨#[249, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Accepted)

-- R23-J
#guard decodeTo (α := Rejected) ⟨#[249, 0, 56]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError Rejected)

-- R24-N
#guard decodeTo (α := Nat) ⟨#[184, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Nat)

-- R24-A
#guard decodeTo (α := Accepted) ⟨#[184, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Accepted)

-- R24-J
#guard decodeTo (α := Rejected) ⟨#[184, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Rejected)

-- R25-N
#guard decodeTo (α := Nat) ⟨#[248, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Nat)

-- R25-A
#guard decodeTo (α := Accepted) ⟨#[248, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Accepted)

-- R25-J
#guard decodeTo (α := Rejected) ⟨#[248, 1]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Rejected)

-- R26-N
#guard decodeTo (α := Nat) ⟨#[184, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Nat)

-- R26-A
#guard decodeTo (α := Accepted) ⟨#[184, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Accepted)

-- R26-J
#guard decodeTo (α := Rejected) ⟨#[184, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Rejected)

-- R27-N
#guard decodeTo (α := Nat) ⟨#[248, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Nat)

-- R27-A
#guard decodeTo (α := Accepted) ⟨#[248, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Accepted)

-- R27-J
#guard decodeTo (α := Rejected) ⟨#[248, 55, 0]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError Rejected)

-- R28-N
#guard decodeTo (α := Nat) ⟨#[193, 129]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R28-A
#guard decodeTo (α := Accepted) ⟨#[193, 129]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R28-J
#guard decodeTo (α := Rejected) ⟨#[193, 129]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- R29-N
#guard decodeTo (α := Nat) ⟨#[194, 129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Nat)

-- R29-A
#guard decodeTo (α := Accepted) ⟨#[194, 129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Accepted)

-- R29-J
#guard decodeTo (α := Rejected) ⟨#[194, 129, 0]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError Rejected)

-- R30-N
#guard decodeTo (α := Nat) ⟨#[194, 184, 1]⟩ =
  (.error (.truncated) : Except RlpError Nat)

-- R30-A
#guard decodeTo (α := Accepted) ⟨#[194, 184, 1]⟩ =
  (.error (.truncated) : Except RlpError Accepted)

-- R30-J
#guard decodeTo (α := Rejected) ⟨#[194, 184, 1]⟩ =
  (.error (.truncated) : Except RlpError Rejected)

-- S01
#guard decodeTo (α := Accepted) ⟨#[128]⟩ =
  (.ok ⟨777, [0,128,255]⟩ : Except RlpError Accepted)

-- S02
#guard decodeTo (α := Accepted) ⟨#[1]⟩ =
  (.ok ⟨777, [0,128,255]⟩ : Except RlpError Accepted)

-- S03
#guard decodeTo (α := Accepted) ⟨#[192]⟩ =
  (.ok ⟨777, [0,128,255]⟩ : Except RlpError Accepted)

end STFSpec.Conformance.Codec.RlpDecodeOfGuards
