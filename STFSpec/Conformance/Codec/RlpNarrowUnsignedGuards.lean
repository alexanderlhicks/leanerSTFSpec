/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Narrow unsigned RLP complete-result controls

Library `EthConformance`. One hundred forty-seven fixed complete outcomes compare whole
words, bytes and diagnostics, including the separate Nat/ByteArray contracts.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpNarrowUnsignedGuards
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- U64-H-E00
#guard encodeOf (U64.ofNat 0) =
  ⟨#[128]⟩

-- U64-H-M00
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[]⟩) =
  (.ok (U64.ofNat 0) : Except RlpError U64)

-- U64-H-W00
#guard decodeTo (α := U64) ⟨#[128]⟩ =
  (.ok (U64.ofNat 0) : Except RlpError U64)

-- U64-H-E01
#guard encodeOf (U64.ofNat 1) =
  ⟨#[1]⟩

-- U64-H-M01
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1]⟩) =
  (.ok (U64.ofNat 1) : Except RlpError U64)

-- U64-H-W01
#guard decodeTo (α := U64) ⟨#[1]⟩ =
  (.ok (U64.ofNat 1) : Except RlpError U64)

-- U64-H-E02
#guard encodeOf (U64.ofNat 127) =
  ⟨#[127]⟩

-- U64-H-M02
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[127]⟩) =
  (.ok (U64.ofNat 127) : Except RlpError U64)

-- U64-H-W02
#guard decodeTo (α := U64) ⟨#[127]⟩ =
  (.ok (U64.ofNat 127) : Except RlpError U64)

-- U64-H-E03
#guard encodeOf (U64.ofNat 128) =
  ⟨#[129, 128]⟩

-- U64-H-M03
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[128]⟩) =
  (.ok (U64.ofNat 128) : Except RlpError U64)

-- U64-H-W03
#guard decodeTo (α := U64) ⟨#[129, 128]⟩ =
  (.ok (U64.ofNat 128) : Except RlpError U64)

-- U64-H-E04
#guard encodeOf (U64.ofNat 4294967296) =
  ⟨#[133, 1, 0, 0, 0, 0]⟩

-- U64-H-M04
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.ok (U64.ofNat 4294967296) : Except RlpError U64)

-- U64-H-W04
#guard decodeTo (α := U64) ⟨#[133, 1, 0, 0, 0, 0]⟩ =
  (.ok (U64.ofNat 4294967296) : Except RlpError U64)

-- U64-H-E05
#guard encodeOf (U64.ofNat 18446744073709551615) =
  ⟨#[136, 255, 255, 255, 255, 255, 255, 255, 255]⟩

-- U64-H-M05
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[255, 255, 255, 255, 255, 255, 255, 255]⟩) =
  (.ok (U64.ofNat 18446744073709551615) : Except RlpError U64)

-- U64-H-W05
#guard decodeTo (α := U64) ⟨#[136, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.ok (U64.ofNat 18446744073709551615) : Except RlpError U64)

-- U64-H-T00
#guard RlpDecode.ofRlp (α := U64) (.list []) =
  (.error (.shape "integer") : Except RlpError U64)

-- U64-H-T01
#guard RlpDecode.ofRlp (α := U64) (.list [.bytes ByteArray.empty]) =
  (.error (.shape "integer") : Except RlpError U64)

-- U64-H-T02
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U64)

-- U64-H-T03
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U64)

-- U64-H-T04
#guard RlpDecode.ofRlp (α := U64) (.bytes (ByteArray.mk ((List.replicate 256 0 : List UInt8).toArray))) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U64)

-- U64-H-T05
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U64)

-- U64-H-T06
#guard RlpDecode.ofRlp (α := U64) (.bytes (ByteArray.mk ((1 :: List.replicate 255 0 : List UInt8).toArray))) =
  (.error (.shape "integer width") : Except RlpError U64)

-- U64-H-R00
#guard decodeTo (α := U64) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError U64)

-- U64-H-R01
#guard decodeTo (α := U64) ⟨#[5, 6]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError U64)

-- U64-H-R02
#guard decodeTo (α := U64) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError U64)

-- U64-H-R03
#guard decodeTo (α := U64) ⟨#[130, 5]⟩ =
  (.error (.truncated) : Except RlpError U64)

-- U64-H-R04
#guard decodeTo (α := U64) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError U64)

-- U64-H-R05
#guard decodeTo (α := U64) ⟨#[129, 5]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError U64)

-- U64-H-R06
#guard decodeTo (α := U64) ⟨#[129, 5, 0]⟩ =
  (.error (.trailing) : Except RlpError U64)

-- U64-H-R07
#guard decodeTo (α := U64) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError U64)

-- U64-H-R08
#guard decodeTo (α := U64) ⟨#[185, 0, 64]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError U64)

-- U64-H-R09
#guard decodeTo (α := U64) ⟨#[184, 5]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError U64)

-- U64-H-R10
#guard decodeTo (α := U64) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError U64)

-- U64-H-R11
#guard decodeTo (α := U64) ⟨#[184, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError U64)

-- U64-H-X00
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1, 0]⟩) =
  (.ok (U64.ofNat 256) : Except RlpError U64)

-- U64-H-X01
#guard decodeTo (α := U64) ⟨#[130, 1, 0]⟩ =
  (.ok (U64.ofNat 256) : Except RlpError U64)

-- U64-H-X02
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.ok (U64.ofNat 4294967296) : Except RlpError U64)

-- U64-H-X03
#guard decodeTo (α := U64) ⟨#[133, 1, 0, 0, 0, 0]⟩ =
  (.ok (U64.ofNat 4294967296) : Except RlpError U64)

-- U64-H-X04
#guard RlpDecode.ofRlp (α := U64) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U64)

-- U64-H-X05
#guard decodeTo (α := U64) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U64)

-- U64-H-C00
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0]⟩) =
  (.ok ⟨#[0]⟩ : Except RlpError ByteArray)

-- U64-H-C01
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- U64-H-C02
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- U64-H-C03
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok 18446744073709551616 : Except RlpError Nat)

-- U64-H-C04
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- U64-H-C05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- U32-H-E00
#guard encodeOf (U32.ofNat 0) =
  ⟨#[128]⟩

-- U32-H-M00
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[]⟩) =
  (.ok (U32.ofNat 0) : Except RlpError U32)

-- U32-H-W00
#guard decodeTo (α := U32) ⟨#[128]⟩ =
  (.ok (U32.ofNat 0) : Except RlpError U32)

-- U32-H-E01
#guard encodeOf (U32.ofNat 1) =
  ⟨#[1]⟩

-- U32-H-M01
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1]⟩) =
  (.ok (U32.ofNat 1) : Except RlpError U32)

-- U32-H-W01
#guard decodeTo (α := U32) ⟨#[1]⟩ =
  (.ok (U32.ofNat 1) : Except RlpError U32)

-- U32-H-E02
#guard encodeOf (U32.ofNat 127) =
  ⟨#[127]⟩

-- U32-H-M02
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[127]⟩) =
  (.ok (U32.ofNat 127) : Except RlpError U32)

-- U32-H-W02
#guard decodeTo (α := U32) ⟨#[127]⟩ =
  (.ok (U32.ofNat 127) : Except RlpError U32)

-- U32-H-E03
#guard encodeOf (U32.ofNat 128) =
  ⟨#[129, 128]⟩

-- U32-H-M03
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[128]⟩) =
  (.ok (U32.ofNat 128) : Except RlpError U32)

-- U32-H-W03
#guard decodeTo (α := U32) ⟨#[129, 128]⟩ =
  (.ok (U32.ofNat 128) : Except RlpError U32)

-- U32-H-E04
#guard encodeOf (U32.ofNat 65536) =
  ⟨#[131, 1, 0, 0]⟩

-- U32-H-M04
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1, 0, 0]⟩) =
  (.ok (U32.ofNat 65536) : Except RlpError U32)

-- U32-H-W04
#guard decodeTo (α := U32) ⟨#[131, 1, 0, 0]⟩ =
  (.ok (U32.ofNat 65536) : Except RlpError U32)

-- U32-H-E05
#guard encodeOf (U32.ofNat 4294967295) =
  ⟨#[132, 255, 255, 255, 255]⟩

-- U32-H-M05
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[255, 255, 255, 255]⟩) =
  (.ok (U32.ofNat 4294967295) : Except RlpError U32)

-- U32-H-W05
#guard decodeTo (α := U32) ⟨#[132, 255, 255, 255, 255]⟩ =
  (.ok (U32.ofNat 4294967295) : Except RlpError U32)

-- U32-H-T00
#guard RlpDecode.ofRlp (α := U32) (.list []) =
  (.error (.shape "integer") : Except RlpError U32)

-- U32-H-T01
#guard RlpDecode.ofRlp (α := U32) (.list [.bytes ByteArray.empty]) =
  (.error (.shape "integer") : Except RlpError U32)

-- U32-H-T02
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U32)

-- U32-H-T03
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U32)

-- U32-H-T04
#guard RlpDecode.ofRlp (α := U32) (.bytes (ByteArray.mk ((List.replicate 256 0 : List UInt8).toArray))) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U32)

-- U32-H-T05
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-T06
#guard RlpDecode.ofRlp (α := U32) (.bytes (ByteArray.mk ((1 :: List.replicate 255 0 : List UInt8).toArray))) =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-R00
#guard decodeTo (α := U32) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError U32)

-- U32-H-R01
#guard decodeTo (α := U32) ⟨#[5, 6]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError U32)

-- U32-H-R02
#guard decodeTo (α := U32) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError U32)

-- U32-H-R03
#guard decodeTo (α := U32) ⟨#[130, 5]⟩ =
  (.error (.truncated) : Except RlpError U32)

-- U32-H-R04
#guard decodeTo (α := U32) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError U32)

-- U32-H-R05
#guard decodeTo (α := U32) ⟨#[129, 5]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError U32)

-- U32-H-R06
#guard decodeTo (α := U32) ⟨#[129, 5, 0]⟩ =
  (.error (.trailing) : Except RlpError U32)

-- U32-H-R07
#guard decodeTo (α := U32) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError U32)

-- U32-H-R08
#guard decodeTo (α := U32) ⟨#[185, 0, 64]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError U32)

-- U32-H-R09
#guard decodeTo (α := U32) ⟨#[184, 5]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError U32)

-- U32-H-R10
#guard decodeTo (α := U32) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError U32)

-- U32-H-R11
#guard decodeTo (α := U32) ⟨#[184, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError U32)

-- U32-H-X00
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1, 0]⟩) =
  (.ok (U32.ofNat 256) : Except RlpError U32)

-- U32-H-X01
#guard decodeTo (α := U32) ⟨#[130, 1, 0]⟩ =
  (.ok (U32.ofNat 256) : Except RlpError U32)

-- U32-H-X02
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-X03
#guard decodeTo (α := U32) ⟨#[133, 1, 0, 0, 0, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-X04
#guard RlpDecode.ofRlp (α := U32) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-X05
#guard decodeTo (α := U32) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U32)

-- U32-H-C00
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0]⟩) =
  (.ok ⟨#[0]⟩ : Except RlpError ByteArray)

-- U32-H-C01
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- U32-H-C02
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.ok ⟨#[1, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- U32-H-C03
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.ok 4294967296 : Except RlpError Nat)

-- U32-H-C04
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0, 0, 0, 0]⟩) =
  (.ok ⟨#[0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- U32-H-C05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- U8-H-E00
#guard encodeOf (U8.ofNat 0) =
  ⟨#[128]⟩

-- U8-H-M00
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[]⟩) =
  (.ok (U8.ofNat 0) : Except RlpError U8)

-- U8-H-W00
#guard decodeTo (α := U8) ⟨#[128]⟩ =
  (.ok (U8.ofNat 0) : Except RlpError U8)

-- U8-H-E01
#guard encodeOf (U8.ofNat 1) =
  ⟨#[1]⟩

-- U8-H-M01
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[1]⟩) =
  (.ok (U8.ofNat 1) : Except RlpError U8)

-- U8-H-W01
#guard decodeTo (α := U8) ⟨#[1]⟩ =
  (.ok (U8.ofNat 1) : Except RlpError U8)

-- U8-H-E02
#guard encodeOf (U8.ofNat 2) =
  ⟨#[2]⟩

-- U8-H-M02
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[2]⟩) =
  (.ok (U8.ofNat 2) : Except RlpError U8)

-- U8-H-W02
#guard decodeTo (α := U8) ⟨#[2]⟩ =
  (.ok (U8.ofNat 2) : Except RlpError U8)

-- U8-H-E03
#guard encodeOf (U8.ofNat 127) =
  ⟨#[127]⟩

-- U8-H-M03
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[127]⟩) =
  (.ok (U8.ofNat 127) : Except RlpError U8)

-- U8-H-W03
#guard decodeTo (α := U8) ⟨#[127]⟩ =
  (.ok (U8.ofNat 127) : Except RlpError U8)

-- U8-H-E04
#guard encodeOf (U8.ofNat 128) =
  ⟨#[129, 128]⟩

-- U8-H-M04
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[128]⟩) =
  (.ok (U8.ofNat 128) : Except RlpError U8)

-- U8-H-W04
#guard decodeTo (α := U8) ⟨#[129, 128]⟩ =
  (.ok (U8.ofNat 128) : Except RlpError U8)

-- U8-H-E05
#guard encodeOf (U8.ofNat 255) =
  ⟨#[129, 255]⟩

-- U8-H-M05
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[255]⟩) =
  (.ok (U8.ofNat 255) : Except RlpError U8)

-- U8-H-W05
#guard decodeTo (α := U8) ⟨#[129, 255]⟩ =
  (.ok (U8.ofNat 255) : Except RlpError U8)

-- U8-H-T00
#guard RlpDecode.ofRlp (α := U8) (.list []) =
  (.error (.shape "integer") : Except RlpError U8)

-- U8-H-T01
#guard RlpDecode.ofRlp (α := U8) (.list [.bytes ByteArray.empty]) =
  (.error (.shape "integer") : Except RlpError U8)

-- U8-H-T02
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U8)

-- U8-H-T03
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U8)

-- U8-H-T04
#guard RlpDecode.ofRlp (α := U8) (.bytes (ByteArray.mk ((List.replicate 256 0 : List UInt8).toArray))) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U8)

-- U8-H-T05
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[1, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-T06
#guard RlpDecode.ofRlp (α := U8) (.bytes (ByteArray.mk ((1 :: List.replicate 255 0 : List UInt8).toArray))) =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-R00
#guard decodeTo (α := U8) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError U8)

-- U8-H-R01
#guard decodeTo (α := U8) ⟨#[5, 6]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError U8)

-- U8-H-R02
#guard decodeTo (α := U8) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError U8)

-- U8-H-R03
#guard decodeTo (α := U8) ⟨#[130, 5]⟩ =
  (.error (.truncated) : Except RlpError U8)

-- U8-H-R04
#guard decodeTo (α := U8) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError U8)

-- U8-H-R05
#guard decodeTo (α := U8) ⟨#[129, 5]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError U8)

-- U8-H-R06
#guard decodeTo (α := U8) ⟨#[129, 5, 0]⟩ =
  (.error (.trailing) : Except RlpError U8)

-- U8-H-R07
#guard decodeTo (α := U8) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError U8)

-- U8-H-R08
#guard decodeTo (α := U8) ⟨#[185, 0, 64]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError U8)

-- U8-H-R09
#guard decodeTo (α := U8) ⟨#[184, 5]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError U8)

-- U8-H-R10
#guard decodeTo (α := U8) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError U8)

-- U8-H-R11
#guard decodeTo (α := U8) ⟨#[184, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError U8)

-- U8-H-X00
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[1, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-X01
#guard decodeTo (α := U8) ⟨#[130, 1, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-X02
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[1, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-X03
#guard decodeTo (α := U8) ⟨#[133, 1, 0, 0, 0, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-X04
#guard RlpDecode.ofRlp (α := U8) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-X05
#guard decodeTo (α := U8) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.error (.shape "integer width") : Except RlpError U8)

-- U8-H-C00
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0]⟩) =
  (.ok ⟨#[0]⟩ : Except RlpError ByteArray)

-- U8-H-C01
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- U8-H-C02
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[1, 0]⟩) =
  (.ok ⟨#[1, 0]⟩ : Except RlpError ByteArray)

-- U8-H-C03
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[1, 0]⟩) =
  (.ok 256 : Except RlpError Nat)

-- U8-H-C04
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0]⟩) =
  (.ok ⟨#[0]⟩ : Except RlpError ByteArray)

-- U8-H-C05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

end STFSpec.Conformance.Codec.RlpNarrowUnsignedGuards
