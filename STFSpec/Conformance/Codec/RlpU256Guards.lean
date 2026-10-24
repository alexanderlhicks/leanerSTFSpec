/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# U256 RLP complete-result controls

Library `EthConformance`. Sixty-four fixed complete outcomes compare whole
words, bytes and diagnostics, including the separate Nat/ByteArray contracts.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpU256Guards
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- H-E00
#guard encodeOf (U256.ofNat 0) = ⟨#[128]⟩

-- H-E01
#guard encodeOf (U256.ofNat 1) = ⟨#[1]⟩

-- H-E02
#guard encodeOf (U256.ofNat 127) = ⟨#[127]⟩

-- H-E03
#guard encodeOf (U256.ofNat 128) = ⟨#[129, 128]⟩

-- H-E04
#guard encodeOf (U256.ofNat 255) = ⟨#[129, 255]⟩

-- H-E05
#guard encodeOf (U256.ofNat 256) = ⟨#[130, 1, 0]⟩

-- H-E06
#guard encodeOf (U256.ofNat 1024) = ⟨#[130, 4, 0]⟩

-- H-E07
#guard encodeOf (U256.ofNat 65538) = ⟨#[131, 1, 0, 2]⟩

-- H-E08
#guard encodeOf (U256.ofNat 18446744073709551615) = ⟨#[136, 255, 255, 255, 255, 255, 255, 255, 255]⟩

-- H-E09
#guard encodeOf (U256.ofNat 18446744073709551616) = ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- H-E10
#guard encodeOf (U256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968) = ⟨#[160, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- H-E11
#guard encodeOf (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) = ⟨#[160, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩

-- H-M00
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[]⟩) =
  (.ok (U256.ofNat 0) : Except RlpError U256)

-- H-M01
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1]⟩) =
  (.ok (U256.ofNat 1) : Except RlpError U256)

-- H-M02
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[127]⟩) =
  (.ok (U256.ofNat 127) : Except RlpError U256)

-- H-M03
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[128]⟩) =
  (.ok (U256.ofNat 128) : Except RlpError U256)

-- H-M04
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[255]⟩) =
  (.ok (U256.ofNat 255) : Except RlpError U256)

-- H-M05
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0]⟩) =
  (.ok (U256.ofNat 256) : Except RlpError U256)

-- H-M06
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[4, 0]⟩) =
  (.ok (U256.ofNat 1024) : Except RlpError U256)

-- H-M07
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0, 2]⟩) =
  (.ok (U256.ofNat 65538) : Except RlpError U256)

-- H-M08
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[255, 255, 255, 255, 255, 255, 255, 255]⟩) =
  (.ok (U256.ofNat 18446744073709551615) : Except RlpError U256)

-- H-M09
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok (U256.ofNat 18446744073709551616) : Except RlpError U256)

-- H-M10
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok (U256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968) : Except RlpError U256)

-- H-M11
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩) =
  (.ok (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) : Except RlpError U256)

-- H-W00
#guard decodeTo (α := U256) ⟨#[128]⟩ =
  (.ok (U256.ofNat 0) : Except RlpError U256)

-- H-W01
#guard decodeTo (α := U256) ⟨#[1]⟩ =
  (.ok (U256.ofNat 1) : Except RlpError U256)

-- H-W02
#guard decodeTo (α := U256) ⟨#[127]⟩ =
  (.ok (U256.ofNat 127) : Except RlpError U256)

-- H-W03
#guard decodeTo (α := U256) ⟨#[129, 128]⟩ =
  (.ok (U256.ofNat 128) : Except RlpError U256)

-- H-W04
#guard decodeTo (α := U256) ⟨#[129, 255]⟩ =
  (.ok (U256.ofNat 255) : Except RlpError U256)

-- H-W05
#guard decodeTo (α := U256) ⟨#[130, 1, 0]⟩ =
  (.ok (U256.ofNat 256) : Except RlpError U256)

-- H-W06
#guard decodeTo (α := U256) ⟨#[130, 4, 0]⟩ =
  (.ok (U256.ofNat 1024) : Except RlpError U256)

-- H-W07
#guard decodeTo (α := U256) ⟨#[131, 1, 0, 2]⟩ =
  (.ok (U256.ofNat 65538) : Except RlpError U256)

-- H-W08
#guard decodeTo (α := U256) ⟨#[136, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.ok (U256.ofNat 18446744073709551615) : Except RlpError U256)

-- H-W09
#guard decodeTo (α := U256) ⟨#[137, 1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.ok (U256.ofNat 18446744073709551616) : Except RlpError U256)

-- H-W10
#guard decodeTo (α := U256) ⟨#[160, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ =
  (.ok (U256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968) : Except RlpError U256)

-- H-W11
#guard decodeTo (α := U256) ⟨#[160, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ =
  (.ok (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) : Except RlpError U256)

-- H-T00
#guard RlpDecode.ofRlp (α := U256) (.list []) =
  (.error (.shape "integer") : Except RlpError U256)

-- H-T01
#guard RlpDecode.ofRlp (α := U256) (.list [.bytes ByteArray.empty]) =
  (.error (.shape "integer") : Except RlpError U256)

-- H-T02
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U256)

-- H-T03
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U256)

-- H-T04
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U256)

-- H-T05
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U256)

-- H-T06
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError U256)

-- H-T07
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U256)

-- H-T08
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U256)

-- H-T09
#guard RlpDecode.ofRlp (α := U256) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.shape "integer width") : Except RlpError U256)

-- H-R00
#guard decodeTo (α := U256) ⟨#[]⟩ =
  (.error (.empty) : Except RlpError U256)

-- H-R01
#guard decodeTo (α := U256) ⟨#[5, 6]⟩ =
  (.error (.nonCanonical "negative length") : Except RlpError U256)

-- H-R02
#guard decodeTo (α := U256) ⟨#[129]⟩ =
  (.error (.truncated) : Except RlpError U256)

-- H-R03
#guard decodeTo (α := U256) ⟨#[130, 5]⟩ =
  (.error (.truncated) : Except RlpError U256)

-- H-R04
#guard decodeTo (α := U256) ⟨#[128, 0]⟩ =
  (.error (.trailing) : Except RlpError U256)

-- H-R05
#guard decodeTo (α := U256) ⟨#[129, 5]⟩ =
  (.error (.nonCanonical "prefixed single byte") : Except RlpError U256)

-- H-R06
#guard decodeTo (α := U256) ⟨#[129, 5, 0]⟩ =
  (.error (.trailing) : Except RlpError U256)

-- H-R07
#guard decodeTo (α := U256) ⟨#[185, 0]⟩ =
  (.error (.truncated) : Except RlpError U256)

-- H-R08
#guard decodeTo (α := U256) ⟨#[185, 0, 64]⟩ =
  (.error (.nonCanonical "leading zero length") : Except RlpError U256)

-- H-R09
#guard decodeTo (α := U256) ⟨#[184, 5]⟩ =
  (.error (.nonCanonical "long form for short payload") : Except RlpError U256)

-- H-R10
#guard decodeTo (α := U256) ⟨#[184, 56]⟩ =
  (.error (.truncated) : Except RlpError U256)

-- H-R11
#guard decodeTo (α := U256) ⟨#[184, 56, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0]⟩ =
  (.error (.trailing) : Except RlpError U256)

-- H-C00
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0]⟩) =
  (.ok ⟨#[0]⟩ : Except RlpError ByteArray)

-- H-C01
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- H-C02
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- H-C03
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok 115792089237316195423570985008687907853269984665640564039457584007913129639936 : Except RlpError Nat)

-- H-C04
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.ok ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- H-C05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) =
  (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

end STFSpec.Conformance.Codec.RlpU256Guards
