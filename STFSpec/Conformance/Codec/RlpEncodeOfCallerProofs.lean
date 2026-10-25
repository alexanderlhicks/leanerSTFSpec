/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Typed RLP encoding public-law callers

Library `EthConformance`. Private consumers reduce the new reference wrapper and
use existing public encoder, parser and Base laws. The raw accepted-image result
retains Q47's domain; bounded discharge adds no restriction to the Nat API.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3,7.
-/

namespace STFSpec.Conformance.Codec.RlpEncodeOfCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private theorem wrapper {α : Type} [RlpEncode α] (a : α) :
    encodeOf a = encode (RlpEncode.toRlp a) := rfl

private theorem bytes {α : Type} [RlpEncode α] (a : α) :
    (encodeOf a).data.toList = encodeModel (RlpEncode.toRlp a) :=
  toList_encode _

private theorem size {α : Type} [RlpEncode α] (a : α) :
    (encodeOf a).size = encodedSize (RlpEncode.toRlp a) :=
  size_encode _

private theorem nat_adapter (n : Nat) : RlpEncode.toRlp n = ofNat n := rfl

private theorem nat_wire_image (n : Nat) (h : Encodable (ofNat n)) :
    decode (encodeOf n) = .ok (ofNat n) := decode_encode _ h

private theorem bounded_domain (n : Nat) (h : n < 2 ^ 256) :
    Encodable (ofNat n) := by
  have shape : RlpItem.bytes (Uint.toBeBytes n).toByteArray = ofNat n :=
    (toNat_eq_ok_iff _ n).mp ((toNat_canonical_iff _ n).mpr rfl)
  rw [← shape, encodable_bytes_iff, Bytes.size_toByteArray]
  have width : (Uint.toBeBytes n).size ≤ 32 := (Uint.size_toBeBytes_le_iff _ _).mpr h
  omega

private theorem bounded_wire_image (n : Nat) (h : n < 2 ^ 256) :
    decode (encodeOf n) = .ok (ofNat n) := nat_wire_image n (bounded_domain n h)

private structure Message where
  digit : UInt8

private instance : RlpEncode Message where
  toRlp a := .list [.bytes ⟨#[0, a.digit, 255]⟩, .list [], .bytes ⟨#[]⟩]

private theorem supplied_dispatch :
    (encodeOf (Message.mk 128)).data.toList = [198, 131, 0, 128, 255, 192, 128] := by
  decide

end STFSpec.Conformance.Codec.RlpEncodeOfCallerProofs
