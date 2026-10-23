/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Typed RLP encoding complete-byte controls

Library `EthConformance`. Handwritten expectations cover minimal integers,
zero-containing digits, width boundaries and private instance dispatch. These
bounded encoder checks establish no typed inverse, source or host equivalence.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4,7.
-/

namespace STFSpec.Conformance.Codec.RlpEncodeOfGuards
open STFSpec.Codec STFSpec.Codec.Rlp

#guard encodeOf (0 : Nat) = ⟨#[128]⟩
#guard encodeOf (1 : Nat) = ⟨#[1]⟩
#guard encodeOf (127 : Nat) = ⟨#[127]⟩
#guard encodeOf (128 : Nat) = ⟨#[129, 128]⟩
#guard encodeOf (255 : Nat) = ⟨#[129, 255]⟩
#guard encodeOf (256 : Nat) = ⟨#[130, 1, 0]⟩
#guard encodeOf (1024 : Nat) = ⟨#[130, 4, 0]⟩
#guard encodeOf (0x01000203 : Nat) = ⟨#[132, 1, 0, 2, 3]⟩
#guard (encodeOf (2 ^ 64 - 1 : Nat)).data.toList = 136 :: List.replicate 8 255
#guard (encodeOf (2 ^ 64 : Nat)).data.toList = [137, 1] ++ List.replicate 8 0
#guard (encodeOf (2 ^ 64 + 1 : Nat)).data.toList = [137, 1] ++ List.replicate 7 0 ++ [1]
#guard (encodeOf (2 ^ 256 - 1 : Nat)).data.toList = 160 :: List.replicate 32 255
#guard (encodeOf (2 ^ 256 : Nat)).data.toList = [161, 1] ++ List.replicate 32 0
#guard (encodeOf (2 ^ 256 + 1 : Nat)).data.toList = [161, 1] ++ List.replicate 31 0 ++ [1]

private structure Message where
  digit : UInt8

private instance : RlpEncode Message where
  toRlp a := .list [.bytes ⟨#[0, a.digit, 255]⟩, .list [], .bytes ⟨#[]⟩]

#guard encodeOf (Message.mk 128) = ⟨#[198, 131, 0, 128, 255, 192, 128]⟩
#guard encodeOf (Message.mk 1) = ⟨#[198, 131, 0, 1, 255, 192, 128]⟩

end STFSpec.Conformance.Codec.RlpEncodeOfGuards
