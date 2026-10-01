/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# RLP encoder deterministic regressions

Library `EthConformance`. All observations use public encoder/model APIs. Symbolic
large-length cases exercise Q47 helper completion, without allocating a payload
or asserting outside-domain protocol/pinned-host agreement.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4.
-/

open STFSpec.Base STFSpec.Codec STFSpec.Codec.Rlp

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def repeated (n : Nat) : ByteArray :=
  (Bytes.generate n (fun _ ↦ 128)).toByteArray
private def emptyChildren (n : Nat) : List RlpItem :=
  List.replicate n (.bytes ByteArray.empty)

#guard encodeBytes ByteArray.empty = bytes [128]
#guard encode (.list []) = bytes [192]
#guard encodeBytes (bytes [0]) = bytes [0]
#guard encodeBytes (bytes [127]) = bytes [127]
#guard encodeBytes (bytes [128]) = bytes [129, 128]
#guard encodeBytes (bytes [255]) = bytes [129, 255]
#guard encodeBytes (bytes [0, 1, 0]) = bytes [131, 0, 1, 0]
#guard encodeBytes (repeated 55) = bytes (183 :: List.replicate 55 128)
#guard encodeBytes (repeated 56) = bytes (184 :: 56 :: List.replicate 56 128)
#guard encodeBytes (repeated 255) = bytes (184 :: 255 :: List.replicate 255 128)
#guard encodeBytes (repeated 256) = bytes (185 :: 1 :: 0 :: List.replicate 256 128)
#guard encode (.list (emptyChildren 55)) = bytes (247 :: List.replicate 55 128)
#guard encode (.list (emptyChildren 56)) = bytes (248 :: 56 :: List.replicate 56 128)
-- The string itself adds a prefix; this boundary is encoded child length, not raw length.
#guard encode (.list [.bytes (repeated 54)]) = bytes (247 :: 182 :: List.replicate 54 128)
#guard encode (.list [.bytes (repeated 55)]) = bytes (248 :: 56 :: 183 :: List.replicate 55 128)
#guard encode (.list [.bytes ByteArray.empty]) = bytes [193, 128]
#guard encode (.list [.list []]) = bytes [193, 192]
#guard encode (.list [.list [.bytes ByteArray.empty]]) = bytes [194, 193, 128]
#guard encode (.list [.bytes (bytes [0]), .bytes ByteArray.empty,
  .list [.bytes (bytes [128]), .list [], .bytes (bytes [1, 0])],
  .bytes (bytes [255])]) = bytes [203, 0, 128, 198, 129, 128, 192, 130, 1, 0, 129, 255]
#guard encode (ofNat 0) = bytes [128]
#guard encode (ofNat 1) = bytes [1]
#guard encode (ofNat 1024) = bytes [130, 4, 0]
#guard encodeLengthPrefix 128 183 0 = bytes [128]
#guard encodeLengthPrefix 192 247 55 = bytes [247]
#guard encodeLengthPrefix 192 247 56 = bytes [248, 56]
#guard encodeLengthPrefix 128 183 255 = bytes [184, 255]
#guard encodeLengthPrefix 128 183 256 = bytes [185, 1, 0]
#guard encodeLengthPrefix 128 183 65535 = bytes [185, 255, 255]
#guard encodeLengthPrefix 128 183 65536 = bytes [186, 1, 0, 0]
#guard encodeLengthPrefix 192 247 (2 ^ 64 - 1) = bytes (255 :: List.replicate 8 255)
#guard encodeLengthPrefix 192 247 (2 ^ 64) = bytes (0 :: 1 :: List.replicate 8 0)
#guard encodeLengthPrefix 128 183 (2 ^ 64) = bytes (192 :: 1 :: List.replicate 8 0)
#guard encodeLengthPrefix 128 183 (256 ^ 71) = bytes (255 :: 1 :: List.replicate 71 0)
#guard encodeLengthPrefix 128 183 (256 ^ 72) = bytes (0 :: 1 :: List.replicate 72 0)
#guard encodeLengthPrefix 192 247 (256 ^ 71) = bytes (63 :: 1 :: List.replicate 71 0)
#guard encodeLengthPrefix 192 247 (256 ^ 72) = bytes (64 :: 1 :: List.replicate 72 0)
#guard encodedSize (.list (emptyChildren 56)) = 58
#guard (encodePayloadModel [.bytes (bytes [0]), .bytes ByteArray.empty,
  .list [.bytes (bytes [128])]]) = [0, 128, 194, 129, 128]
#guard (encode (.list (emptyChildren 56))).size = encodedSize (.list (emptyChildren 56))
