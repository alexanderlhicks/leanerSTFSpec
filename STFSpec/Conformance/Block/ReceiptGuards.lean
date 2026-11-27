/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Complete raw receipt controls

Library `EthConformance`. The guards compare all receipt fields, the complete legacy
receipt and every byte of the typed payload.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–4.
-/

namespace STFSpec.Conformance.Block.ReceiptGuards

open STFSpec.Base STFSpec.Block STFSpec.Vm.Core

private abbrev LogFields := List UInt8 × List (List UInt8) × List UInt8
private abbrev ReceiptFields := Bool × Nat × List UInt8 × List LogFields

private def logFields (log : Log) : LogFields :=
  (log.address.toBytes.toList, log.topics.toList.map (·.toBytes.toList), log.data.toList)

private def fields (r : Receipt) : ReceiptFields :=
  (r.succeeded, r.cumulativeGasUsed, r.bloom.toBytes.toList, r.logs.toList.map logFields)

private def zeroBloom : Bloom := FixedBytes.ofNat 0
private def sampleBloom : Bloom := FixedBytes.ofNat (128 * 256 ^ 255 + 7 * 256 + 255)
private def zeroBloomBytes : List UInt8 := List.replicate 256 0
private def sampleBloomBytes : List UInt8 := [128] ++ List.replicate 253 0 ++ [7, 255]

private def firstTopic : Hash32 :=
  Hash32.ofBytes32 <|
    FixedBytes.ofNat 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
private def secondTopic : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (255 * 256 ^ 31))

private def firstLog : Log :=
  ⟨Address.ofNat 0x000102030405060708090a0b0c0d0e0f10111213,
    #[firstTopic, secondTopic, firstTopic], Bytes.ofList [0, 255, 0]⟩
private def secondLog : Log := ⟨Address.ofNat 0, #[], Bytes.ofList []⟩

private def expectedLogs : List LogFields :=
  let firstTopicBytes := (List.range 32).map UInt8.ofNat
  let secondTopicBytes := 255 :: List.replicate 31 0
  let first : LogFields :=
    ((List.range 20).map UInt8.ofNat, [firstTopicBytes, secondTopicBytes, firstTopicBytes],
      [0, 255, 0])
  [first, (List.replicate 20 0, [], []), first]

private def sampleGas : Nat := 2 ^ 256 + 9
private def sample : Receipt :=
  Receipt.mk true sampleGas sampleBloom #[firstLog, secondLog, firstLog]

#guard fields (Receipt.mk false 0 zeroBloom #[]) == (false, 0, zeroBloomBytes, [])
#guard fields sample ==
  (true, 115792089237316195423570985008687907853269984665640564039457584007913129639945,
    sampleBloomBytes, expectedLogs)

#guard fields { sample with succeeded := false } ==
  (false, sampleGas, sampleBloomBytes, expectedLogs)
#guard fields { sample with cumulativeGasUsed := 0 } == (true, 0, sampleBloomBytes, expectedLogs)
#guard fields { sample with bloom := zeroBloom } == (true, sampleGas, zeroBloomBytes, expectedLogs)
#guard fields { sample with logs := #[] } == (true, sampleGas, sampleBloomBytes, [])

private def legacyFields (encoded : EncodedReceipt) : Option ReceiptFields :=
  match encoded with
  | .legacy r => some (fields r)
  | .typed _ => none

private def typedBytes (encoded : EncodedReceipt) : Option (List UInt8) :=
  match encoded with
  | .legacy _ => none
  | .typed b => some b.data.toList

#guard legacyFields (.legacy sample) == some (true, sampleGas, sampleBloomBytes, expectedLogs)
#guard typedBytes (.typed ⟨#[]⟩) == some []
#guard typedBytes (.typed ⟨#[255, 0, 192, 0]⟩) == some [255, 0, 192, 0]

end STFSpec.Conformance.Block.ReceiptGuards
