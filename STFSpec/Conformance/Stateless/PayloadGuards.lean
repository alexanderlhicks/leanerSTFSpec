/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Whole raw payload and request controls

Library `EthConformance`. Private complete observations retain every byte, word and nested value.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

open STFSpec STFSpec.Base STFSpec.Stateless

set_option maxRecDepth 4096


private def fixed (n : Nat) (xs : List UInt8) (h : xs.length = n) : FixedBytes n :=
  (FixedBytes.ofBytes? (Bytes.ofList xs)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact FixedBytes.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofList, h]))

private def address (xs : List UInt8) (h : xs.length = 20) : Address :=
  (Address.ofBytes? (Bytes.ofList xs)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact Address.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofList, h]))

private def hash (xs : List UInt8) (h : xs.length = 32) : Hash32 :=
  (Hash32.ofBytes? (Bytes.ofList xs)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact Hash32.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofList, h]))

private def word64 (n : Nat) (_h : n < 2 ^ 64) : U64 := U64.ofNat n
private def word256 (n : Nat) (_h : n < 2 ^ 256) : U256 := U256.ofNat n
private theorem word64_observe (n : Nat) (h : n < 2 ^ 64) :
    (word64 n h).toNat = n := U64.toNat_ofNat_of_lt h
private theorem word256_observe (n : Nat) (h : n < 2 ^ 256) :
    (word256 n h).toNat = n := U256.toNat_ofNat_of_lt h

private abbrev WithdrawalObservation := Nat × Nat × List UInt8 × Nat

private def withdrawalObserve (r : Block.Withdrawal) : WithdrawalObservation :=
  (r.index.toNat, r.validatorIndex.toNat, r.address.toBytes.toList, r.amount.toNat)

private abbrev DepositRequestObservation := List UInt8 × List UInt8 × Nat × List UInt8 × Nat

private def depositRequestObserve (r : DepositRequest) : DepositRequestObservation :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList, r.index.toNat)

private abbrev WithdrawalRequestObservation := List UInt8 × List UInt8 × Nat

private def withdrawalRequestObserve (r : WithdrawalRequest) : WithdrawalRequestObservation :=
  (r.sourceAddress.toBytes.toList, r.validatorPubkey.toBytes.toList, r.amount.toNat)

private abbrev ConsolidationRequestObservation := List UInt8 × List UInt8 × List UInt8

private def consolidationRequestObserve (r : ConsolidationRequest) :
  ConsolidationRequestObservation :=
  (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList)

private abbrev BuilderDepositRequestObservation := List UInt8 × List UInt8 × Nat × List UInt8

private def builderDepositRequestObserve (r : BuilderDepositRequest) :
  BuilderDepositRequestObservation :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList)

private abbrev BuilderExitRequestObservation := List UInt8 × List UInt8

private def builderExitRequestObserve (r : BuilderExitRequest) : BuilderExitRequestObservation :=
  (r.sourceAddress.toBytes.toList, r.pubkey.toBytes.toList)

private abbrev ExecutionRequestsObservation := List (DepositRequestObservation) × List
  (WithdrawalRequestObservation) × List (ConsolidationRequestObservation) × List
  (BuilderDepositRequestObservation) × List (BuilderExitRequestObservation)

private def executionRequestsObserve (r : ExecutionRequests) : ExecutionRequestsObservation :=
  ((r.deposits.toList.map depositRequestObserve), (r.withdrawals.toList.map
    withdrawalRequestObserve), (r.consolidations.toList.map consolidationRequestObserve),
    (r.builderDeposits.toList.map builderDepositRequestObserve), (r.builderExits.toList.map
    builderExitRequestObserve))

private abbrev ExecutionPayloadObservation := List UInt8 × List UInt8 × List UInt8 × List UInt8 ×
  List UInt8 × List UInt8 × Nat × Nat × Nat × Nat × List UInt8 × Nat × List UInt8 × List (List
  UInt8) × List (WithdrawalObservation) × Nat × Nat × List UInt8 × Nat

private def executionPayloadObserve (r : ExecutionPayload) : ExecutionPayloadObservation :=
  (r.parentHash.toBytes.toList, r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList,
    r.receiptsRoot.toBytes.toList, r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList,
    r.blockNumber.toNat, r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
    r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
    (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map
    withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray
    r.blockAccessList).toList, r.slotNumber.toNat)

private abbrev NewPayloadRequestObservation := ExecutionPayloadObservation × List (List UInt8) ×
  List UInt8 × ExecutionRequestsObservation

private def newPayloadRequestObserve (r : NewPayloadRequest) : NewPayloadRequestObservation :=
  (executionPayloadObserve r.executionPayload, (r.versionedHashes.toList.map (fun h ↦
    h.toBytes.toList)), r.parentBeaconBlockRoot.toBytes.toList, executionRequestsObserve
    r.executionRequests)

private def newPayloadRequestEqual (a b : NewPayloadRequestObservation) : Bool :=
  (a.1 == b.1) && (a.2.1 == b.2.1) && (a.2.2.1 == b.2.2.1) &&
    (a.2.2.2 == b.2.2.2)

private def withdrawalZero_indexExpected : Nat :=
  0

private def withdrawalZero_validatorIndexExpected : Nat :=
  0

private def withdrawalZero_addressExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def withdrawalZero_amountExpected : Nat :=
  0

private def withdrawalZero : Block.Withdrawal :=
  Block.Withdrawal.mk (word64 0 (by decide)) (word64 0 (by decide)) (address [0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (word64 0 (by decide))

private def withdrawalZeroExpected : WithdrawalObservation :=
  (withdrawalZero_indexExpected, withdrawalZero_validatorIndexExpected,
    withdrawalZero_addressExpected, withdrawalZero_amountExpected)

#guard withdrawalObserve withdrawalZero == withdrawalZeroExpected

private def withdrawalMax_indexExpected : Nat :=
  18446744073709551615

private def withdrawalMax_validatorIndexExpected : Nat :=
  18446744073709551615

private def withdrawalMax_addressExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def withdrawalMax_amountExpected : Nat :=
  18446744073709551615

private def withdrawalMax : Block.Withdrawal :=
  Block.Withdrawal.mk (word64 18446744073709551615 (by decide)) (word64 18446744073709551615 (by
    decide)) (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255] (by decide)) (word64 18446744073709551615 (by decide))

private def withdrawalMaxExpected : WithdrawalObservation :=
  (withdrawalMax_indexExpected, withdrawalMax_validatorIndexExpected,
    withdrawalMax_addressExpected, withdrawalMax_amountExpected)

#guard withdrawalObserve withdrawalMax == withdrawalMaxExpected

private def withdrawalA_indexExpected : Nat :=
  1234605616436508552

private def withdrawalA_validatorIndexExpected : Nat :=
  3340697550357611376

private def withdrawalA_addressExpected : List UInt8 :=
  [0, 112, 149, 186, 223, 4, 41, 78, 115, 152, 0, 226, 7, 44, 81, 118, 155, 192, 229, 0]

private def withdrawalA_amountExpected : Nat :=
  7552881418199817024

private def withdrawalA : Block.Withdrawal :=
  Block.Withdrawal.mk (word64 1234605616436508552 (by decide)) (word64 3340697550357611376 (by
    decide)) (address [0, 112, 149, 186, 223, 4, 41, 78, 115, 152, 0, 226, 7, 44, 81, 118, 155,
    192, 229, 0] (by decide)) (word64 7552881418199817024 (by decide))

private def withdrawalAExpected : WithdrawalObservation :=
  (withdrawalA_indexExpected, withdrawalA_validatorIndexExpected, withdrawalA_addressExpected,
    withdrawalA_amountExpected)

#guard withdrawalObserve withdrawalA == withdrawalAExpected

private def withdrawalB_indexExpected : Nat :=
  1234605616436508552

private def withdrawalB_validatorIndexExpected : Nat :=
  3340697550357611376

private def withdrawalB_addressExpected : List UInt8 :=
  [0, 183, 220, 1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115, 152, 189, 226, 7, 44, 0]

private def withdrawalB_amountExpected : Nat :=
  7552881418199817024

private def withdrawalB : Block.Withdrawal :=
  Block.Withdrawal.mk (word64 1234605616436508552 (by decide)) (word64 3340697550357611376 (by
    decide)) (address [0, 183, 220, 1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115, 152, 189, 226,
    7, 44, 0] (by decide)) (word64 7552881418199817024 (by decide))

private def withdrawalBExpected : WithdrawalObservation :=
  (withdrawalB_indexExpected, withdrawalB_validatorIndexExpected, withdrawalB_addressExpected,
    withdrawalB_amountExpected)

#guard withdrawalObserve withdrawalB == withdrawalBExpected

private def depositRequestZero_pubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def depositRequestZero_withdrawalCredentialsExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def depositRequestZero_amountExpected : Nat :=
  0

private def depositRequestZero_signatureExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0]

private def depositRequestZero_indexExpected : Nat :=
  0

private def depositRequestZero : DepositRequest :=
  DepositRequest.mk (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (fixed 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0] (by decide)) (word64 0 (by decide)) (fixed 96 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (word64 0 (by
    decide))

private def depositRequestZeroExpected : DepositRequestObservation :=
  (depositRequestZero_pubkeyExpected, depositRequestZero_withdrawalCredentialsExpected,
    depositRequestZero_amountExpected, depositRequestZero_signatureExpected,
    depositRequestZero_indexExpected)

#guard depositRequestObserve depositRequestZero == depositRequestZeroExpected

private def depositRequestMax_pubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def depositRequestMax_withdrawalCredentialsExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def depositRequestMax_amountExpected : Nat :=
  18446744073709551615

private def depositRequestMax_signatureExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def depositRequestMax_indexExpected : Nat :=
  18446744073709551615

private def depositRequestMax : DepositRequest :=
  DepositRequest.mk (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (fixed 32 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (word64 18446744073709551615 (by decide)) (fixed 96 [255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide)) (word64
    18446744073709551615 (by decide))

private def depositRequestMaxExpected : DepositRequestObservation :=
  (depositRequestMax_pubkeyExpected, depositRequestMax_withdrawalCredentialsExpected,
    depositRequestMax_amountExpected, depositRequestMax_signatureExpected,
    depositRequestMax_indexExpected)

#guard depositRequestObserve depositRequestMax == depositRequestMaxExpected

private def depositRequestA_pubkeyExpected : List UInt8 :=
  [0, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251,
    32, 69, 106, 143, 0, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 0]

private def depositRequestA_withdrawalCredentialsExpected : List UInt8 :=
  [0, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 0, 206, 243, 24, 61,
    98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 0]

private def depositRequestA_amountExpected : Nat :=
  8569615455265177008

private def depositRequestA_signatureExpected : List UInt8 :=
  [0, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128,
    165, 202, 239, 20, 57, 94, 0, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137,
    174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
    146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 0]

private def depositRequestA_indexExpected : Nat :=
  12781799323107382656

private def depositRequestA : DepositRequest :=
  DepositRequest.mk (fixed 48 [0, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66,
    103, 140, 177, 214, 251, 32, 69, 106, 143, 0, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75,
    112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 0] (by decide)) (fixed 32 [0, 126, 163,
    200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 0, 206, 243, 24, 61, 98, 135, 172,
    209, 246, 27, 64, 101, 138, 175, 0] (by decide)) (word64 8569615455265177008 (by decide))
    (fixed 96 [0, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45,
    82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17,
    54, 91, 128, 165, 202, 239, 20, 57, 94, 0, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26,
    63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254,
    35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 0] (by decide)) (word64
    12781799323107382656 (by decide))

private def depositRequestAExpected : DepositRequestObservation :=
  (depositRequestA_pubkeyExpected, depositRequestA_withdrawalCredentialsExpected,
    depositRequestA_amountExpected, depositRequestA_signatureExpected,
    depositRequestA_indexExpected)

#guard depositRequestObserve depositRequestA == depositRequestAExpected

private def depositRequestB_pubkeyExpected : List UInt8 :=
  [0, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103,
    140, 177, 214, 0, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112,
    149, 186, 223, 4, 41, 0]

private def depositRequestB_withdrawalCredentialsExpected : List UInt8 :=
  [0, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 0, 21, 58, 95, 132,
    169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 0]

private def depositRequestB_amountExpected : Nat :=
  8569615455265177008

private def depositRequestB_signatureExpected : List UInt8 :=
  [0, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190,
    227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199,
    236, 17, 54, 91, 128, 165, 0, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208,
    245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 0]

private def depositRequestB_indexExpected : Nat :=
  12781799323107382656

private def depositRequestB : DepositRequest :=
  DepositRequest.mk (fixed 48 [0, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137,
    174, 211, 248, 29, 66, 103, 140, 177, 214, 0, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
    146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 0] (by decide)) (fixed 32 [0, 197, 234,
    15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 0, 21, 58, 95, 132, 169, 206, 243,
    24, 61, 98, 135, 172, 209, 246, 0] (by decide)) (word64 8569615455265177008 (by decide))
    (fixed 96 [0, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116,
    153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125,
    162, 199, 236, 17, 54, 91, 128, 165, 0, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134,
    171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106,
    143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 0] (by decide)) (word64
    12781799323107382656 (by decide))

private def depositRequestBExpected : DepositRequestObservation :=
  (depositRequestB_pubkeyExpected, depositRequestB_withdrawalCredentialsExpected,
    depositRequestB_amountExpected, depositRequestB_signatureExpected,
    depositRequestB_indexExpected)

#guard depositRequestObserve depositRequestB == depositRequestBExpected

private def withdrawalRequestZero_sourceAddressExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def withdrawalRequestZero_validatorPubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def withdrawalRequestZero_amountExpected : Nat :=
  0

private def withdrawalRequestZero : WithdrawalRequest :=
  WithdrawalRequest.mk (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by
    decide)) (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (word64 0
    (by decide))

private def withdrawalRequestZeroExpected : WithdrawalRequestObservation :=
  (withdrawalRequestZero_sourceAddressExpected, withdrawalRequestZero_validatorPubkeyExpected,
    withdrawalRequestZero_amountExpected)

#guard withdrawalRequestObserve withdrawalRequestZero == withdrawalRequestZeroExpected

private def withdrawalRequestMax_sourceAddressExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def withdrawalRequestMax_validatorPubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def withdrawalRequestMax_amountExpected : Nat :=
  18446744073709551615

private def withdrawalRequestMax : WithdrawalRequest :=
  WithdrawalRequest.mk (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255] (by decide)) (fixed 48 [255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255] (by decide)) (word64 18446744073709551615 (by decide))

private def withdrawalRequestMaxExpected : WithdrawalRequestObservation :=
  (withdrawalRequestMax_sourceAddressExpected, withdrawalRequestMax_validatorPubkeyExpected,
    withdrawalRequestMax_amountExpected)

#guard withdrawalRequestObserve withdrawalRequestMax == withdrawalRequestMaxExpected

private def withdrawalRequestA_sourceAddressExpected : List UInt8 :=
  [0, 140, 177, 214, 251, 32, 69, 106, 143, 180, 0, 254, 35, 72, 109, 146, 183, 220, 1, 0]

private def withdrawalRequestA_validatorPubkeyExpected : List UInt8 :=
  [0, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104,
    141, 178, 215, 0, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113,
    150, 187, 224, 5, 42, 0]

private def withdrawalRequestA_amountExpected : Nat :=
  11692441426251639816

private def withdrawalRequestA : WithdrawalRequest :=
  WithdrawalRequest.mk (address [0, 140, 177, 214, 251, 32, 69, 106, 143, 180, 0, 254, 35, 72,
    109, 146, 183, 220, 1, 0] (by decide)) (fixed 48 [0, 169, 206, 243, 24, 61, 98, 135, 172, 209,
    246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 0, 33, 70, 107, 144, 181,
    218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 0] (by decide))
    (word64 11692441426251639816 (by decide))

private def withdrawalRequestAExpected : WithdrawalRequestObservation :=
  (withdrawalRequestA_sourceAddressExpected, withdrawalRequestA_validatorPubkeyExpected,
    withdrawalRequestA_amountExpected)

#guard withdrawalRequestObserve withdrawalRequestA == withdrawalRequestAExpected

private def withdrawalRequestB_sourceAddressExpected : List UInt8 :=
  [0, 211, 248, 29, 66, 103, 140, 177, 214, 251, 0, 69, 106, 143, 180, 217, 254, 35, 72, 0]

private def withdrawalRequestB_validatorPubkeyExpected : List UInt8 :=
  [0, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175,
    212, 249, 30, 0, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147,
    184, 221, 2, 39, 76, 113, 0]

private def withdrawalRequestB_amountExpected : Nat :=
  11692441426251639816

private def withdrawalRequestB : WithdrawalRequest :=
  WithdrawalRequest.mk (address [0, 211, 248, 29, 66, 103, 140, 177, 214, 251, 0, 69, 106, 143,
    180, 217, 254, 35, 72, 0] (by decide)) (fixed 48 [0, 240, 21, 58, 95, 132, 169, 206, 243, 24,
    61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 0, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 0] (by decide))
    (word64 11692441426251639816 (by decide))

private def withdrawalRequestBExpected : WithdrawalRequestObservation :=
  (withdrawalRequestB_sourceAddressExpected, withdrawalRequestB_validatorPubkeyExpected,
    withdrawalRequestB_amountExpected)

#guard withdrawalRequestObserve withdrawalRequestB == withdrawalRequestBExpected

private def consolidationRequestZero_sourceAddressExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def consolidationRequestZero_sourcePubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def consolidationRequestZero_targetPubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def consolidationRequestZero : ConsolidationRequest :=
  ConsolidationRequest.mk (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    (by decide)) (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (fixed
    48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def consolidationRequestZeroExpected : ConsolidationRequestObservation :=
  (consolidationRequestZero_sourceAddressExpected, consolidationRequestZero_sourcePubkeyExpected,
    consolidationRequestZero_targetPubkeyExpected)

#guard consolidationRequestObserve consolidationRequestZero == consolidationRequestZeroExpected

private def consolidationRequestMax_sourceAddressExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def consolidationRequestMax_sourcePubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def consolidationRequestMax_targetPubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def consolidationRequestMax : ConsolidationRequest :=
  ConsolidationRequest.mk (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255] (by decide)) (fixed 48 [255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255] (by decide)) (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]
    (by decide))

private def consolidationRequestMaxExpected : ConsolidationRequestObservation :=
  (consolidationRequestMax_sourceAddressExpected, consolidationRequestMax_sourcePubkeyExpected,
    consolidationRequestMax_targetPubkeyExpected)

#guard consolidationRequestObserve consolidationRequestMax == consolidationRequestMaxExpected

private def consolidationRequestA_sourceAddressExpected : List UInt8 :=
  [0, 183, 220, 1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115, 152, 189, 226, 7, 44, 0]

private def consolidationRequestA_sourcePubkeyExpected : List UInt8 :=
  [0, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110,
    147, 184, 221, 2, 0, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119,
    156, 193, 230, 11, 48, 85, 0]

private def consolidationRequestA_targetPubkeyExpected : List UInt8 :=
  [0, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
    213, 250, 31, 0, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148,
    185, 222, 3, 40, 77, 114, 0]

private def consolidationRequestA : ConsolidationRequest :=
  ConsolidationRequest.mk (address [0, 183, 220, 1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115,
    152, 189, 226, 7, 44, 0] (by decide)) (fixed 48 [0, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 0, 76, 113, 150, 187, 224, 5,
    42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 0] (by decide)) (fixed
    48 [0, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139,
    176, 213, 250, 31, 0, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111,
    148, 185, 222, 3, 40, 77, 114, 0] (by decide))

private def consolidationRequestAExpected : ConsolidationRequestObservation :=
  (consolidationRequestA_sourceAddressExpected, consolidationRequestA_sourcePubkeyExpected,
    consolidationRequestA_targetPubkeyExpected)

#guard consolidationRequestObserve consolidationRequestA == consolidationRequestAExpected

private def consolidationRequestB_sourceAddressExpected : List UInt8 :=
  [0, 254, 35, 72, 109, 146, 183, 220, 1, 38, 0, 112, 149, 186, 223, 4, 41, 78, 115, 0]

private def consolidationRequestB_sourcePubkeyExpected : List UInt8 :=
  [0, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181,
    218, 255, 36, 73, 0, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190,
    227, 8, 45, 82, 119, 156, 0]

private def consolidationRequestB_targetPubkeyExpected : List UInt8 :=
  [0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247,
    28, 65, 102, 0, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0,
    37, 74, 111, 148, 185, 0]

private def consolidationRequestB : ConsolidationRequest :=
  ConsolidationRequest.mk (address [0, 254, 35, 72, 109, 146, 183, 220, 1, 38, 0, 112, 149, 186,
    223, 4, 41, 78, 115, 0] (by decide)) (fixed 48 [0, 27, 64, 101, 138, 175, 212, 249, 30, 67,
    104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 0, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 0] (by decide)) (fixed
    48 [0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210,
    247, 28, 65, 102, 0, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182,
    219, 0, 37, 74, 111, 148, 185, 0] (by decide))

private def consolidationRequestBExpected : ConsolidationRequestObservation :=
  (consolidationRequestB_sourceAddressExpected, consolidationRequestB_sourcePubkeyExpected,
    consolidationRequestB_targetPubkeyExpected)

#guard consolidationRequestObserve consolidationRequestB == consolidationRequestBExpected

private def builderDepositRequestZero_pubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def builderDepositRequestZero_withdrawalCredentialsExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def builderDepositRequestZero_amountExpected : Nat :=
  0

private def builderDepositRequestZero_signatureExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0]

private def builderDepositRequestZero : BuilderDepositRequest :=
  BuilderDepositRequest.mk (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by
    decide)) (fixed 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] (by decide)) (word64 0 (by decide)) (fixed 96 [0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def builderDepositRequestZeroExpected : BuilderDepositRequestObservation :=
  (builderDepositRequestZero_pubkeyExpected,
    builderDepositRequestZero_withdrawalCredentialsExpected,
    builderDepositRequestZero_amountExpected, builderDepositRequestZero_signatureExpected)

#guard builderDepositRequestObserve builderDepositRequestZero == builderDepositRequestZeroExpected

private def builderDepositRequestMax_pubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def builderDepositRequestMax_withdrawalCredentialsExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def builderDepositRequestMax_amountExpected : Nat :=
  18446744073709551615

private def builderDepositRequestMax_signatureExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def builderDepositRequestMax : BuilderDepositRequest :=
  BuilderDepositRequest.mk (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by
    decide)) (fixed 32 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by
    decide)) (word64 18446744073709551615 (by decide)) (fixed 96 [255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))

private def builderDepositRequestMaxExpected : BuilderDepositRequestObservation :=
  (builderDepositRequestMax_pubkeyExpected,
    builderDepositRequestMax_withdrawalCredentialsExpected,
    builderDepositRequestMax_amountExpected, builderDepositRequestMax_signatureExpected)

#guard builderDepositRequestObserve builderDepositRequestMax == builderDepositRequestMaxExpected

private def builderDepositRequestA_pubkeyExpected : List UInt8 :=
  [0, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161,
    198, 235, 16, 0, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170,
    207, 244, 25, 62, 99, 0]

private def builderDepositRequestA_withdrawalCredentialsExpected : List UInt8 :=
  [0, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0, 79, 116, 153, 190,
    227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 0]

private def builderDepositRequestA_amountExpected : Nat :=
  17938093368224565432

private def builderDepositRequestA_signatureExpected : List UInt8 :=
  [0, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248,
    29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220,
    1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229,
    10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201,
    238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0]

private def builderDepositRequestA : BuilderDepositRequest :=
  BuilderDepositRequest.mk (fixed 48 [0, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158,
    195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 0, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167,
    204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 0] (by decide)) (fixed 32 [0, 255, 36,
    73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0, 79, 116, 153, 190, 227, 8, 45,
    82, 119, 156, 193, 230, 11, 48, 0] (by decide)) (word64 17938093368224565432 (by decide))
    (fixed 96 [0, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137,
    174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
    146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 0, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118,
    155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90,
    127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0] (by decide))

private def builderDepositRequestAExpected : BuilderDepositRequestObservation :=
  (builderDepositRequestA_pubkeyExpected, builderDepositRequestA_withdrawalCredentialsExpected,
    builderDepositRequestA_amountExpected, builderDepositRequestA_signatureExpected)

#guard builderDepositRequestObserve builderDepositRequestA == builderDepositRequestAExpected

private def builderDepositRequestB_pubkeyExpected : List UInt8 :=
  [0, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232,
    13, 50, 87, 0, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241,
    22, 59, 96, 133, 170, 0]

private def builderDepositRequestB_withdrawalCredentialsExpected : List UInt8 :=
  [0, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 0, 150, 187, 224, 5, 42,
    79, 116, 153, 190, 227, 8, 45, 82, 119, 0]

private def builderDepositRequestB_amountExpected : Nat :=
  17938093368224565432

private def builderDepositRequestB_signatureExpected : List UInt8 :=
  [0, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63,
    100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35,
    72, 109, 146, 183, 220, 1, 38, 0, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44,
    81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16,
    53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 0]

private def builderDepositRequestB : BuilderDepositRequest :=
  BuilderDepositRequest.mk (fixed 48 [0, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192,
    229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 0, 161, 198, 235, 16, 53, 90, 127, 164, 201,
    238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0] (by decide)) (fixed 32 [0, 70,
    107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 0, 150, 187, 224, 5, 42, 79,
    116, 153, 190, 227, 8, 45, 82, 119, 0] (by decide)) (word64 17938093368224565432 (by decide))
    (fixed 96 [0, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208,
    245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 0, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189,
    226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198,
    235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 0] (by decide))

private def builderDepositRequestBExpected : BuilderDepositRequestObservation :=
  (builderDepositRequestB_pubkeyExpected, builderDepositRequestB_withdrawalCredentialsExpected,
    builderDepositRequestB_amountExpected, builderDepositRequestB_signatureExpected)

#guard builderDepositRequestObserve builderDepositRequestB == builderDepositRequestBExpected

private def builderExitRequestZero_sourceAddressExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def builderExitRequestZero_pubkeyExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def builderExitRequestZero : BuilderExitRequest :=
  BuilderExitRequest.mk (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by
    decide)) (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def builderExitRequestZeroExpected : BuilderExitRequestObservation :=
  (builderExitRequestZero_sourceAddressExpected, builderExitRequestZero_pubkeyExpected)

#guard builderExitRequestObserve builderExitRequestZero == builderExitRequestZeroExpected

private def builderExitRequestMax_sourceAddressExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def builderExitRequestMax_pubkeyExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def builderExitRequestMax : BuilderExitRequest :=
  BuilderExitRequest.mk (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255] (by decide)) (fixed 48 [255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255] (by decide))

private def builderExitRequestMaxExpected : BuilderExitRequestObservation :=
  (builderExitRequestMax_sourceAddressExpected, builderExitRequestMax_pubkeyExpected)

#guard builderExitRequestObserve builderExitRequestMax == builderExitRequestMaxExpected

private def builderExitRequestA_sourceAddressExpected : List UInt8 :=
  [0, 13, 50, 87, 124, 161, 198, 235, 16, 53, 0, 127, 164, 201, 238, 19, 56, 93, 130, 0]

private def builderExitRequestA_pubkeyExpected : List UInt8 :=
  [0, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 0, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242,
    23, 60, 97, 134, 171, 0]

private def builderExitRequestA : BuilderExitRequest :=
  BuilderExitRequest.mk (address [0, 13, 50, 87, 124, 161, 198, 235, 16, 53, 0, 127, 164, 201,
    238, 19, 56, 93, 130, 0] (by decide)) (fixed 48 [0, 42, 79, 116, 153, 190, 227, 8, 45, 82,
    119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 0, 162, 199, 236, 17, 54, 91,
    128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 0] (by decide))

private def builderExitRequestAExpected : BuilderExitRequestObservation :=
  (builderExitRequestA_sourceAddressExpected, builderExitRequestA_pubkeyExpected)

#guard builderExitRequestObserve builderExitRequestA == builderExitRequestAExpected

private def builderExitRequestB_sourceAddressExpected : List UInt8 :=
  [0, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0, 198, 235, 16, 53, 90, 127, 164, 201, 0]

private def builderExitRequestB_pubkeyExpected : List UInt8 :=
  [0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48,
    85, 122, 159, 0, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57,
    94, 131, 168, 205, 242, 0]

private def builderExitRequestB : BuilderExitRequest :=
  BuilderExitRequest.mk (address [0, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0, 198, 235, 16, 53,
    90, 127, 164, 201, 0] (by decide)) (fixed 48 [0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190,
    227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 0, 233, 14, 51, 88, 125, 162, 199,
    236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 0] (by decide))

private def builderExitRequestBExpected : BuilderExitRequestObservation :=
  (builderExitRequestB_sourceAddressExpected, builderExitRequestB_pubkeyExpected)

#guard builderExitRequestObserve builderExitRequestB == builderExitRequestBExpected

private def executionRequestsZero_depositsExpected : List DepositRequestObservation :=
  []

private def executionRequestsZero_withdrawalsExpected : List WithdrawalRequestObservation :=
  []

private def executionRequestsZero_consolidationsExpected : List ConsolidationRequestObservation :=
  []

private def executionRequestsZero_builderDepositsExpected : List BuilderDepositRequestObservation
  :=
  []

private def executionRequestsZero_builderExitsExpected : List BuilderExitRequestObservation :=
  []

private def executionRequestsZero : ExecutionRequests :=
  ExecutionRequests.mk #[] #[] #[] #[] #[]

private def executionRequestsZeroExpected : ExecutionRequestsObservation :=
  (executionRequestsZero_depositsExpected, executionRequestsZero_withdrawalsExpected,
    executionRequestsZero_consolidationsExpected, executionRequestsZero_builderDepositsExpected,
    executionRequestsZero_builderExitsExpected)

#guard executionRequestsObserve executionRequestsZero == executionRequestsZeroExpected

private def executionRequestsMax_depositsExpected : List DepositRequestObservation :=
  [depositRequestMaxExpected]

private def executionRequestsMax_withdrawalsExpected : List WithdrawalRequestObservation :=
  [withdrawalRequestMaxExpected]

private def executionRequestsMax_consolidationsExpected : List ConsolidationRequestObservation :=
  [consolidationRequestMaxExpected]

private def executionRequestsMax_builderDepositsExpected : List BuilderDepositRequestObservation
  :=
  [builderDepositRequestMaxExpected]

private def executionRequestsMax_builderExitsExpected : List BuilderExitRequestObservation :=
  [builderExitRequestMaxExpected]

private def executionRequestsMax : ExecutionRequests :=
  ExecutionRequests.mk #[depositRequestMax] #[withdrawalRequestMax] #[consolidationRequestMax]
    #[builderDepositRequestMax] #[builderExitRequestMax]

private def executionRequestsMaxExpected : ExecutionRequestsObservation :=
  (executionRequestsMax_depositsExpected, executionRequestsMax_withdrawalsExpected,
    executionRequestsMax_consolidationsExpected, executionRequestsMax_builderDepositsExpected,
    executionRequestsMax_builderExitsExpected)

#guard executionRequestsObserve executionRequestsMax == executionRequestsMaxExpected

private def executionRequestsA_depositsExpected : List DepositRequestObservation :=
  [depositRequestAExpected]

private def executionRequestsA_withdrawalsExpected : List WithdrawalRequestObservation :=
  [withdrawalRequestAExpected, withdrawalRequestBExpected, withdrawalRequestAExpected]

private def executionRequestsA_consolidationsExpected : List ConsolidationRequestObservation :=
  [consolidationRequestAExpected, consolidationRequestBExpected, consolidationRequestAExpected,
    consolidationRequestBExpected, consolidationRequestAExpected]

private def executionRequestsA_builderDepositsExpected : List BuilderDepositRequestObservation :=
  [builderDepositRequestAExpected, builderDepositRequestBExpected, builderDepositRequestAExpected,
    builderDepositRequestBExpected, builderDepositRequestAExpected,
    builderDepositRequestBExpected, builderDepositRequestAExpected]

private def executionRequestsA_builderExitsExpected : List BuilderExitRequestObservation :=
  [builderExitRequestAExpected, builderExitRequestBExpected, builderExitRequestAExpected,
    builderExitRequestBExpected, builderExitRequestAExpected, builderExitRequestBExpected,
    builderExitRequestAExpected, builderExitRequestBExpected, builderExitRequestAExpected]

private def executionRequestsA : ExecutionRequests :=
  ExecutionRequests.mk #[depositRequestA] #[withdrawalRequestA, withdrawalRequestB,
    withdrawalRequestA] #[consolidationRequestA, consolidationRequestB, consolidationRequestA,
    consolidationRequestB, consolidationRequestA] #[builderDepositRequestA,
    builderDepositRequestB, builderDepositRequestA, builderDepositRequestB,
    builderDepositRequestA, builderDepositRequestB, builderDepositRequestA] #[builderExitRequestA,
    builderExitRequestB, builderExitRequestA, builderExitRequestB, builderExitRequestA,
    builderExitRequestB, builderExitRequestA, builderExitRequestB, builderExitRequestA]

private def executionRequestsAExpected : ExecutionRequestsObservation :=
  (executionRequestsA_depositsExpected, executionRequestsA_withdrawalsExpected,
    executionRequestsA_consolidationsExpected, executionRequestsA_builderDepositsExpected,
    executionRequestsA_builderExitsExpected)

#guard executionRequestsObserve executionRequestsA == executionRequestsAExpected

private def executionRequestsB_depositsExpected : List DepositRequestObservation :=
  [depositRequestBExpected, depositRequestBExpected]

private def executionRequestsB_withdrawalsExpected : List WithdrawalRequestObservation :=
  [withdrawalRequestBExpected, withdrawalRequestBExpected, withdrawalRequestAExpected]

private def executionRequestsB_consolidationsExpected : List ConsolidationRequestObservation :=
  [consolidationRequestBExpected, consolidationRequestBExpected, consolidationRequestAExpected,
    consolidationRequestAExpected]

private def executionRequestsB_builderDepositsExpected : List BuilderDepositRequestObservation :=
  [builderDepositRequestBExpected, builderDepositRequestBExpected, builderDepositRequestAExpected,
    builderDepositRequestAExpected, builderDepositRequestAExpected]

private def executionRequestsB_builderExitsExpected : List BuilderExitRequestObservation :=
  [builderExitRequestBExpected, builderExitRequestBExpected, builderExitRequestAExpected,
    builderExitRequestAExpected, builderExitRequestAExpected, builderExitRequestAExpected]

private def executionRequestsB : ExecutionRequests :=
  ExecutionRequests.mk #[depositRequestB, depositRequestB] #[withdrawalRequestB,
    withdrawalRequestB, withdrawalRequestA] #[consolidationRequestB, consolidationRequestB,
    consolidationRequestA, consolidationRequestA] #[builderDepositRequestB,
    builderDepositRequestB, builderDepositRequestA, builderDepositRequestA,
    builderDepositRequestA] #[builderExitRequestB, builderExitRequestB, builderExitRequestA,
    builderExitRequestA, builderExitRequestA, builderExitRequestA]

private def executionRequestsBExpected : ExecutionRequestsObservation :=
  (executionRequestsB_depositsExpected, executionRequestsB_withdrawalsExpected,
    executionRequestsB_consolidationsExpected, executionRequestsB_builderDepositsExpected,
    executionRequestsB_builderExitsExpected)

#guard executionRequestsObserve executionRequestsB == executionRequestsBExpected

private def executionPayloadZero_parentHashExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_feeRecipientExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_stateRootExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_receiptsRootExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_logsBloomExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_prevRandaoExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_blockNumberExpected : Nat :=
  0

private def executionPayloadZero_gasLimitExpected : Nat :=
  0

private def executionPayloadZero_gasUsedExpected : Nat :=
  0

private def executionPayloadZero_timestampExpected : Nat :=
  0

private def executionPayloadZero_extraDataExpected : List UInt8 :=
  []

private def executionPayloadZero_baseFeePerGasExpected : Nat :=
  0

private def executionPayloadZero_blockHashExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def executionPayloadZero_transactionsExpected : List (List UInt8) :=
  []

private def executionPayloadZero_withdrawalsExpected : List WithdrawalObservation :=
  []

private def executionPayloadZero_blobGasUsedExpected : Nat :=
  0

private def executionPayloadZero_excessBlobGasExpected : Nat :=
  0

private def executionPayloadZero_blockAccessListExpected : List UInt8 :=
  []

private def executionPayloadZero_slotNumberExpected : Nat :=
  0

private def executionPayloadZero : ExecutionPayload :=
  ExecutionPayload.mk (hash [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] (by decide)) (hash [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (hash [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (fixed 256 [0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0] (by decide)) (fixed 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) (word64 0 (by decide)) (word64 0 (by
    decide)) (word64 0 (by decide)) (word64 0 (by decide)) ⟨#[]⟩ (word256 0 (by decide)) (hash [0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    (by decide)) #[] #[] (word64 0 (by decide)) (word64 0 (by decide)) ⟨#[]⟩ (word64 0 (by
    decide))

private def executionPayloadZeroExpected : ExecutionPayloadObservation :=
  (executionPayloadZero_parentHashExpected, executionPayloadZero_feeRecipientExpected,
    executionPayloadZero_stateRootExpected, executionPayloadZero_receiptsRootExpected,
    executionPayloadZero_logsBloomExpected, executionPayloadZero_prevRandaoExpected,
    executionPayloadZero_blockNumberExpected, executionPayloadZero_gasLimitExpected,
    executionPayloadZero_gasUsedExpected, executionPayloadZero_timestampExpected,
    executionPayloadZero_extraDataExpected, executionPayloadZero_baseFeePerGasExpected,
    executionPayloadZero_blockHashExpected, executionPayloadZero_transactionsExpected,
    executionPayloadZero_withdrawalsExpected, executionPayloadZero_blobGasUsedExpected,
    executionPayloadZero_excessBlobGasExpected, executionPayloadZero_blockAccessListExpected,
    executionPayloadZero_slotNumberExpected)

#guard executionPayloadObserve executionPayloadZero == executionPayloadZeroExpected

private def executionPayloadMax_parentHashExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_feeRecipientExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]

private def executionPayloadMax_stateRootExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_receiptsRootExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_logsBloomExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_prevRandaoExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_blockNumberExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_gasLimitExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_gasUsedExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_timestampExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_extraDataExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255]

private def executionPayloadMax_baseFeePerGasExpected : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

private def executionPayloadMax_blockHashExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_transactionsExpected : List (List UInt8) :=
  [[255]]

private def executionPayloadMax_withdrawalsExpected : List WithdrawalObservation :=
  [withdrawalMaxExpected]

private def executionPayloadMax_blobGasUsedExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_excessBlobGasExpected : Nat :=
  18446744073709551615

private def executionPayloadMax_blockAccessListExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255]

private def executionPayloadMax_slotNumberExpected : Nat :=
  18446744073709551615

private def executionPayloadMax : ExecutionPayload :=
  ExecutionPayload.mk (hash [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by
    decide)) (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255] (by decide)) (hash [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255] (by decide)) (hash [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255] (by decide)) (fixed 256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide)) (fixed
    32 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide)) (word64
    18446744073709551615 (by decide)) (word64 18446744073709551615 (by decide)) (word64
    18446744073709551615 (by decide)) (word64 18446744073709551615 (by decide)) ⟨#[255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255]⟩ (word256 115792089237316195423570985008687907853269984665640564039457584007913129639935
    (by decide)) (hash [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by
    decide)) #[⟨#[255]⟩] #[withdrawalMax] (word64 18446744073709551615 (by decide)) (word64
    18446744073709551615 (by decide)) ⟨#[255, 255, 255, 255, 255, 255, 255]⟩ (word64
    18446744073709551615 (by decide))

private def executionPayloadMaxExpected : ExecutionPayloadObservation :=
  (executionPayloadMax_parentHashExpected, executionPayloadMax_feeRecipientExpected,
    executionPayloadMax_stateRootExpected, executionPayloadMax_receiptsRootExpected,
    executionPayloadMax_logsBloomExpected, executionPayloadMax_prevRandaoExpected,
    executionPayloadMax_blockNumberExpected, executionPayloadMax_gasLimitExpected,
    executionPayloadMax_gasUsedExpected, executionPayloadMax_timestampExpected,
    executionPayloadMax_extraDataExpected, executionPayloadMax_baseFeePerGasExpected,
    executionPayloadMax_blockHashExpected, executionPayloadMax_transactionsExpected,
    executionPayloadMax_withdrawalsExpected, executionPayloadMax_blobGasUsedExpected,
    executionPayloadMax_excessBlobGasExpected, executionPayloadMax_blockAccessListExpected,
    executionPayloadMax_slotNumberExpected)

#guard executionPayloadObserve executionPayloadMax == executionPayloadMaxExpected

private def executionPayloadA_parentHashExpected : List UInt8 :=
  [0, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 0, 179, 216, 253, 34,
    71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 0]

private def executionPayloadA_feeRecipientExpected : List UInt8 :=
  [0, 128, 165, 202, 239, 20, 57, 94, 131, 168, 0, 242, 23, 60, 97, 134, 171, 208, 245, 0]

private def executionPayloadA_stateRootExpected : List UInt8 :=
  [0, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 0, 237, 18, 55, 92,
    129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 0]

private def executionPayloadA_receiptsRootExpected : List UInt8 :=
  [0, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 0, 10, 47, 84, 121, 158,
    195, 232, 13, 50, 87, 124, 161, 198, 235, 0]

private def executionPayloadA_logsBloomExpected : List UInt8 :=
  [0, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150,
    187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159,
    196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131,
    168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103,
    140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75,
    112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 0, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93,
    130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65,
    102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37,
    74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46,
    83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18,
    55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246,
    27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 0]

private def executionPayloadA_prevRandaoExpected : List UInt8 :=
  [0, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 0, 68, 105, 142, 179,
    216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 0]

private def executionPayloadA_blockNumberExpected : Nat :=
  17284194943158813537

private def executionPayloadA_gasLimitExpected : Nat :=
  1

private def executionPayloadA_gasUsedExpected : Nat :=
  18446744073709551615

private def executionPayloadA_timestampExpected : Nat :=
  0

private def executionPayloadA_extraDataExpected : List UInt8 :=
  [0, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 0,
    105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 0]

private def executionPayloadA_baseFeePerGasExpected : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

private def executionPayloadA_blockHashExpected : List UInt8 :=
  [0, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 0, 15, 52, 89, 126, 163,
    200, 237, 18, 55, 92, 129, 166, 203, 240, 0]

private def executionPayloadA_transactionsExpected : List (List UInt8) :=
  [[], [0, 255, 128, 0], [0, 255, 128, 0], [192, 0]]

private def executionPayloadA_withdrawalsExpected : List WithdrawalObservation :=
  [withdrawalBExpected, withdrawalAExpected, withdrawalAExpected]

private def executionPayloadA_blobGasUsedExpected : Nat :=
  17792278274739187338

private def executionPayloadA_excessBlobGasExpected : Nat :=
  1451626134950738547

private def executionPayloadA_blockAccessListExpected : List UInt8 :=
  [0, 80, 117, 0, 191, 228, 0]

private def executionPayloadA_slotNumberExpected : Nat :=
  5663810002792944195

private def executionPayloadA : ExecutionPayload :=
  ExecutionPayload.mk (hash [0, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68,
    105, 0, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 0] (by decide))
    (address [0, 128, 165, 202, 239, 20, 57, 94, 131, 168, 0, 242, 23, 60, 97, 134, 171, 208, 245,
    0] (by decide)) (hash [0, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163,
    0, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 0] (by decide)) (hash [0,
    186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 0, 10, 47, 84, 121, 158,
    195, 232, 13, 50, 87, 124, 161, 198, 235, 0] (by decide)) (fixed 256 [0, 215, 252, 33, 70,
    107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79,
    116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88,
    125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32,
    69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41,
    78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 0,
    87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22,
    59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250,
    31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3,
    40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12,
    49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240,
    21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212,
    249, 30, 67, 104, 0] (by decide)) (fixed 32 [0, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65,
    102, 139, 176, 213, 250, 0, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 0]
    (by decide)) (word64 17284194943158813537 (by decide)) (word64 1 (by decide)) (word64
    18446744073709551615 (by decide)) (word64 0 (by decide)) ⟨#[0, 133, 170, 207, 244, 25, 62, 99,
    136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 0, 105, 142, 179, 216, 253, 34, 71,
    108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 0]⟩ (word256
    115792089237316195423570985008687907853269984665640564039457584007913129639935 (by decide))
    (hash [0, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 0, 15, 52, 89,
    126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 0] (by decide)) #[⟨#[]⟩, ⟨#[0, 255, 128,
    0]⟩, ⟨#[0, 255, 128, 0]⟩, ⟨#[192, 0]⟩] #[withdrawalB, withdrawalA, withdrawalA] (word64
    17792278274739187338 (by decide)) (word64 1451626134950738547 (by decide)) ⟨#[0, 80, 117, 0,
    191, 228, 0]⟩ (word64 5663810002792944195 (by decide))

private def executionPayloadAExpected : ExecutionPayloadObservation :=
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve executionPayloadA == executionPayloadAExpected

private def executionPayloadB_parentHashExpected : List UInt8 :=
  [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 0, 250, 31, 68, 105,
    142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0]

private def executionPayloadB_feeRecipientExpected : List UInt8 :=
  [0, 199, 236, 17, 54, 91, 128, 165, 202, 239, 0, 57, 94, 131, 168, 205, 242, 23, 60, 0]

private def executionPayloadB_stateRootExpected : List UInt8 :=
  [0, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 0, 52, 89, 126, 163,
    200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 0]

private def executionPayloadB_receiptsRootExpected : List UInt8 :=
  [0, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 0, 81, 118, 155, 192, 229,
    10, 47, 84, 121, 158, 195, 232, 13, 50, 0]

private def executionPayloadB_logsBloomExpected : List UInt8 :=
  [0, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184,
    221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193,
    230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165,
    202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137,
    174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
    146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118,
    155, 192, 229, 10, 47, 84, 0, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127,
    164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99,
    136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71,
    108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80,
    117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89,
    126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61,
    98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 0]

private def executionPayloadB_prevRandaoExpected : List UInt8 :=
  [0, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 0, 139, 176, 213, 250,
    31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 0]

private def executionPayloadB_blockNumberExpected : Nat :=
  18446744073709551615

private def executionPayloadB_gasLimitExpected : Nat :=
  18446744073709551615

private def executionPayloadB_gasUsedExpected : Nat :=
  0

private def executionPayloadB_timestampExpected : Nat :=
  18446744073709551615

private def executionPayloadB_extraDataExpected : List UInt8 :=
  [0, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 0,
    176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 0]

private def executionPayloadB_baseFeePerGasExpected : Nat :=
  0

private def executionPayloadB_blockHashExpected : List UInt8 :=
  [0, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 0, 86, 123, 160, 197, 234,
    15, 52, 89, 126, 163, 200, 237, 18, 55, 0]

private def executionPayloadB_transactionsExpected : List (List UInt8) :=
  [[192, 0], [0, 255, 128, 0], [0, 255, 128, 0], []]

private def executionPayloadB_withdrawalsExpected : List WithdrawalObservation :=
  [withdrawalAExpected, withdrawalAExpected, withdrawalBExpected]

private def executionPayloadB_blobGasUsedExpected : Nat :=
  17792278274739187338

private def executionPayloadB_excessBlobGasExpected : Nat :=
  1451626134950738547

private def executionPayloadB_blockAccessListExpected : List UInt8 :=
  [0, 151, 188, 0, 6, 43, 0]

private def executionPayloadB_slotNumberExpected : Nat :=
  5663810002792944195

private def executionPayloadB : ExecutionPayload :=
  ExecutionPayload.mk (hash [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139,
    176, 0, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0] (by decide))
    (address [0, 199, 236, 17, 54, 91, 128, 165, 202, 239, 0, 57, 94, 131, 168, 205, 242, 23, 60,
    0] (by decide)) (hash [0, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234,
    0, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 0] (by decide)) (hash [0,
    1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 0, 81, 118, 155, 192, 229,
    10, 47, 84, 121, 158, 195, 232, 13, 50, 0] (by decide)) (fixed 256 [0, 30, 67, 104, 141, 178,
    215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150,
    187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159,
    196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131,
    168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103,
    140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75,
    112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    0, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93,
    130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65,
    102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37,
    74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46,
    83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18,
    55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246,
    27, 64, 101, 138, 175, 0] (by decide)) (fixed 32 [0, 59, 96, 133, 170, 207, 244, 25, 62, 99,
    136, 173, 210, 247, 28, 65, 0, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71,
    108, 0] (by decide)) (word64 18446744073709551615 (by decide)) (word64 18446744073709551615
    (by decide)) (word64 0 (by decide)) (word64 18446744073709551615 (by decide)) ⟨#[0, 204, 241,
    22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 0, 176, 213, 250,
    31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 0]⟩ (word256 0 (by
    decide)) (hash [0, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 0, 86,
    123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 0] (by decide)) #[⟨#[192, 0]⟩,
    ⟨#[0, 255, 128, 0]⟩, ⟨#[0, 255, 128, 0]⟩, ⟨#[]⟩] #[withdrawalA, withdrawalA, withdrawalB]
    (word64 17792278274739187338 (by decide)) (word64 1451626134950738547 (by decide)) ⟨#[0, 151,
    188, 0, 6, 43, 0]⟩ (word64 5663810002792944195 (by decide))

private def executionPayloadBExpected : ExecutionPayloadObservation :=
  (executionPayloadB_parentHashExpected, executionPayloadB_feeRecipientExpected,
    executionPayloadB_stateRootExpected, executionPayloadB_receiptsRootExpected,
    executionPayloadB_logsBloomExpected, executionPayloadB_prevRandaoExpected,
    executionPayloadB_blockNumberExpected, executionPayloadB_gasLimitExpected,
    executionPayloadB_gasUsedExpected, executionPayloadB_timestampExpected,
    executionPayloadB_extraDataExpected, executionPayloadB_baseFeePerGasExpected,
    executionPayloadB_blockHashExpected, executionPayloadB_transactionsExpected,
    executionPayloadB_withdrawalsExpected, executionPayloadB_blobGasUsedExpected,
    executionPayloadB_excessBlobGasExpected, executionPayloadB_blockAccessListExpected,
    executionPayloadB_slotNumberExpected)

#guard executionPayloadObserve executionPayloadB == executionPayloadBExpected

private def newPayloadRequestZero_executionPayloadExpected : ExecutionPayloadObservation :=
  executionPayloadZeroExpected

private def newPayloadRequestZero_versionedHashesExpected : List (List UInt8) :=
  []

private def newPayloadRequestZero_parentBeaconBlockRootExpected : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def newPayloadRequestZero_executionRequestsExpected : ExecutionRequestsObservation :=
  executionRequestsZeroExpected

private def newPayloadRequestZero : NewPayloadRequest :=
  NewPayloadRequest.mk executionPayloadZero #[] (hash [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)) executionRequestsZero

private def newPayloadRequestZeroExpected : NewPayloadRequestObservation :=
  (newPayloadRequestZero_executionPayloadExpected, newPayloadRequestZero_versionedHashesExpected,
    newPayloadRequestZero_parentBeaconBlockRootExpected,
    newPayloadRequestZero_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve newPayloadRequestZero)
  newPayloadRequestZeroExpected

private def newPayloadRequestMax_executionPayloadExpected : ExecutionPayloadObservation :=
  executionPayloadMaxExpected

private def newPayloadRequestMax_versionedHashesExpected : List (List UInt8) :=
  [[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]]

private def newPayloadRequestMax_parentBeaconBlockRootExpected : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private def newPayloadRequestMax_executionRequestsExpected : ExecutionRequestsObservation :=
  executionRequestsMaxExpected

private def newPayloadRequestMax : NewPayloadRequest :=
  NewPayloadRequest.mk executionPayloadMax #[(hash [255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255] (by decide))] (hash [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255] (by decide)) executionRequestsMax

private def newPayloadRequestMaxExpected : NewPayloadRequestObservation :=
  (newPayloadRequestMax_executionPayloadExpected, newPayloadRequestMax_versionedHashesExpected,
    newPayloadRequestMax_parentBeaconBlockRootExpected,
    newPayloadRequestMax_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve newPayloadRequestMax)
  newPayloadRequestMaxExpected

private def newPayloadRequestA_executionPayloadExpected : ExecutionPayloadObservation :=
  executionPayloadAExpected

private def newPayloadRequestA_versionedHashesExpected : List (List UInt8) :=
  [[255, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 0, 201, 238, 19, 56,
    93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0], [2, 128, 165, 202, 239, 20, 57, 94, 131,
    168, 205, 242, 23, 60, 97, 134, 0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103,
    140, 177, 0], [2, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 0, 208,
    245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 0]]

private def newPayloadRequestA_parentBeaconBlockRootExpected : List UInt8 :=
  [0, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 0, 24, 61, 98, 135,
    172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 0]

private def newPayloadRequestA_executionRequestsExpected : ExecutionRequestsObservation :=
  executionRequestsAExpected

private def newPayloadRequestA : NewPayloadRequest :=
  NewPayloadRequest.mk executionPayloadA #[(hash [255, 121, 158, 195, 232, 13, 50, 87, 124, 161,
    198, 235, 16, 53, 90, 127, 0, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170,
    0] (by decide)), (hash [2, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97,
    134, 0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 0] (by decide)),
    (hash [2, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 0, 208, 245,
    26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 0] (by decide))] (hash [0, 200, 237,
    18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 0, 24, 61, 98, 135, 172, 209, 246,
    27, 64, 101, 138, 175, 212, 249, 0] (by decide)) executionRequestsA

private def newPayloadRequestAExpected : NewPayloadRequestObservation :=
  (newPayloadRequestA_executionPayloadExpected, newPayloadRequestA_versionedHashesExpected,
    newPayloadRequestA_parentBeaconBlockRootExpected,
    newPayloadRequestA_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve newPayloadRequestA)
  newPayloadRequestAExpected

private def newPayloadRequestB_executionPayloadExpected : ExecutionPayloadObservation :=
  executionPayloadBExpected

private def newPayloadRequestB_versionedHashesExpected : List (List UInt8) :=
  [[2, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 0, 208, 245, 26, 63,
    100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 0], [2, 128, 165, 202, 239, 20, 57, 94, 131,
    168, 205, 242, 23, 60, 97, 134, 0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103,
    140, 177, 0], [255, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 0,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0]]

private def newPayloadRequestB_parentBeaconBlockRootExpected : List UInt8 :=
  [0, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 0, 95, 132, 169, 206,
    243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 0]

private def newPayloadRequestB_executionRequestsExpected : ExecutionRequestsObservation :=
  executionRequestsBExpected

private def newPayloadRequestB : NewPayloadRequest :=
  NewPayloadRequest.mk executionPayloadB #[(hash [2, 128, 165, 202, 239, 20, 57, 94, 131, 168,
    205, 242, 23, 60, 97, 134, 0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140,
    177, 0] (by decide)), (hash [2, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 0] (by decide)),
    (hash [255, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 0, 201, 238,
    19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 0] (by decide))] (hash [0, 15, 52, 89,
    126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 0, 95, 132, 169, 206, 243, 24, 61, 98,
    135, 172, 209, 246, 27, 64, 0] (by decide)) executionRequestsB

private def newPayloadRequestBExpected : NewPayloadRequestObservation :=
  (newPayloadRequestB_executionPayloadExpected, newPayloadRequestB_versionedHashesExpected,
    newPayloadRequestB_parentBeaconBlockRootExpected,
    newPayloadRequestB_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve newPayloadRequestB)
  newPayloadRequestBExpected

#guard executionPayloadObserve
    { executionPayloadA with parentHash := executionPayloadB.parentHash } ==
  (executionPayloadB_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with feeRecipient := executionPayloadB.feeRecipient } ==
  (executionPayloadA_parentHashExpected, executionPayloadB_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with stateRoot := executionPayloadB.stateRoot } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadB_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with receiptsRoot := executionPayloadB.receiptsRoot } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadB_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with logsBloom := executionPayloadB.logsBloom } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadB_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with prevRandao := executionPayloadB.prevRandao } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadB_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with blockNumber := executionPayloadB.blockNumber } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadB_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve { executionPayloadA with gasLimit := executionPayloadB.gasLimit } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadB_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve { executionPayloadA with gasUsed := executionPayloadB.gasUsed } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadB_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with timestamp := executionPayloadB.timestamp } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadB_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with extraData := executionPayloadB.extraData } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadB_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with baseFeePerGas := executionPayloadB.baseFeePerGas } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadB_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with blockHash := executionPayloadB.blockHash } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadB_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with transactions := executionPayloadB.transactions } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadB_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with withdrawals := executionPayloadB.withdrawals } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadB_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with blobGasUsed := executionPayloadB.blobGasUsed } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadB_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with excessBlobGas := executionPayloadB.excessBlobGas } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadB_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with blockAccessList := executionPayloadB.blockAccessList } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadB_blockAccessListExpected,
    executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve
    { executionPayloadA with slotNumber := executionPayloadB.slotNumber } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected,
    executionPayloadA_withdrawalsExpected, executionPayloadA_blobGasUsedExpected,
    executionPayloadA_excessBlobGasExpected, executionPayloadA_blockAccessListExpected,
    executionPayloadB_slotNumberExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve
    { newPayloadRequestA with executionPayload := newPayloadRequestB.executionPayload })
  (newPayloadRequestB_executionPayloadExpected, newPayloadRequestA_versionedHashesExpected,
    newPayloadRequestA_parentBeaconBlockRootExpected,
    newPayloadRequestA_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve
    { newPayloadRequestA with versionedHashes := newPayloadRequestB.versionedHashes })
  (newPayloadRequestA_executionPayloadExpected, newPayloadRequestB_versionedHashesExpected,
    newPayloadRequestA_parentBeaconBlockRootExpected,
    newPayloadRequestA_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve
    { newPayloadRequestA with parentBeaconBlockRoot := newPayloadRequestB.parentBeaconBlockRoot })
  (newPayloadRequestA_executionPayloadExpected, newPayloadRequestA_versionedHashesExpected,
    newPayloadRequestB_parentBeaconBlockRootExpected,
    newPayloadRequestA_executionRequestsExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve
    { newPayloadRequestA with executionRequests := newPayloadRequestB.executionRequests })
  (newPayloadRequestA_executionPayloadExpected, newPayloadRequestA_versionedHashesExpected,
    newPayloadRequestA_parentBeaconBlockRootExpected,
    newPayloadRequestB_executionRequestsExpected)

#guard executionPayloadObserve { executionPayloadA with transactions := #[] } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, [], executionPayloadA_withdrawalsExpected,
    executionPayloadA_blobGasUsedExpected, executionPayloadA_excessBlobGasExpected,
    executionPayloadA_blockAccessListExpected, executionPayloadA_slotNumberExpected)

#guard executionPayloadObserve { executionPayloadA with withdrawals := #[] } ==
  (executionPayloadA_parentHashExpected, executionPayloadA_feeRecipientExpected,
    executionPayloadA_stateRootExpected, executionPayloadA_receiptsRootExpected,
    executionPayloadA_logsBloomExpected, executionPayloadA_prevRandaoExpected,
    executionPayloadA_blockNumberExpected, executionPayloadA_gasLimitExpected,
    executionPayloadA_gasUsedExpected, executionPayloadA_timestampExpected,
    executionPayloadA_extraDataExpected, executionPayloadA_baseFeePerGasExpected,
    executionPayloadA_blockHashExpected, executionPayloadA_transactionsExpected, [],
    executionPayloadA_blobGasUsedExpected, executionPayloadA_excessBlobGasExpected,
    executionPayloadA_blockAccessListExpected, executionPayloadA_slotNumberExpected)

#guard newPayloadRequestEqual (newPayloadRequestObserve
    { newPayloadRequestA with versionedHashes := #[] })
  (newPayloadRequestA_executionPayloadExpected, [],
    newPayloadRequestA_parentBeaconBlockRootExpected,
    newPayloadRequestA_executionRequestsExpected)
