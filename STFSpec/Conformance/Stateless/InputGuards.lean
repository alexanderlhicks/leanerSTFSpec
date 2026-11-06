/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Whole raw stateless input controls

Library `EthConformance`. Private observations retain every nested byte, word and array occurrence.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

open STFSpec STFSpec.Base STFSpec.Stateless

set_option maxRecDepth 4096

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

private def consolidationRequestObserve (r : ConsolidationRequest) : ConsolidationRequestObservation :=
  (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList)

private abbrev BuilderDepositRequestObservation := List UInt8 × List UInt8 × Nat × List UInt8

private def builderDepositRequestObserve (r : BuilderDepositRequest) : BuilderDepositRequestObservation :=
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

private abbrev WitnessObservation := List (List UInt8) × List (List UInt8) × List (List UInt8)

private def witnessObserve (w : ExecutionWitness) : WitnessObservation :=
  (w.state.toList.map (fun b ↦ (Bytes.ofByteArray b).toList),
    w.codes.toList.map (fun b ↦ (Bytes.ofByteArray b).toList),
    w.headers.toList.map (fun b ↦ (Bytes.ofByteArray b).toList))

private def observe (x : StatelessInput) :
    NewPayloadRequestObservation × WitnessObservation × Nat :=
  (newPayloadRequestObserve x.newPayloadRequest, witnessObserve x.witness, x.chainId.toNat)

private def same (a b : NewPayloadRequestObservation × WitnessObservation × Nat) : Bool :=
  (a.1.1 == b.1.1) && (a.1.2.1 == b.1.2.1) &&
    (a.1.2.2.1 == b.1.2.2.1) && (a.1.2.2.2 == b.1.2.2.2) &&
    (a.2.1 == b.2.1) && (a.2.2 == b.2.2)

private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def raw (xs : List UInt8) : ByteArray := (Bytes.ofList xs).toByteArray

private def withdrawal : Block.Withdrawal :=
  ⟨U64.max, U64.zero, Address.ofNat 7, U64.ofNat 17⟩

private def deposit : DepositRequest :=
  ⟨FixedBytes.ofNat 8, FixedBytes.ofNat 9, U64.zero, FixedBytes.ofNat 10, U64.max⟩

private def withdrawalRequest : WithdrawalRequest :=
  ⟨Address.ofNat 11, FixedBytes.ofNat 12, U64.ofNat 19⟩

private def consolidation : ConsolidationRequest :=
  ⟨Address.ofNat 13, FixedBytes.ofNat 14, FixedBytes.ofNat 15⟩

private def builderDeposit : BuilderDepositRequest :=
  ⟨FixedBytes.ofNat 16, FixedBytes.ofNat 17, U64.max, FixedBytes.ofNat 18⟩

private def builderExit : BuilderExitRequest := ⟨Address.ofNat 19, FixedBytes.ofNat 20⟩

private def payload : ExecutionPayload :=
  ⟨hash 1, Address.ofNat 2, hash 3, hash 4, FixedBytes.ofNat 5, FixedBytes.ofNat 6,
    U64.zero, U64.max, U64.ofNat 23, U64.ofNat 0x0102030405060708,
    raw (List.replicate 33 255), U256.ofNat (2 ^ 255 + 37), hash 21,
    #[raw [], raw [255, 0, 128], raw [255, 0, 128], raw [0, 1]],
    #[withdrawal, withdrawal], U64.ofNat 29, U64.ofNat 31, raw [128, 255, 0],
    U64.ofNat 41⟩

private def request : NewPayloadRequest :=
  ⟨payload, #[hash 22, hash 23, hash 22, hash 24], hash 24,
    ⟨#[deposit, deposit], #[withdrawalRequest], #[consolidation],
      #[builderDeposit, builderDeposit, builderDeposit], #[builderExit]⟩⟩

private def emptyRequest : NewPayloadRequest :=
  ⟨{ payload with
      extraData := raw []
      transactions := #[]
      withdrawals := #[]
      blockAccessList := raw [] }, #[], hash 0, ⟨#[], #[], #[], #[], #[]⟩⟩

private def witness : ExecutionWitness :=
  ⟨#[raw [255, 0, 128], raw [], raw [255, 0, 128]], #[raw [0]],
    #[raw [128], raw [1, 0], raw []]⟩

private def input : StatelessInput := ⟨request, witness, U64.ofNat 0x0102030405060708⟩

private def bytes (n : Nat) (last : UInt8) : List UInt8 := List.replicate (n - 1) 0 ++ [last]

private def expectedWithdrawal : WithdrawalObservation :=
  (2 ^ 64 - 1, 0, bytes 20 7, 17)

private def expectedDeposit : DepositRequestObservation :=
  (bytes 48 8, bytes 32 9, 0, bytes 96 10, 2 ^ 64 - 1)

private def expectedPayload : ExecutionPayloadObservation :=
  (bytes 32 1, bytes 20 2, bytes 32 3, bytes 32 4, bytes 256 5, bytes 32 6,
    0, 2 ^ 64 - 1, 23, 0x0102030405060708, List.replicate 33 255, 2 ^ 255 + 37,
    bytes 32 21, [[], [255, 0, 128], [255, 0, 128], [0, 1]],
    [expectedWithdrawal, expectedWithdrawal], 29, 31, [128, 255, 0], 41)

private def expectedRequest : NewPayloadRequestObservation :=
  (expectedPayload, [bytes 32 22, bytes 32 23, bytes 32 22, bytes 32 24], bytes 32 24,
    ([expectedDeposit, expectedDeposit], [(bytes 20 11, bytes 48 12, 19)],
      [(bytes 20 13, bytes 48 14, bytes 48 15)],
      List.replicate 3 (bytes 48 16, bytes 32 17, 2 ^ 64 - 1, bytes 96 18),
      [(bytes 20 19, bytes 48 20)]))

private def expectedEmptyRequest : NewPayloadRequestObservation :=
  ((bytes 32 1, bytes 20 2, bytes 32 3, bytes 32 4, bytes 256 5, bytes 32 6,
    0, 2 ^ 64 - 1, 23, 0x0102030405060708, [], 2 ^ 255 + 37,
    bytes 32 21, [], [], 29, 31, [], 41), [], List.replicate 32 0, ([], [], [], [], []))

private def expectedWitness : WitnessObservation :=
  ([[255, 0, 128], [], [255, 0, 128]], [[0]], [[128], [1, 0], []])

#guard same (observe input) (expectedRequest, expectedWitness, 0x0102030405060708)
#guard same (observe { input with chainId := U64.zero }) (expectedRequest, expectedWitness, 0)
#guard same (observe { input with chainId := U64.max })
  (expectedRequest, expectedWitness, 2 ^ 64 - 1)
#guard same (observe { input with newPayloadRequest := emptyRequest })
  (expectedEmptyRequest, expectedWitness, 0x0102030405060708)
#guard same (observe { input with witness := ⟨#[], #[], #[]⟩ })
  (expectedRequest, ([], [], []), 0x0102030405060708)
#guard same (observe (StatelessInput.mk emptyRequest ⟨#[], #[], #[]⟩ U64.zero))
  (expectedEmptyRequest, ([], [], []), 0)
#guard same (observe { input with witness := ⟨witness.headers.reverse, witness.state, witness.codes⟩ })
  (expectedRequest, ([[], [1, 0], [128]], [[255, 0, 128], [], [255, 0, 128]], [[0]]),
    0x0102030405060708)
#guard same (observe { input with witness :=
    ⟨#[raw (List.replicate 1025 255)], #[], #[raw [], raw []]⟩ })
  (expectedRequest, ([List.replicate 1025 255], [], [[], []]), 0x0102030405060708)

private def changedRequest : NewPayloadRequest :=
  { request with
    executionPayload := { payload with transactions := payload.transactions.reverse }
    versionedHashes := request.versionedHashes.reverse
    executionRequests := { request.executionRequests with deposits := #[] } }

#guard same (observe { input with newPayloadRequest := changedRequest })
  (((bytes 32 1, bytes 20 2, bytes 32 3, bytes 32 4, bytes 256 5, bytes 32 6,
      0, 2 ^ 64 - 1, 23, 0x0102030405060708, List.replicate 33 255, 2 ^ 255 + 37,
      bytes 32 21, [[0, 1], [255, 0, 128], [255, 0, 128], []],
      [expectedWithdrawal, expectedWithdrawal], 29, 31, [128, 255, 0], 41),
    [bytes 32 24, bytes 32 22, bytes 32 23, bytes 32 22], bytes 32 24,
    ([], [(bytes 20 11, bytes 48 12, 19)], [(bytes 20 13, bytes 48 14, bytes 48 15)],
      List.replicate 3 (bytes 48 16, bytes 32 17, 2 ^ 64 - 1, bytes 96 18),
      [(bytes 20 19, bytes 48 20)])), expectedWitness, 0x0102030405060708)
