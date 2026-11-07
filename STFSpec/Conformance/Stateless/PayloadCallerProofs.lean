/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Raw payload and request facade clients

Library `EthConformance`. Private complete observations retain every byte, word and nested value.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

open STFSpec STFSpec.Base STFSpec.Stateless


private theorem bytes_determine (a b : ByteArray)
    (h : (Bytes.ofByteArray a).toList = (Bytes.ofByteArray b).toList) : a = b := by
  have recovered := congrArg Bytes.toByteArray (Bytes.ext h)
  simpa only [Bytes.toByteArray_ofByteArray] using recovered

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

private theorem withdrawalObserve_determine (a b : Block.Withdrawal)
    (h : withdrawalObserve a = withdrawalObserve b) : a = b := by
  simp only [withdrawalObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have e0 : a.index = b.index := U64.toNat_inj.mp h0
  have e1 : a.validatorIndex = b.validatorIndex := U64.toNat_inj.mp h1
  have e2 : a.address = b.address := Address.toBytes_inj.mp (Bytes.ext h2)
  have e3 : a.amount = b.amount := U64.toNat_inj.mp h3
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  rfl

private theorem depositRequestObserve_determine (a b : DepositRequest)
    (h : depositRequestObserve a = depositRequestObserve b) : a = b := by
  simp only [depositRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have e0 : a.pubkey = b.pubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.withdrawalCredentials = b.withdrawalCredentials := FixedBytes.toBytes_inj.mp
    (Bytes.ext h1)
  have e2 : a.amount = b.amount := U64.toNat_inj.mp h2
  have e3 : a.signature = b.signature := FixedBytes.toBytes_inj.mp (Bytes.ext h3)
  have e4 : a.index = b.index := U64.toNat_inj.mp h4
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  cases e4
  rfl

private theorem withdrawalRequestObserve_determine (a b : WithdrawalRequest)
    (h : withdrawalRequestObserve a = withdrawalRequestObserve b) : a = b := by
  simp only [withdrawalRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2⟩
  have e0 : a.sourceAddress = b.sourceAddress := Address.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.validatorPubkey = b.validatorPubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h1)
  have e2 : a.amount = b.amount := U64.toNat_inj.mp h2
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  rfl

private theorem consolidationRequestObserve_determine (a b : ConsolidationRequest)
    (h : consolidationRequestObserve a = consolidationRequestObserve b) : a = b := by
  simp only [consolidationRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2⟩
  have e0 : a.sourceAddress = b.sourceAddress := Address.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.sourcePubkey = b.sourcePubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h1)
  have e2 : a.targetPubkey = b.targetPubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h2)
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  rfl

private theorem builderDepositRequestObserve_determine (a b : BuilderDepositRequest)
    (h : builderDepositRequestObserve a = builderDepositRequestObserve b) : a = b := by
  simp only [builderDepositRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have e0 : a.pubkey = b.pubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.withdrawalCredentials = b.withdrawalCredentials := FixedBytes.toBytes_inj.mp
    (Bytes.ext h1)
  have e2 : a.amount = b.amount := U64.toNat_inj.mp h2
  have e3 : a.signature = b.signature := FixedBytes.toBytes_inj.mp (Bytes.ext h3)
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  rfl

private theorem builderExitRequestObserve_determine (a b : BuilderExitRequest)
    (h : builderExitRequestObserve a = builderExitRequestObserve b) : a = b := by
  simp only [builderExitRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1⟩
  have e0 : a.sourceAddress = b.sourceAddress := Address.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.pubkey = b.pubkey := FixedBytes.toBytes_inj.mp (Bytes.ext h1)
  cases a
  cases b
  cases e0
  cases e1
  rfl

private theorem executionRequestsObserve_determine (a b : ExecutionRequests)
    (h : executionRequestsObserve a = executionRequestsObserve b) : a = b := by
  simp only [executionRequestsObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have e0 : a.deposits = b.deposits := Array.toList_inj.mp ((List.map_inj_right (fun x y h ↦
    depositRequestObserve_determine _ _ h)).mp h0)
  have e1 : a.withdrawals = b.withdrawals := Array.toList_inj.mp ((List.map_inj_right (fun x y h ↦
    withdrawalRequestObserve_determine _ _ h)).mp h1)
  have e2 : a.consolidations = b.consolidations := Array.toList_inj.mp ((List.map_inj_right (fun x
    y h ↦ consolidationRequestObserve_determine _ _ h)).mp h2)
  have e3 : a.builderDeposits = b.builderDeposits := Array.toList_inj.mp ((List.map_inj_right (fun
    x y h ↦ builderDepositRequestObserve_determine _ _ h)).mp h3)
  have e4 : a.builderExits = b.builderExits := Array.toList_inj.mp ((List.map_inj_right (fun x y h
    ↦ builderExitRequestObserve_determine _ _ h)).mp h4)
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  cases e4
  rfl

private theorem executionPayloadObserve_determine (a b : ExecutionPayload)
    (h : executionPayloadObserve a = executionPayloadObserve b) : a = b := by
  simp only [executionPayloadObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18⟩
  have e0 : a.parentHash = b.parentHash := Hash32.toBytes_inj.mp (Bytes.ext h0)
  have e1 : a.feeRecipient = b.feeRecipient := Address.toBytes_inj.mp (Bytes.ext h1)
  have e2 : a.stateRoot = b.stateRoot := Hash32.toBytes_inj.mp (Bytes.ext h2)
  have e3 : a.receiptsRoot = b.receiptsRoot := Hash32.toBytes_inj.mp (Bytes.ext h3)
  have e4 : a.logsBloom = b.logsBloom := FixedBytes.toBytes_inj.mp (Bytes.ext h4)
  have e5 : a.prevRandao = b.prevRandao := FixedBytes.toBytes_inj.mp (Bytes.ext h5)
  have e6 : a.blockNumber = b.blockNumber := U64.toNat_inj.mp h6
  have e7 : a.gasLimit = b.gasLimit := U64.toNat_inj.mp h7
  have e8 : a.gasUsed = b.gasUsed := U64.toNat_inj.mp h8
  have e9 : a.timestamp = b.timestamp := U64.toNat_inj.mp h9
  have e10 : a.extraData = b.extraData := bytes_determine _ _ h10
  have e11 : a.baseFeePerGas = b.baseFeePerGas := U256.toNat_inj.mp h11
  have e12 : a.blockHash = b.blockHash := Hash32.toBytes_inj.mp (Bytes.ext h12)
  have e13 : a.transactions = b.transactions := Array.toList_inj.mp ((List.map_inj_right (fun x y
    h ↦ bytes_determine _ _ h)).mp h13)
  have e14 : a.withdrawals = b.withdrawals := Array.toList_inj.mp ((List.map_inj_right (fun x y h
    ↦ withdrawalObserve_determine _ _ h)).mp h14)
  have e15 : a.blobGasUsed = b.blobGasUsed := U64.toNat_inj.mp h15
  have e16 : a.excessBlobGas = b.excessBlobGas := U64.toNat_inj.mp h16
  have e17 : a.blockAccessList = b.blockAccessList := bytes_determine _ _ h17
  have e18 : a.slotNumber = b.slotNumber := U64.toNat_inj.mp h18
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  cases e4
  cases e5
  cases e6
  cases e7
  cases e8
  cases e9
  cases e10
  cases e11
  cases e12
  cases e13
  cases e14
  cases e15
  cases e16
  cases e17
  cases e18
  rfl

private theorem newPayloadRequestObserve_determine (a b : NewPayloadRequest)
    (h : newPayloadRequestObserve a = newPayloadRequestObserve b) : a = b := by
  simp only [newPayloadRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have e0 : a.executionPayload = b.executionPayload := executionPayloadObserve_determine _ _ h0
  have e1 : a.versionedHashes = b.versionedHashes := Array.toList_inj.mp ((List.map_inj_right (fun
    x y h ↦ Hash32.toBytes_inj.mp (Bytes.ext h))).mp h1)
  have e2 : a.parentBeaconBlockRoot = b.parentBeaconBlockRoot := Hash32.toBytes_inj.mp (Bytes.ext
    h2)
  have e3 : a.executionRequests = b.executionRequests := executionRequestsObserve_determine _ _ h3
  cases a
  cases b
  cases e0
  cases e1
  cases e2
  cases e3
  rfl

private def executionPayloadConstructor : Hash32 → Address → Hash32 → Hash32 → Bloom → Bytes32 →
  U64 → U64 → U64 → U64 → ByteArray → U256 → Hash32 → Array ByteArray → Array Block.Withdrawal →
  U64 → U64 → ByteArray → U64 → ExecutionPayload := ExecutionPayload.mk

private def executionPayload_parentHash : ExecutionPayload → Hash32 := ExecutionPayload.parentHash

private def executionPayload_feeRecipient : ExecutionPayload → Address :=
  ExecutionPayload.feeRecipient

private def executionPayload_stateRoot : ExecutionPayload → Hash32 := ExecutionPayload.stateRoot

private def executionPayload_receiptsRoot : ExecutionPayload → Hash32 :=
  ExecutionPayload.receiptsRoot

private def executionPayload_logsBloom : ExecutionPayload → Bloom := ExecutionPayload.logsBloom

private def executionPayload_prevRandao : ExecutionPayload → Bytes32 := ExecutionPayload.prevRandao

private def executionPayload_blockNumber : ExecutionPayload → U64 := ExecutionPayload.blockNumber

private def executionPayload_gasLimit : ExecutionPayload → U64 := ExecutionPayload.gasLimit

private def executionPayload_gasUsed : ExecutionPayload → U64 := ExecutionPayload.gasUsed

private def executionPayload_timestamp : ExecutionPayload → U64 := ExecutionPayload.timestamp

private def executionPayload_extraData : ExecutionPayload → ByteArray := ExecutionPayload.extraData

private def executionPayload_baseFeePerGas : ExecutionPayload → U256 :=
  ExecutionPayload.baseFeePerGas

private def executionPayload_blockHash : ExecutionPayload → Hash32 := ExecutionPayload.blockHash

private def executionPayload_transactions : ExecutionPayload → Array ByteArray :=
  ExecutionPayload.transactions

private def executionPayload_withdrawals : ExecutionPayload → Array Block.Withdrawal :=
  ExecutionPayload.withdrawals

private def executionPayload_blobGasUsed : ExecutionPayload → U64 := ExecutionPayload.blobGasUsed

private def executionPayload_excessBlobGas : ExecutionPayload → U64 :=
  ExecutionPayload.excessBlobGas

private def executionPayload_blockAccessList : ExecutionPayload → ByteArray :=
  ExecutionPayload.blockAccessList

private def executionPayload_slotNumber : ExecutionPayload → U64 := ExecutionPayload.slotNumber

private def executionPayloadFields (r : ExecutionPayload) : Hash32 × Address × Hash32 × Hash32 ×
  Bloom × Bytes32 × U64 × U64 × U64 × U64 × ByteArray × U256 × Hash32 × Array ByteArray × Array
  Block.Withdrawal × U64 × U64 × ByteArray × U64 :=
  (r.parentHash, r.feeRecipient, r.stateRoot, r.receiptsRoot, r.logsBloom, r.prevRandao,
    r.blockNumber, r.gasLimit, r.gasUsed, r.timestamp, r.extraData, r.baseFeePerGas, r.blockHash,
    r.transactions, r.withdrawals, r.blobGasUsed, r.excessBlobGas, r.blockAccessList,
    r.slotNumber)

private theorem executionPayload_construction (parentHash : Hash32) (feeRecipient : Address)
  (stateRoot : Hash32) (receiptsRoot : Hash32) (logsBloom : Bloom) (prevRandao : Bytes32)
  (blockNumber : U64) (gasLimit : U64) (gasUsed : U64) (timestamp : U64) (extraData : ByteArray)
  (baseFeePerGas : U256) (blockHash : Hash32) (transactions : Array ByteArray) (withdrawals :
  Array Block.Withdrawal) (blobGasUsed : U64) (excessBlobGas : U64) (blockAccessList : ByteArray)
  (slotNumber : U64) :
    executionPayloadFields (executionPayloadConstructor parentHash feeRecipient stateRoot
      receiptsRoot logsBloom prevRandao blockNumber gasLimit gasUsed timestamp extraData
      baseFeePerGas blockHash transactions withdrawals blobGasUsed excessBlobGas blockAccessList
      slotNumber) = (parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao,
      blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash,
      transactions, withdrawals, blobGasUsed, excessBlobGas, blockAccessList, slotNumber) := rfl

private theorem executionPayload_construction_observations (parentHash : Hash32) (feeRecipient :
  Address) (stateRoot : Hash32) (receiptsRoot : Hash32) (logsBloom : Bloom) (prevRandao : Bytes32)
  (blockNumber : U64) (gasLimit : U64) (gasUsed : U64) (timestamp : U64) (extraData : ByteArray)
  (baseFeePerGas : U256) (blockHash : Hash32) (transactions : Array ByteArray) (withdrawals :
  Array Block.Withdrawal) (blobGasUsed : U64) (excessBlobGas : U64) (blockAccessList : ByteArray)
  (slotNumber : U64) :
    executionPayloadObserve (ExecutionPayload.mk parentHash feeRecipient stateRoot receiptsRoot
      logsBloom prevRandao blockNumber gasLimit gasUsed timestamp extraData baseFeePerGas
      blockHash transactions withdrawals blobGasUsed excessBlobGas blockAccessList slotNumber) =
      (parentHash.toBytes.toList, feeRecipient.toBytes.toList, stateRoot.toBytes.toList,
      receiptsRoot.toBytes.toList, logsBloom.toBytes.toList, prevRandao.toBytes.toList,
      blockNumber.toNat, gasLimit.toNat, gasUsed.toNat, timestamp.toNat, (Bytes.ofByteArray
      extraData).toList, baseFeePerGas.toNat, blockHash.toBytes.toList, (transactions.toList.map
      (fun b ↦ (Bytes.ofByteArray b).toList)), (withdrawals.toList.map withdrawalObserve),
      blobGasUsed.toNat, excessBlobGas.toNat, (Bytes.ofByteArray blockAccessList).toList,
      slotNumber.toNat) := rfl

private theorem executionPayload_reconstruction (r : ExecutionPayload) :
    ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot r.receiptsRoot r.logsBloom
      r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp r.extraData r.baseFeePerGas
      r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas r.blockAccessList
      r.slotNumber = r := rfl

private theorem executionPayload_fields_determine (a b : ExecutionPayload)
    (h : executionPayloadFields a = executionPayloadFields b) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem executionPayload_update_parentHash (r : ExecutionPayload) (value : Hash32) :
    { r with parentHash := value } = ExecutionPayload.mk value r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_parentHash (r : ExecutionPayload)
  (value : Hash32) :
    executionPayloadObserve { r with parentHash := value } = (value.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_parentHash (r : ExecutionPayload) :
    Hash32.ofBytes? r.parentHash.toBytes = some r.parentHash := Hash32.ofBytes?_toBytes _

private theorem executionPayload_update_feeRecipient (r : ExecutionPayload) (value : Address) :
    { r with feeRecipient := value } = ExecutionPayload.mk r.parentHash value r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_feeRecipient (r : ExecutionPayload)
  (value : Address) :
    executionPayloadObserve { r with feeRecipient := value } = (r.parentHash.toBytes.toList,
      value.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_feeRecipient (r : ExecutionPayload) :
    Address.ofBytes? r.feeRecipient.toBytes = some r.feeRecipient := Address.ofBytes?_toBytes _

private theorem executionPayload_update_stateRoot (r : ExecutionPayload) (value : Hash32) :
    { r with stateRoot := value } = ExecutionPayload.mk r.parentHash r.feeRecipient value
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_stateRoot (r : ExecutionPayload) (value : Hash32) :
    executionPayloadObserve { r with stateRoot := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, value.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_stateRoot (r : ExecutionPayload) :
    Hash32.ofBytes? r.stateRoot.toBytes = some r.stateRoot := Hash32.ofBytes?_toBytes _

private theorem executionPayload_update_receiptsRoot (r : ExecutionPayload) (value : Hash32) :
    { r with receiptsRoot := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      value r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp r.extraData
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_receiptsRoot (r : ExecutionPayload)
  (value : Hash32) :
    executionPayloadObserve { r with receiptsRoot := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, value.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_receiptsRoot (r : ExecutionPayload) :
    Hash32.ofBytes? r.receiptsRoot.toBytes = some r.receiptsRoot := Hash32.ofBytes?_toBytes _

private theorem executionPayload_update_logsBloom (r : ExecutionPayload) (value : Bloom) :
    { r with logsBloom := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot value r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp r.extraData
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_logsBloom (r : ExecutionPayload) (value : Bloom) :
    executionPayloadObserve { r with logsBloom := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      value.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat, r.gasLimit.toNat,
      r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_logsBloom (r : ExecutionPayload) :
    FixedBytes.ofBytes? r.logsBloom.toBytes = some r.logsBloom := FixedBytes.ofBytes?_toBytes _

private theorem executionPayload_update_prevRandao (r : ExecutionPayload) (value : Bytes32) :
    { r with prevRandao := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom value r.blockNumber r.gasLimit r.gasUsed r.timestamp r.extraData
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_prevRandao (r : ExecutionPayload)
  (value : Bytes32) :
    executionPayloadObserve { r with prevRandao := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, value.toBytes.toList, r.blockNumber.toNat, r.gasLimit.toNat,
      r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_prevRandao (r : ExecutionPayload) :
    FixedBytes.ofBytes? r.prevRandao.toBytes = some r.prevRandao := FixedBytes.ofBytes?_toBytes _

private theorem executionPayload_update_blockNumber (r : ExecutionPayload) (value : U64) :
    { r with blockNumber := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao value r.gasLimit r.gasUsed r.timestamp r.extraData
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_blockNumber (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with blockNumber := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, value.toNat, r.gasLimit.toNat,
      r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_blockNumber (r : ExecutionPayload) :
    U64.ofNat r.blockNumber.toNat = r.blockNumber := U64.ofNat_toNat _

private theorem executionPayload_update_gasLimit (r : ExecutionPayload) (value : U64) :
    { r with gasLimit := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber value r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_gasLimit (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with gasLimit := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat, value.toNat,
      r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_gasLimit (r : ExecutionPayload) :
    U64.ofNat r.gasLimit.toNat = r.gasLimit := U64.ofNat_toNat _

private theorem executionPayload_update_gasUsed (r : ExecutionPayload) (value : U64) :
    { r with gasUsed := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit value r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_gasUsed (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with gasUsed := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, value.toNat, r.timestamp.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_gasUsed (r : ExecutionPayload) :
    U64.ofNat r.gasUsed.toNat = r.gasUsed := U64.ofNat_toNat _

private theorem executionPayload_update_timestamp (r : ExecutionPayload) (value : U64) :
    { r with timestamp := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed value r.extraData
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_timestamp (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with timestamp := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, value.toNat, (Bytes.ofByteArray r.extraData).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_timestamp (r : ExecutionPayload) :
    U64.ofNat r.timestamp.toNat = r.timestamp := U64.ofNat_toNat _

private theorem executionPayload_update_extraData (r : ExecutionPayload) (value : ByteArray) :
    { r with extraData := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp value
      r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_extraData (r : ExecutionPayload)
  (value : ByteArray) :
    executionPayloadObserve { r with extraData := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray value).toList,
      r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map (fun b ↦
      (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_extraData (r : ExecutionPayload) :
    (Bytes.ofList (Bytes.ofByteArray r.extraData).toList).toByteArray = r.extraData := by
  rw [Bytes.ofList_toList, Bytes.toByteArray_ofByteArray]

private theorem executionPayload_update_baseFeePerGas (r : ExecutionPayload) (value : U256) :
    { r with baseFeePerGas := value } = ExecutionPayload.mk r.parentHash r.feeRecipient
      r.stateRoot r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed
      r.timestamp r.extraData value r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_baseFeePerGas (r : ExecutionPayload)
  (value : U256) :
    executionPayloadObserve { r with baseFeePerGas := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, value.toNat, r.blockHash.toBytes.toList, (r.transactions.toList.map
      (fun b ↦ (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_baseFeePerGas (r : ExecutionPayload) :
    U256.ofNat r.baseFeePerGas.toNat = r.baseFeePerGas := U256.ofNat_toNat _

private theorem executionPayload_update_blockHash (r : ExecutionPayload) (value : Hash32) :
    { r with blockHash := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas value r.transactions r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_blockHash (r : ExecutionPayload) (value : Hash32) :
    executionPayloadObserve { r with blockHash := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, value.toBytes.toList, (r.transactions.toList.map
      (fun b ↦ (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_blockHash (r : ExecutionPayload) :
    Hash32.ofBytes? r.blockHash.toBytes = some r.blockHash := Hash32.ofBytes?_toBytes _

private theorem executionPayload_update_transactions (r : ExecutionPayload)
  (value : Array ByteArray) :
    { r with transactions := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash value r.withdrawals r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_transactions (r : ExecutionPayload)
  (value : Array ByteArray) :
    executionPayloadObserve { r with transactions := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList, (value.toList.map
      (fun b ↦ (Bytes.ofByteArray b).toList)), (r.withdrawals.toList.map withdrawalObserve),
      r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray r.blockAccessList).toList,
      r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_transactions (r : ExecutionPayload) :
    r.transactions.toList.toArray = r.transactions := Array.toArray_toList

private theorem executionPayload_update_withdrawals (r : ExecutionPayload)
  (value : Array Block.Withdrawal) :
    { r with withdrawals := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions value r.blobGasUsed r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_withdrawals (r : ExecutionPayload)
  (value : Array Block.Withdrawal) :
    executionPayloadObserve { r with withdrawals := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)), (value.toList.map
      withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat, (Bytes.ofByteArray
      r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_withdrawals (r : ExecutionPayload) :
    r.withdrawals.toList.toArray = r.withdrawals := Array.toArray_toList

private theorem executionPayload_update_blobGasUsed (r : ExecutionPayload) (value : U64) :
    { r with blobGasUsed := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals value r.excessBlobGas
      r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_blobGasUsed (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with blobGasUsed := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), value.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_blobGasUsed (r : ExecutionPayload) :
    U64.ofNat r.blobGasUsed.toNat = r.blobGasUsed := U64.ofNat_toNat _

private theorem executionPayload_update_excessBlobGas (r : ExecutionPayload) (value : U64) :
    { r with excessBlobGas := value } = ExecutionPayload.mk r.parentHash r.feeRecipient
      r.stateRoot r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed
      r.timestamp r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals
      r.blobGasUsed value r.blockAccessList r.slotNumber := rfl

private theorem executionPayload_observe_update_excessBlobGas (r : ExecutionPayload)
  (value : U64) :
    executionPayloadObserve { r with excessBlobGas := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, value.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_excessBlobGas (r : ExecutionPayload) :
    U64.ofNat r.excessBlobGas.toNat = r.excessBlobGas := U64.ofNat_toNat _

private theorem executionPayload_update_blockAccessList (r : ExecutionPayload)
  (value : ByteArray) :
    { r with blockAccessList := value } = ExecutionPayload.mk r.parentHash r.feeRecipient
      r.stateRoot r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed
      r.timestamp r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals
      r.blobGasUsed r.excessBlobGas value r.slotNumber := rfl

private theorem executionPayload_observe_update_blockAccessList (r : ExecutionPayload)
  (value : ByteArray) :
    executionPayloadObserve { r with blockAccessList := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray value).toList, r.slotNumber.toNat) := rfl

private theorem executionPayload_recover_blockAccessList (r : ExecutionPayload) :
    (Bytes.ofList (Bytes.ofByteArray r.blockAccessList).toList).toByteArray = r.blockAccessList :=
      by
  rw [Bytes.ofList_toList, Bytes.toByteArray_ofByteArray]

private theorem executionPayload_update_slotNumber (r : ExecutionPayload) (value : U64) :
    { r with slotNumber := value } = ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot
      r.receiptsRoot r.logsBloom r.prevRandao r.blockNumber r.gasLimit r.gasUsed r.timestamp
      r.extraData r.baseFeePerGas r.blockHash r.transactions r.withdrawals r.blobGasUsed
      r.excessBlobGas r.blockAccessList value := rfl

private theorem executionPayload_observe_update_slotNumber (r : ExecutionPayload) (value : U64) :
    executionPayloadObserve { r with slotNumber := value } = (r.parentHash.toBytes.toList,
      r.feeRecipient.toBytes.toList, r.stateRoot.toBytes.toList, r.receiptsRoot.toBytes.toList,
      r.logsBloom.toBytes.toList, r.prevRandao.toBytes.toList, r.blockNumber.toNat,
      r.gasLimit.toNat, r.gasUsed.toNat, r.timestamp.toNat, (Bytes.ofByteArray
      r.extraData).toList, r.baseFeePerGas.toNat, r.blockHash.toBytes.toList,
      (r.transactions.toList.map (fun b ↦ (Bytes.ofByteArray b).toList)),
      (r.withdrawals.toList.map withdrawalObserve), r.blobGasUsed.toNat, r.excessBlobGas.toNat,
      (Bytes.ofByteArray r.blockAccessList).toList, value.toNat) := rfl

private theorem executionPayload_recover_slotNumber (r : ExecutionPayload) :
    U64.ofNat r.slotNumber.toNat = r.slotNumber := U64.ofNat_toNat _

private theorem executionPayload_whole_conversion_recovery (r : ExecutionPayload) :
    ExecutionPayload.mk r.parentHash r.feeRecipient r.stateRoot r.receiptsRoot r.logsBloom
      r.prevRandao (U64.ofNat r.blockNumber.toNat) (U64.ofNat r.gasLimit.toNat) (U64.ofNat
      r.gasUsed.toNat) (U64.ofNat r.timestamp.toNat) (Bytes.ofList (Bytes.ofByteArray
      r.extraData).toList).toByteArray (U256.ofNat r.baseFeePerGas.toNat) r.blockHash
      r.transactions.toList.toArray r.withdrawals.toList.toArray (U64.ofNat r.blobGasUsed.toNat)
      (U64.ofNat r.excessBlobGas.toNat) (Bytes.ofList (Bytes.ofByteArray
      r.blockAccessList).toList).toByteArray (U64.ofNat r.slotNumber.toNat) = r := by
  simp only [U64.ofNat_toNat, Bytes.ofList_toList, Bytes.toByteArray_ofByteArray,
    U256.ofNat_toNat, Array.toArray_toList]

private def newPayloadRequestConstructor : ExecutionPayload → Array VersionedHash → Hash32 →
  ExecutionRequests → NewPayloadRequest := NewPayloadRequest.mk

private def newPayloadRequest_executionPayload : NewPayloadRequest → ExecutionPayload :=
  NewPayloadRequest.executionPayload

private def newPayloadRequest_versionedHashes : NewPayloadRequest → Array VersionedHash :=
  NewPayloadRequest.versionedHashes

private def newPayloadRequest_parentBeaconBlockRoot : NewPayloadRequest → Hash32 :=
  NewPayloadRequest.parentBeaconBlockRoot

private def newPayloadRequest_executionRequests : NewPayloadRequest → ExecutionRequests :=
  NewPayloadRequest.executionRequests

private def newPayloadRequestFields (r : NewPayloadRequest) : ExecutionPayload × Array
  VersionedHash × Hash32 × ExecutionRequests :=
  (r.executionPayload, r.versionedHashes, r.parentBeaconBlockRoot, r.executionRequests)

private theorem newPayloadRequest_construction (executionPayload : ExecutionPayload)
  (versionedHashes : Array VersionedHash) (parentBeaconBlockRoot : Hash32) (executionRequests :
  ExecutionRequests) :
    newPayloadRequestFields (newPayloadRequestConstructor executionPayload versionedHashes
      parentBeaconBlockRoot executionRequests) = (executionPayload, versionedHashes,
      parentBeaconBlockRoot, executionRequests) := rfl

private theorem newPayloadRequest_construction_observations (executionPayload : ExecutionPayload)
  (versionedHashes : Array VersionedHash) (parentBeaconBlockRoot : Hash32) (executionRequests :
  ExecutionRequests) :
    newPayloadRequestObserve (NewPayloadRequest.mk executionPayload versionedHashes
      parentBeaconBlockRoot executionRequests) = (executionPayloadObserve executionPayload,
      (versionedHashes.toList.map (fun h ↦ h.toBytes.toList)),
      parentBeaconBlockRoot.toBytes.toList, executionRequestsObserve executionRequests) := rfl

private theorem newPayloadRequest_reconstruction (r : NewPayloadRequest) :
    NewPayloadRequest.mk r.executionPayload r.versionedHashes r.parentBeaconBlockRoot
      r.executionRequests = r := rfl

private theorem newPayloadRequest_fields_determine (a b : NewPayloadRequest)
    (h : newPayloadRequestFields a = newPayloadRequestFields b) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem newPayloadRequest_update_executionPayload (r : NewPayloadRequest)
  (value : ExecutionPayload) :
    { r with executionPayload := value } = NewPayloadRequest.mk value r.versionedHashes
      r.parentBeaconBlockRoot r.executionRequests := rfl

private theorem newPayloadRequest_observe_update_executionPayload (r : NewPayloadRequest)
  (value : ExecutionPayload) :
    newPayloadRequestObserve { r with executionPayload := value } = (executionPayloadObserve
      value, (r.versionedHashes.toList.map (fun h ↦ h.toBytes.toList)),
      r.parentBeaconBlockRoot.toBytes.toList, executionRequestsObserve r.executionRequests) := rfl

private theorem newPayloadRequest_update_versionedHashes (r : NewPayloadRequest)
  (value : Array VersionedHash) :
    { r with versionedHashes := value } = NewPayloadRequest.mk r.executionPayload value
      r.parentBeaconBlockRoot r.executionRequests := rfl

private theorem newPayloadRequest_observe_update_versionedHashes (r : NewPayloadRequest)
  (value : Array VersionedHash) :
    newPayloadRequestObserve { r with versionedHashes := value } = (executionPayloadObserve
      r.executionPayload, (value.toList.map (fun h ↦ h.toBytes.toList)),
      r.parentBeaconBlockRoot.toBytes.toList, executionRequestsObserve r.executionRequests) := rfl

private theorem newPayloadRequest_recover_versionedHashes (r : NewPayloadRequest) :
    r.versionedHashes.toList.toArray = r.versionedHashes := Array.toArray_toList

private theorem newPayloadRequest_update_parentBeaconBlockRoot (r : NewPayloadRequest)
  (value : Hash32) :
    { r with parentBeaconBlockRoot := value } = NewPayloadRequest.mk r.executionPayload
      r.versionedHashes value r.executionRequests := rfl

private theorem newPayloadRequest_observe_update_parentBeaconBlockRoot (r : NewPayloadRequest)
  (value : Hash32) :
    newPayloadRequestObserve { r with parentBeaconBlockRoot := value } = (executionPayloadObserve
      r.executionPayload, (r.versionedHashes.toList.map (fun h ↦ h.toBytes.toList)),
      value.toBytes.toList, executionRequestsObserve r.executionRequests) := rfl

private theorem newPayloadRequest_recover_parentBeaconBlockRoot (r : NewPayloadRequest) :
    Hash32.ofBytes? r.parentBeaconBlockRoot.toBytes = some r.parentBeaconBlockRoot :=
      Hash32.ofBytes?_toBytes _

private theorem newPayloadRequest_update_executionRequests (r : NewPayloadRequest)
  (value : ExecutionRequests) :
    { r with executionRequests := value } = NewPayloadRequest.mk r.executionPayload
      r.versionedHashes r.parentBeaconBlockRoot value := rfl

private theorem newPayloadRequest_observe_update_executionRequests (r : NewPayloadRequest)
  (value : ExecutionRequests) :
    newPayloadRequestObserve { r with executionRequests := value } = (executionPayloadObserve
      r.executionPayload, (r.versionedHashes.toList.map (fun h ↦ h.toBytes.toList)),
      r.parentBeaconBlockRoot.toBytes.toList, executionRequestsObserve value) := rfl

private theorem newPayloadRequest_whole_conversion_recovery (r : NewPayloadRequest) :
    NewPayloadRequest.mk r.executionPayload r.versionedHashes.toList.toArray
      r.parentBeaconBlockRoot r.executionRequests = r := by
  simp only [Array.toArray_toList]
