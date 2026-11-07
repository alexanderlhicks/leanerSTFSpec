/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual payload schema clients

Library `EthConformance`. Private complete clients use the actual dictionary and
certificates through the public facade. Count recovery adds no wire-validity premise.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.PayloadSszCallerProofs

open STFSpec.Stateless STFSpec.Codec

private abbrev actual : SszSchema ExecutionPayload := ExecutionPayload.instSszSchema

private theorem inferred : (inferInstance : SszSchema ExecutionPayload) = actual := rfl

private theorem descriptor : actual.type = .progressiveContainer (List.replicate 19 true) [
    .byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32,
    .byteVector 256, .byteVector 32, .uint 8, .uint 8, .uint 8, .uint 8,
    .byteList maxExtraDataBytes, .uint 32, .byteVector 32,
    .progressiveList .progressiveByteList,
    .progressiveList STFSpec.Block.Withdrawal.instSszSchema.type,
    .uint 8, .uint 8, .progressiveByteList, .uint 8] := rfl

private theorem withdrawal_width :
    STFSpec.Block.Withdrawal.instSszSchema.type.fixedSize? = some 44 := by decide

private theorem head_slots :
    (match actual.type with
    | .progressiveContainer _ fs => fs.map (fun t ↦ t.fixedSize?.getD 4)
    | _ => []) = [32, 20, 32, 32, 256, 32, 8, 8, 8, 8, 4, 32, 32, 4, 4, 8, 8, 4, 8] := by
  decide

private theorem head_size :
    ([32, 20, 32, 32, 256, 32, 8, 8, 8, 8, 4, 32, 32, 4, 4, 8, 8, 4, 8] : List Nat).sum =
      540 := by decide

private theorem names : actual.fieldNames = [
    "parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
    "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
    "base_fee_per_gas", "block_hash", "transactions", "withdrawals", "blob_gas_used",
    "excess_blob_gas", "block_access_list", "slot_number"] := rfl

private theorem validity (a : ExecutionPayload) :
    actual.valid a ↔ a.extraData.size ≤ STFSpec.Fork.Amsterdam.MAX_EXTRA_DATA_BYTES := Iff.rfl

private theorem wf : actual.type.WellFormed := ExecutionPayload.ssz_type_wellFormed

private theorem forward : ∀ a : ExecutionPayload, actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) := ExecutionPayload.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : ExecutionPayload),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := ExecutionPayload.ssz_toValue_ofValue

private theorem complete_model (a : ExecutionPayload) : actual.toValue a = .container [
    .bytes a.parentHash.toBytes.toByteArray, .bytes a.feeRecipient.toBytes.toByteArray,
    .bytes a.stateRoot.toBytes.toByteArray, .bytes a.receiptsRoot.toBytes.toByteArray,
    .bytes a.logsBloom.toBytes.toByteArray, .bytes a.prevRandao.toBytes.toByteArray,
    .uint a.blockNumber.toNat, .uint a.gasLimit.toNat, .uint a.gasUsed.toNat,
    .uint a.timestamp.toNat, .bytes a.extraData, .uint a.baseFeePerGas.toNat,
    .bytes a.blockHash.toBytes.toByteArray, .list (a.transactions.toList.map SszValue.bytes),
    .list (a.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
    .uint a.blobGasUsed.toNat, .uint a.excessBlobGas.toNat, .bytes a.blockAccessList,
    .uint a.slotNumber.toNat] := rfl

private theorem complete_recovery (a : ExecutionPayload) (h : actual.valid a) :
    actual.ofValue? (actual.toValue a) = some a := (forward a h).1

private theorem recovered_reforward (v : SszValue) (a : ExecutionPayload)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem checked_recovery (a : ExecutionPayload)
    (parentHash : ByteArray)
    (feeRecipient : ByteArray)
    (stateRoot : ByteArray)
    (receiptsRoot : ByteArray)
    (logsBloom : ByteArray)
    (prevRandao : ByteArray)
    (blockNumber : Nat)
    (gasLimit : Nat)
    (gasUsed : Nat)
    (timestamp : Nat)
    (baseFeePerGas : Nat)
    (blockHash : ByteArray)
    (blobGasUsed : Nat)
    (excessBlobGas : Nat)
    (slotNumber : Nat)
    (h_parentHash : STFSpec.Base.Hash32.ofBytes? (STFSpec.Base.Bytes.ofByteArray parentHash) =
      some a.parentHash)
    (h_feeRecipient : STFSpec.Base.Address.ofBytes? (STFSpec.Base.Bytes.ofByteArray feeRecipient) =
      some a.feeRecipient)
    (h_stateRoot : STFSpec.Base.Hash32.ofBytes? (STFSpec.Base.Bytes.ofByteArray stateRoot) =
      some a.stateRoot)
    (h_receiptsRoot : STFSpec.Base.Hash32.ofBytes? (STFSpec.Base.Bytes.ofByteArray receiptsRoot) =
      some a.receiptsRoot)
    (h_logsBloom : STFSpec.Base.FixedBytes.ofBytes? (STFSpec.Base.Bytes.ofByteArray logsBloom) =
      some a.logsBloom)
    (h_prevRandao : STFSpec.Base.FixedBytes.ofBytes? (STFSpec.Base.Bytes.ofByteArray prevRandao) =
      some a.prevRandao)
    (h_blockNumber : STFSpec.Base.U64.ofNat? blockNumber = some a.blockNumber)
    (h_gasLimit : STFSpec.Base.U64.ofNat? gasLimit = some a.gasLimit)
    (h_gasUsed : STFSpec.Base.U64.ofNat? gasUsed = some a.gasUsed)
    (h_timestamp : STFSpec.Base.U64.ofNat? timestamp = some a.timestamp)
    (h_baseFeePerGas : STFSpec.Base.U256.ofNat? baseFeePerGas = some a.baseFeePerGas)
    (h_blockHash : STFSpec.Base.Hash32.ofBytes? (STFSpec.Base.Bytes.ofByteArray blockHash) =
      some a.blockHash)
    (h_blobGasUsed : STFSpec.Base.U64.ofNat? blobGasUsed = some a.blobGasUsed)
    (h_excessBlobGas : STFSpec.Base.U64.ofNat? excessBlobGas = some a.excessBlobGas)
    (h_slotNumber : STFSpec.Base.U64.ofNat? slotNumber = some a.slotNumber)
    (hvalid : actual.valid a) :
    actual.ofValue? (.container [
      .bytes parentHash,
      .bytes feeRecipient,
      .bytes stateRoot,
      .bytes receiptsRoot,
      .bytes logsBloom,
      .bytes prevRandao,
      .uint blockNumber,
      .uint gasLimit,
      .uint gasUsed,
      .uint timestamp,
      .bytes a.extraData,
      .uint baseFeePerGas,
      .bytes blockHash,
      .list (a.transactions.toList.map SszValue.bytes),
      .list (a.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
      .uint blobGasUsed,
      .uint excessBlobGas,
      .bytes a.blockAccessList,
      .uint slotNumber]) = some a ∧
      SszValue.WellTyped actual.type (.container [
      .bytes parentHash,
      .bytes feeRecipient,
      .bytes stateRoot,
      .bytes receiptsRoot,
      .bytes logsBloom,
      .bytes prevRandao,
      .uint blockNumber,
      .uint gasLimit,
      .uint gasUsed,
      .uint timestamp,
      .bytes a.extraData,
      .uint baseFeePerGas,
      .bytes blockHash,
      .list (a.transactions.toList.map SszValue.bytes),
      .list (a.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
      .uint blobGasUsed,
      .uint excessBlobGas,
      .bytes a.blockAccessList,
      .uint slotNumber]) ∧
      actual.toValue a = .container [
      .bytes parentHash,
      .bytes feeRecipient,
      .bytes stateRoot,
      .bytes receiptsRoot,
      .bytes logsBloom,
      .bytes prevRandao,
      .uint blockNumber,
      .uint gasLimit,
      .uint gasUsed,
      .uint timestamp,
      .bytes a.extraData,
      .uint baseFeePerGas,
      .bytes blockHash,
      .list (a.transactions.toList.map SszValue.bytes),
      .list (a.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
      .uint blobGasUsed,
      .uint excessBlobGas,
      .bytes a.blockAccessList,
      .uint slotNumber] := by
  have e_parentHash := (STFSpec.Base.Hash32.ofBytes?_eq_some_iff).mp h_parentHash
  have e_feeRecipient := (STFSpec.Base.Address.ofBytes?_eq_some_iff).mp h_feeRecipient
  have e_stateRoot := (STFSpec.Base.Hash32.ofBytes?_eq_some_iff).mp h_stateRoot
  have e_receiptsRoot := (STFSpec.Base.Hash32.ofBytes?_eq_some_iff).mp h_receiptsRoot
  have e_logsBloom := (STFSpec.Base.FixedBytes.ofBytes?_eq_some_iff).mp h_logsBloom
  have e_prevRandao := (STFSpec.Base.FixedBytes.ofBytes?_eq_some_iff).mp h_prevRandao
  have e_blockNumber := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_blockNumber
  have e_gasLimit := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_gasLimit
  have e_gasUsed := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_gasUsed
  have e_timestamp := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_timestamp
  have e_baseFeePerGas := (STFSpec.Base.U256.ofNat?_eq_some_iff _ _).mp h_baseFeePerGas
  have e_blockHash := (STFSpec.Base.Hash32.ofBytes?_eq_some_iff).mp h_blockHash
  have e_blobGasUsed := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_blobGasUsed
  have e_excessBlobGas := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_excessBlobGas
  have e_slotNumber := (STFSpec.Base.U64.ofNat?_eq_some_iff _ _).mp h_slotNumber
  have he : actual.toValue a = .container [
      .bytes parentHash,
      .bytes feeRecipient,
      .bytes stateRoot,
      .bytes receiptsRoot,
      .bytes logsBloom,
      .bytes prevRandao,
      .uint blockNumber,
      .uint gasLimit,
      .uint gasUsed,
      .uint timestamp,
      .bytes a.extraData,
      .uint baseFeePerGas,
      .bytes blockHash,
      .list (a.transactions.toList.map SszValue.bytes),
      .list (a.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
      .uint blobGasUsed,
      .uint excessBlobGas,
      .bytes a.blockAccessList,
      .uint slotNumber] := by
    rw [complete_model]
    simp only [e_parentHash.2, e_feeRecipient.2, e_stateRoot.2, e_receiptsRoot.2, e_logsBloom.2,
      e_prevRandao.2, e_blockNumber.2, e_gasLimit.2, e_gasUsed.2, e_timestamp.2, e_baseFeePerGas.2,
      e_blockHash.2, e_blobGasUsed.2, e_excessBlobGas.2, e_slotNumber.2,
      STFSpec.Base.Bytes.toByteArray_ofByteArray]
  exact ⟨he ▸ (forward a hvalid).1, he ▸ (forward a hvalid).2, he⟩

private theorem image_countRecoverable (a : ExecutionPayload) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue, ExecutionPayload.instSszSchema]
  simp [Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _),
    Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff (.progressiveByteList) (.bytes _),
    SszType.fixedSize?_eq (.progressiveByteList), SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _)]

end STFSpec.Conformance.Stateless.PayloadSszCallerProofs
