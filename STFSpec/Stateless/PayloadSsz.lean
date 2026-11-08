/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.Payload
import STFSpec.Stateless.WireLimits
import STFSpec.Block.WithdrawalSsz
import STFSpec.Codec.SszSchema
import STFSpec.Codec.SszWellFormed
import STFSpec.Codec.SszWellTyped
import Init.Data.Array.Lemmas

/-!
# Execution payload SSZ schema

Library `EthStateless`. Complete ordered adapters for the nineteen independent payload
fields, using the actual Block Withdrawal dictionary. Operation support and execution
validity remain separate from the wire domain.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless.ExecutionPayload

open Base Codec

private def byteMembers? : List SszValue → Option (List ByteArray)
  | [] => some []
  | .bytes b :: rest => do
      let bs ← byteMembers? rest
      pure (b :: bs)
  | _ => none

private def withdrawalMembers? : List SszValue → Option (List Block.Withdrawal)
  | [] => some []
  | v :: rest => do
      let a ← Block.Withdrawal.instSszSchema.ofValue? v
      let bs ← withdrawalMembers? rest
      pure (a :: bs)

private def fromValue? : SszValue → Option ExecutionPayload
  | .container [.bytes parentHash, .bytes feeRecipient, .bytes stateRoot, .bytes receiptsRoot,
    .bytes logsBloom, .bytes prevRandao, .uint blockNumber, .uint gasLimit, .uint gasUsed,
    .uint timestamp, .bytes extraData, .uint baseFeePerGas, .bytes blockHash, .list transactions,
    .list withdrawals, .uint blobGasUsed, .uint excessBlobGas, .bytes blockAccessList,
    .uint slotNumber] => do
      let parentHash ← Hash32.ofBytes? (Bytes.ofByteArray parentHash)
      let feeRecipient ← Address.ofBytes? (Bytes.ofByteArray feeRecipient)
      let stateRoot ← Hash32.ofBytes? (Bytes.ofByteArray stateRoot)
      let receiptsRoot ← Hash32.ofBytes? (Bytes.ofByteArray receiptsRoot)
      let logsBloom ← FixedBytes.ofBytes? (Bytes.ofByteArray logsBloom)
      let prevRandao ← FixedBytes.ofBytes? (Bytes.ofByteArray prevRandao)
      let blockNumber ← U64.ofNat? blockNumber
      let gasLimit ← U64.ofNat? gasLimit
      let gasUsed ← U64.ofNat? gasUsed
      let timestamp ← U64.ofNat? timestamp
      let baseFeePerGas ← U256.ofNat? baseFeePerGas
      let blockHash ← Hash32.ofBytes? (Bytes.ofByteArray blockHash)
      let transactions ← byteMembers? transactions
      let withdrawals ← withdrawalMembers? withdrawals
      let blobGasUsed ← U64.ofNat? blobGasUsed
      let excessBlobGas ← U64.ofNat? excessBlobGas
      let slotNumber ← U64.ofNat? slotNumber
      pure ⟨parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockNumber,
        gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash, transactions.toArray,
        withdrawals.toArray, blobGasUsed, excessBlobGas, blockAccessList, slotNumber⟩
  | _ => none

/-- Actual progressive payload metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:39–72` and
`src/ethereum/utils/ssz.py:174–320`. Validity adds only the extra-data wire bound. -/
instance instSszSchema : SszSchema ExecutionPayload where
  type := .progressiveContainer (List.replicate 19 true) [
    .byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32,
    .byteVector 256, .byteVector 32, .uint 8, .uint 8, .uint 8, .uint 8,
    .byteList maxExtraDataBytes, .uint 32, .byteVector 32,
    .progressiveList .progressiveByteList,
    .progressiveList Block.Withdrawal.instSszSchema.type,
    .uint 8, .uint 8, .progressiveByteList, .uint 8]
  fieldNames := ["parent_hash", "fee_recipient", "state_root", "receipts_root",
    "logs_bloom", "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp",
    "extra_data", "base_fee_per_gas", "block_hash", "transactions", "withdrawals",
    "blob_gas_used", "excess_blob_gas", "block_access_list", "slot_number"]
  valid a := a.extraData.size ≤ maxExtraDataBytes
  toValue a := .container [
    .bytes a.parentHash.toBytes.toByteArray,
    .bytes a.feeRecipient.toBytes.toByteArray,
    .bytes a.stateRoot.toBytes.toByteArray,
    .bytes a.receiptsRoot.toBytes.toByteArray,
    .bytes a.logsBloom.toBytes.toByteArray,
    .bytes a.prevRandao.toBytes.toByteArray,
    .uint a.blockNumber.toNat,
    .uint a.gasLimit.toNat,
    .uint a.gasUsed.toNat,
    .uint a.timestamp.toNat,
    .bytes a.extraData,
    .uint a.baseFeePerGas.toNat,
    .bytes a.blockHash.toBytes.toByteArray,
    .list (a.transactions.toList.map SszValue.bytes),
    .list (a.withdrawals.toList.map Block.Withdrawal.instSszSchema.toValue),
    .uint a.blobGasUsed.toNat,
    .uint a.excessBlobGas.toNat,
    .bytes a.blockAccessList,
    .uint a.slotNumber.toNat]
  ofValue? := fromValue?

private theorem byteMembers?_map (bs : List ByteArray) :
    byteMembers? (bs.map SszValue.bytes) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [byteMembers?, ih]

private theorem byteMembers?_preserves (xs : List SszValue) (bs : List ByteArray)
    (h : byteMembers? xs = some bs) : bs.map SszValue.bytes = xs := by
  induction xs generalizing bs with
  | nil => simpa [byteMembers?] using h.symm
  | cons x xs ih =>
    cases x <;> try contradiction
    rename_i b
    cases hr : byteMembers? xs with
    | none => simp [byteMembers?, hr] at h
    | some rest =>
      simp [byteMembers?, hr] at h
      subst bs
      simp only [List.map_cons, ih rest hr]

private theorem withdrawalMembers?_map (as : List Block.Withdrawal) :
    withdrawalMembers? (as.map Block.Withdrawal.instSszSchema.toValue) = some as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [withdrawalMembers?, (Block.Withdrawal.ssz_ofValue_toValue a True.intro).1, ih]

private theorem withdrawalMembers?_preserves (xs : List SszValue)
    (as : List Block.Withdrawal)
    (ht : ∀ v ∈ xs, SszValue.WellTyped Block.Withdrawal.instSszSchema.type v)
    (h : withdrawalMembers? xs = some as) :
    as.map Block.Withdrawal.instSszSchema.toValue = xs := by
  induction xs generalizing as with
  | nil => simpa [withdrawalMembers?] using h.symm
  | cons v xs ih =>
    simp only [withdrawalMembers?, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, rest, hr, he⟩ := h
    subst as
    have hv := (Block.Withdrawal.ssz_toValue_ofValue v a ⟨ht v (by simp), ha⟩).2
    simp only [List.map_cons, hv, ih rest (fun x hx ↦ ht x (by simp [hx])) hr]

private theorem typed_forward_iff (a : ExecutionPayload) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) ↔
      instSszSchema.valid a := by
  have h64 (x : U64) : x.toNat < 18446744073709551616 := U64.toNat_lt x
  have h256 (x : U256) :
      x.toNat <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    U256.toNat_lt x
  have hw (b : Block.Withdrawal) : SszValue.WellTyped
      (.container [.uint 8, .uint 8, .byteVector 20, .uint 8])
      (.container [.uint b.index.toNat, .uint b.validatorIndex.toNat,
        .bytes b.address.toBytes.toByteArray, .uint b.amount.toNat]) :=
    (Block.Withdrawal.ssz_ofValue_toValue b True.intro).2
  dsimp only [SszSchema.type, SszSchema.toValue, SszSchema.valid, instSszSchema]
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    SszValue.wellTyped_iff (.progressiveByteList) (.bytes _),
    SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.byteVector _) (.bytes _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _),
    Bytes.size_toByteArray, Hash32.size_toBytes, Address.size_toBytes,
    FixedBytes.size_toBytes, h64, h256, hw]

/-- The actual nineteen-field progressive descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  have hw : SszType.WellFormed (.container [.uint 8, .uint 8, .byteVector 20,
    .uint 8]) := Block.Withdrawal.ssz_type_wellFormed
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.progressiveContainer _ _),
    SszType.wellFormed_iff (.progressiveList _),
    SszType.wellFormed_iff (.progressiveByteList),
    SszType.wellFormed_iff (.uint _), SszType.wellFormed_iff (.byteVector _),
    SszType.wellFormed_iff (.byteList _), hw]

/-- Every wire-valid payload reconstructs completely and has its declared payload type. -/
theorem ssz_ofValue_toValue (a : ExecutionPayload) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  refine ⟨?_, (typed_forward_iff a).mpr h⟩
  have hw (bs : List Block.Withdrawal) :
      withdrawalMembers? (bs.map (fun b ↦ .container [
        .uint b.index.toNat, .uint b.validatorIndex.toNat,
        .bytes b.address.toBytes.toByteArray, .uint b.amount.toNat])) = some bs :=
    withdrawalMembers?_map bs
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, U64.ofNat?_toNat, U256.ofNat?_toNat,
    Bytes.ofByteArray_toByteArray, Hash32.ofBytes?_toBytes, Address.ofBytes?_toBytes,
    FixedBytes.ofBytes?_toBytes, byteMembers?_map, hw]

private theorem fromValue?_preserves (v : SszValue) (a : ExecutionPayload)
    (ht : SszValue.WellTyped instSszSchema.type v)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next parentHash feeRecipient stateRoot receiptsRoot logsBloom prevRandao blockNumber gasLimit
    gasUsed timestamp extraData baseFeePerGas blockHash transactions withdrawals blobGasUsed
    excessBlobGas blockAccessList slotNumber =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨parentHash', h_parentHash, feeRecipient', h_feeRecipient, stateRoot', h_stateRoot,
      receiptsRoot', h_receiptsRoot, logsBloom', h_logsBloom, prevRandao', h_prevRandao,
      blockNumber', h_blockNumber, gasLimit', h_gasLimit, gasUsed', h_gasUsed, timestamp',
      h_timestamp, baseFeePerGas', h_baseFeePerGas, blockHash', h_blockHash, transactions',
      h_transactions, withdrawals', h_withdrawals, blobGasUsed', h_blobGasUsed, excessBlobGas',
      h_excessBlobGas, slotNumber', h_slotNumber, ha⟩ := h
    cases ha
    have hw : ∀ w ∈ withdrawals,
        SszValue.WellTyped Block.Withdrawal.instSszSchema.type w := by
      dsimp only [SszSchema.type, instSszSchema] at ht
      simp only [SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
        List.length_cons, List.length_nil, List.zip_cons_cons, List.zip_nil_left,
        List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at ht
      apply (SszValue.wellTyped_iff (.progressiveList _) (.list _)).mp
      exact ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have e_parentHash := (Hash32.ofBytes?_eq_some_iff).mp h_parentHash
    have e_feeRecipient := (Address.ofBytes?_eq_some_iff).mp h_feeRecipient
    have e_stateRoot := (Hash32.ofBytes?_eq_some_iff).mp h_stateRoot
    have e_receiptsRoot := (Hash32.ofBytes?_eq_some_iff).mp h_receiptsRoot
    have e_logsBloom := (FixedBytes.ofBytes?_eq_some_iff).mp h_logsBloom
    have e_prevRandao := (FixedBytes.ofBytes?_eq_some_iff).mp h_prevRandao
    have e_blockNumber := (U64.ofNat?_eq_some_iff _ _).mp h_blockNumber
    have e_gasLimit := (U64.ofNat?_eq_some_iff _ _).mp h_gasLimit
    have e_gasUsed := (U64.ofNat?_eq_some_iff _ _).mp h_gasUsed
    have e_timestamp := (U64.ofNat?_eq_some_iff _ _).mp h_timestamp
    have e_baseFeePerGas := (U256.ofNat?_eq_some_iff _ _).mp h_baseFeePerGas
    have e_blockHash := (Hash32.ofBytes?_eq_some_iff).mp h_blockHash
    have e_transactions := byteMembers?_preserves transactions transactions' h_transactions
    have e_withdrawals := withdrawalMembers?_preserves withdrawals withdrawals' hw h_withdrawals
    change List.map (fun b ↦ .container [.uint b.index.toNat, .uint b.validatorIndex.toNat,
      .bytes b.address.toBytes.toByteArray, .uint b.amount.toNat]) withdrawals' = withdrawals
      at e_withdrawals
    have e_blobGasUsed := (U64.ofNat?_eq_some_iff _ _).mp h_blobGasUsed
    have e_excessBlobGas := (U64.ofNat?_eq_some_iff _ _).mp h_excessBlobGas
    have e_slotNumber := (U64.ofNat?_eq_some_iff _ _).mp h_slotNumber
    dsimp only [SszSchema.toValue, instSszSchema]
    simp only [e_parentHash.2, e_feeRecipient.2, e_stateRoot.2, e_receiptsRoot.2, e_logsBloom.2,
      e_prevRandao.2, e_blockNumber.2, e_gasLimit.2, e_gasUsed.2, e_timestamp.2, e_baseFeePerGas.2,
      e_blockHash.2, e_transactions, e_withdrawals, e_blobGasUsed.2, e_excessBlobGas.2,
      e_slotNumber.2, Bytes.toByteArray_ofByteArray]
  next => contradiction

/-- A typed successful reconstruction retains the whole raw value and wire validity (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : ExecutionPayload)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v := by
  have he := fromValue?_preserves v a h.1 h.2
  exact ⟨(typed_forward_iff a).mp (he.symm ▸ h.1), he⟩

end STFSpec.Stateless.ExecutionPayload
