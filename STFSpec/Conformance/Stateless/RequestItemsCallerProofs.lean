/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Raw execution-request public-facade clients

Library `EthConformance`. Private clients quantify all fields of each nominal item.
Complete byte/word observations use only the public Base contracts.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.RequestItemsCallerProofs

open STFSpec.Base STFSpec.Stateless

set_option exponentiation.threshold 1024

private def depositRequestConstructor : Bytes48 → Bytes32 → U64 → Bytes96 → U64 → DepositRequest :=
  DepositRequest.mk

private def depositRequestPubkey : DepositRequest → Bytes48 := DepositRequest.pubkey
private def depositRequestWithdrawalCredentials : DepositRequest → Bytes32 :=
  DepositRequest.withdrawalCredentials
private def depositRequestAmount : DepositRequest → U64 := DepositRequest.amount
private def depositRequestSignature : DepositRequest → Bytes96 := DepositRequest.signature
private def depositRequestIndex : DepositRequest → U64 := DepositRequest.index

private def depositRequestFields (r : DepositRequest) : Bytes48 × Bytes32 × U64 × Bytes96 × U64 :=
  (r.pubkey, r.withdrawalCredentials, r.amount, r.signature, r.index)

private def depositRequestObserve (r : DepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList, r.index.toNat)

private theorem depositRequest_constructor (pubkey : Bytes48) (withdrawalCredentials : Bytes32)
  (amount : U64) (signature : Bytes96) (index : U64) :
    depositRequestFields (depositRequestConstructor pubkey withdrawalCredentials amount signature
      index) = (pubkey, withdrawalCredentials, amount, signature, index) := rfl

private theorem depositRequest_reconstruction (r : DepositRequest) :
    DepositRequest.mk r.pubkey r.withdrawalCredentials r.amount r.signature r.index = r := rfl

private theorem depositRequest_fields_determine (r s : DepositRequest)
    (h : depositRequestFields r = depositRequestFields s) : r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem depositRequest_observations_determine (r s : DepositRequest)
    (h : depositRequestObserve r = depositRequestObserve s) : r = s := by
  simp only [depositRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  apply depositRequest_fields_determine
  simp only [depositRequestFields, Prod.mk.injEq]
  exact ⟨FixedBytes.toBytes_inj.mp (Bytes.ext h0),
    FixedBytes.toBytes_inj.mp (Bytes.ext h1),
    U64.toNat_inj.mp h2,
    FixedBytes.toBytes_inj.mp (Bytes.ext h3),
    U64.toNat_inj.mp h4⟩

private theorem depositRequest_update_pubkey (r : DepositRequest) (value : Bytes48) :
    { r with pubkey := value } = DepositRequest.mk value r.withdrawalCredentials r.amount
      r.signature r.index := rfl

private theorem depositRequest_observe_update_pubkey (r : DepositRequest) (value : Bytes48) :
    depositRequestObserve { r with pubkey := value } =
      (value.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
        r.signature.toBytes.toList, r.index.toNat) := rfl

private theorem depositRequest_update_withdrawalCredentials (r : DepositRequest)
  (value : Bytes32) :
    { r with withdrawalCredentials := value } = DepositRequest.mk r.pubkey value r.amount
      r.signature r.index := rfl

private theorem depositRequest_observe_update_withdrawalCredentials (r : DepositRequest)
  (value : Bytes32) :
    depositRequestObserve { r with withdrawalCredentials := value } =
      (r.pubkey.toBytes.toList, value.toBytes.toList, r.amount.toNat, r.signature.toBytes.toList,
        r.index.toNat) := rfl

private theorem depositRequest_update_amount (r : DepositRequest) (value : U64) :
    { r with amount := value } = DepositRequest.mk r.pubkey r.withdrawalCredentials value
      r.signature r.index := rfl

private theorem depositRequest_observe_update_amount (r : DepositRequest) (value : U64) :
    depositRequestObserve { r with amount := value } =
      (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, value.toNat,
        r.signature.toBytes.toList, r.index.toNat) := rfl

private theorem depositRequest_update_signature (r : DepositRequest) (value : Bytes96) :
    { r with signature := value } = DepositRequest.mk r.pubkey r.withdrawalCredentials r.amount
      value r.index := rfl

private theorem depositRequest_observe_update_signature (r : DepositRequest) (value : Bytes96) :
    depositRequestObserve { r with signature := value } =
      (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
        value.toBytes.toList, r.index.toNat) := rfl

private theorem depositRequest_update_index (r : DepositRequest) (value : U64) :
    { r with index := value } = DepositRequest.mk r.pubkey r.withdrawalCredentials r.amount
      r.signature value := rfl

private theorem depositRequest_observe_update_index (r : DepositRequest) (value : U64) :
    depositRequestObserve { r with index := value } =
      (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
        r.signature.toBytes.toList, value.toNat) := rfl

private theorem depositRequest_pubkey_model (r : DepositRequest) :
    FixedBytes.ofBytes? r.pubkey.toBytes = some r.pubkey ∧
      r.pubkey.toBytes.size = 48 ∧ r.pubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem depositRequest_withdrawalCredentials_model (r : DepositRequest) :
    FixedBytes.ofBytes? r.withdrawalCredentials.toBytes = some r.withdrawalCredentials ∧
      r.withdrawalCredentials.toBytes.size = 32 ∧ r.withdrawalCredentials.toNat < 2 ^ (8 * 32) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem depositRequest_amount_model (r : DepositRequest) :
    U64.ofNat? r.amount.toNat = some r.amount ∧
      r.amount.toNat < 2 ^ 64 ∧ r.amount.toNat = r.amount.toBitVec.toNat :=
  ⟨U64.ofNat?_toNat _, U64.toNat_lt _, U64.toNat_def _⟩

private theorem depositRequest_signature_model (r : DepositRequest) :
    FixedBytes.ofBytes? r.signature.toBytes = some r.signature ∧
      r.signature.toBytes.size = 96 ∧ r.signature.toNat < 2 ^ (8 * 96) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem depositRequest_index_model (r : DepositRequest) :
    U64.ofNat? r.index.toNat = some r.index ∧
      r.index.toNat < 2 ^ 64 ∧ r.index.toNat = r.index.toBitVec.toNat :=
  ⟨U64.ofNat?_toNat _, U64.toNat_lt _, U64.toNat_def _⟩

private def withdrawalRequestConstructor : Address → Bytes48 → U64 → WithdrawalRequest :=
  WithdrawalRequest.mk

private def withdrawalRequestSourceAddress : WithdrawalRequest → Address :=
  WithdrawalRequest.sourceAddress
private def withdrawalRequestValidatorPubkey : WithdrawalRequest → Bytes48 :=
  WithdrawalRequest.validatorPubkey
private def withdrawalRequestAmount : WithdrawalRequest → U64 := WithdrawalRequest.amount

private def withdrawalRequestFields (r : WithdrawalRequest) : Address × Bytes48 × U64 :=
  (r.sourceAddress, r.validatorPubkey, r.amount)

private def withdrawalRequestObserve (r : WithdrawalRequest) :
    List UInt8 × List UInt8 × Nat :=
  (r.sourceAddress.toBytes.toList, r.validatorPubkey.toBytes.toList, r.amount.toNat)

private theorem withdrawalRequest_constructor (sourceAddress : Address) (validatorPubkey : Bytes48)
  (amount : U64) :
    withdrawalRequestFields (withdrawalRequestConstructor sourceAddress validatorPubkey amount) =
      (sourceAddress, validatorPubkey, amount) := rfl

private theorem withdrawalRequest_reconstruction (r : WithdrawalRequest) :
    WithdrawalRequest.mk r.sourceAddress r.validatorPubkey r.amount = r := rfl

private theorem withdrawalRequest_fields_determine (r s : WithdrawalRequest)
    (h : withdrawalRequestFields r = withdrawalRequestFields s) : r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem withdrawalRequest_observations_determine (r s : WithdrawalRequest)
    (h : withdrawalRequestObserve r = withdrawalRequestObserve s) : r = s := by
  simp only [withdrawalRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2⟩
  apply withdrawalRequest_fields_determine
  simp only [withdrawalRequestFields, Prod.mk.injEq]
  exact ⟨Address.toBytes_inj.mp (Bytes.ext h0),
    FixedBytes.toBytes_inj.mp (Bytes.ext h1),
    U64.toNat_inj.mp h2⟩

private theorem withdrawalRequest_update_sourceAddress (r : WithdrawalRequest) (value : Address) :
    { r with sourceAddress := value } =
      WithdrawalRequest.mk value r.validatorPubkey r.amount := rfl

private theorem withdrawalRequest_observe_update_sourceAddress (r : WithdrawalRequest)
  (value : Address) :
    withdrawalRequestObserve { r with sourceAddress := value } =
      (value.toBytes.toList, r.validatorPubkey.toBytes.toList, r.amount.toNat) := rfl

private theorem withdrawalRequest_update_validatorPubkey (r : WithdrawalRequest)
  (value : Bytes48) :
    { r with validatorPubkey := value } =
      WithdrawalRequest.mk r.sourceAddress value r.amount := rfl

private theorem withdrawalRequest_observe_update_validatorPubkey (r : WithdrawalRequest)
  (value : Bytes48) :
    withdrawalRequestObserve { r with validatorPubkey := value } =
      (r.sourceAddress.toBytes.toList, value.toBytes.toList, r.amount.toNat) := rfl

private theorem withdrawalRequest_update_amount (r : WithdrawalRequest) (value : U64) :
    { r with amount := value } =
      WithdrawalRequest.mk r.sourceAddress r.validatorPubkey value := rfl

private theorem withdrawalRequest_observe_update_amount (r : WithdrawalRequest) (value : U64) :
    withdrawalRequestObserve { r with amount := value } =
      (r.sourceAddress.toBytes.toList, r.validatorPubkey.toBytes.toList, value.toNat) := rfl

private theorem withdrawalRequest_sourceAddress_model (r : WithdrawalRequest) :
    Address.ofBytes? r.sourceAddress.toBytes = some r.sourceAddress ∧
      r.sourceAddress.toBytes.size = 20 ∧ r.sourceAddress.toNat < 2 ^ (8 * 20) :=
  ⟨Address.ofBytes?_toBytes _, Address.size_toBytes _, Address.toNat_lt _⟩

private theorem withdrawalRequest_validatorPubkey_model (r : WithdrawalRequest) :
    FixedBytes.ofBytes? r.validatorPubkey.toBytes = some r.validatorPubkey ∧
      r.validatorPubkey.toBytes.size = 48 ∧ r.validatorPubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem withdrawalRequest_amount_model (r : WithdrawalRequest) :
    U64.ofNat? r.amount.toNat = some r.amount ∧
      r.amount.toNat < 2 ^ 64 ∧ r.amount.toNat = r.amount.toBitVec.toNat :=
  ⟨U64.ofNat?_toNat _, U64.toNat_lt _, U64.toNat_def _⟩

private def consolidationRequestConstructor : Address → Bytes48 → Bytes48 → ConsolidationRequest :=
  ConsolidationRequest.mk

private def consolidationRequestSourceAddress : ConsolidationRequest → Address :=
  ConsolidationRequest.sourceAddress
private def consolidationRequestSourcePubkey : ConsolidationRequest → Bytes48 :=
  ConsolidationRequest.sourcePubkey
private def consolidationRequestTargetPubkey : ConsolidationRequest → Bytes48 :=
  ConsolidationRequest.targetPubkey

private def consolidationRequestFields (r : ConsolidationRequest) : Address × Bytes48 × Bytes48 :=
  (r.sourceAddress, r.sourcePubkey, r.targetPubkey)

private def consolidationRequestObserve (r : ConsolidationRequest) :
    List UInt8 × List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList)

private theorem consolidationRequest_constructor (sourceAddress : Address) (sourcePubkey : Bytes48)
  (targetPubkey : Bytes48) :
    consolidationRequestFields (consolidationRequestConstructor sourceAddress sourcePubkey
      targetPubkey) = (sourceAddress, sourcePubkey, targetPubkey) := rfl

private theorem consolidationRequest_reconstruction (r : ConsolidationRequest) :
    ConsolidationRequest.mk r.sourceAddress r.sourcePubkey r.targetPubkey = r := rfl

private theorem consolidationRequest_fields_determine (r s : ConsolidationRequest)
    (h : consolidationRequestFields r = consolidationRequestFields s) : r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem consolidationRequest_observations_determine (r s : ConsolidationRequest)
    (h : consolidationRequestObserve r = consolidationRequestObserve s) : r = s := by
  simp only [consolidationRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2⟩
  apply consolidationRequest_fields_determine
  simp only [consolidationRequestFields, Prod.mk.injEq]
  exact ⟨Address.toBytes_inj.mp (Bytes.ext h0),
    FixedBytes.toBytes_inj.mp (Bytes.ext h1),
    FixedBytes.toBytes_inj.mp (Bytes.ext h2)⟩

private theorem consolidationRequest_update_sourceAddress (r : ConsolidationRequest)
  (value : Address) :
    { r with sourceAddress := value } =
      ConsolidationRequest.mk value r.sourcePubkey r.targetPubkey := rfl

private theorem consolidationRequest_observe_update_sourceAddress (r : ConsolidationRequest)
  (value : Address) :
    consolidationRequestObserve { r with sourceAddress := value } =
      (value.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList) := rfl

private theorem consolidationRequest_update_sourcePubkey (r : ConsolidationRequest)
  (value : Bytes48) :
    { r with sourcePubkey := value } =
      ConsolidationRequest.mk r.sourceAddress value r.targetPubkey := rfl

private theorem consolidationRequest_observe_update_sourcePubkey (r : ConsolidationRequest)
  (value : Bytes48) :
    consolidationRequestObserve { r with sourcePubkey := value } =
      (r.sourceAddress.toBytes.toList, value.toBytes.toList, r.targetPubkey.toBytes.toList) := rfl

private theorem consolidationRequest_update_targetPubkey (r : ConsolidationRequest)
  (value : Bytes48) :
    { r with targetPubkey := value } =
      ConsolidationRequest.mk r.sourceAddress r.sourcePubkey value := rfl

private theorem consolidationRequest_observe_update_targetPubkey (r : ConsolidationRequest)
  (value : Bytes48) :
    consolidationRequestObserve { r with targetPubkey := value } =
      (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, value.toBytes.toList) := rfl

private theorem consolidationRequest_sourceAddress_model (r : ConsolidationRequest) :
    Address.ofBytes? r.sourceAddress.toBytes = some r.sourceAddress ∧
      r.sourceAddress.toBytes.size = 20 ∧ r.sourceAddress.toNat < 2 ^ (8 * 20) :=
  ⟨Address.ofBytes?_toBytes _, Address.size_toBytes _, Address.toNat_lt _⟩

private theorem consolidationRequest_sourcePubkey_model (r : ConsolidationRequest) :
    FixedBytes.ofBytes? r.sourcePubkey.toBytes = some r.sourcePubkey ∧
      r.sourcePubkey.toBytes.size = 48 ∧ r.sourcePubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem consolidationRequest_targetPubkey_model (r : ConsolidationRequest) :
    FixedBytes.ofBytes? r.targetPubkey.toBytes = some r.targetPubkey ∧
      r.targetPubkey.toBytes.size = 48 ∧ r.targetPubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private def builderDepositRequestConstructor : Bytes48 → Bytes32 → U64 → Bytes96 →
  BuilderDepositRequest :=
  BuilderDepositRequest.mk

private def builderDepositRequestPubkey : BuilderDepositRequest → Bytes48 :=
  BuilderDepositRequest.pubkey
private def builderDepositRequestWithdrawalCredentials : BuilderDepositRequest → Bytes32 :=
  BuilderDepositRequest.withdrawalCredentials
private def builderDepositRequestAmount : BuilderDepositRequest → U64 :=
  BuilderDepositRequest.amount
private def builderDepositRequestSignature : BuilderDepositRequest → Bytes96 :=
  BuilderDepositRequest.signature

private def builderDepositRequestFields (r : BuilderDepositRequest) : Bytes48 × Bytes32 × U64 ×
  Bytes96 :=
  (r.pubkey, r.withdrawalCredentials, r.amount, r.signature)

private def builderDepositRequestObserve (r : BuilderDepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList)

private theorem builderDepositRequest_constructor (pubkey : Bytes48)
  (withdrawalCredentials : Bytes32) (amount : U64) (signature : Bytes96) :
    builderDepositRequestFields (builderDepositRequestConstructor pubkey withdrawalCredentials
      amount signature) = (pubkey, withdrawalCredentials, amount, signature) := rfl

private theorem builderDepositRequest_reconstruction (r : BuilderDepositRequest) :
    BuilderDepositRequest.mk r.pubkey r.withdrawalCredentials r.amount r.signature = r := rfl

private theorem builderDepositRequest_fields_determine (r s : BuilderDepositRequest)
    (h : builderDepositRequestFields r = builderDepositRequestFields s) : r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem builderDepositRequest_observations_determine (r s : BuilderDepositRequest)
    (h : builderDepositRequestObserve r = builderDepositRequestObserve s) : r = s := by
  simp only [builderDepositRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  apply builderDepositRequest_fields_determine
  simp only [builderDepositRequestFields, Prod.mk.injEq]
  exact ⟨FixedBytes.toBytes_inj.mp (Bytes.ext h0),
    FixedBytes.toBytes_inj.mp (Bytes.ext h1),
    U64.toNat_inj.mp h2,
    FixedBytes.toBytes_inj.mp (Bytes.ext h3)⟩

private theorem builderDepositRequest_update_pubkey (r : BuilderDepositRequest) (value : Bytes48) :
    { r with pubkey := value } = BuilderDepositRequest.mk value r.withdrawalCredentials r.amount
      r.signature := rfl

private theorem builderDepositRequest_observe_update_pubkey (r : BuilderDepositRequest)
  (value : Bytes48) :
    builderDepositRequestObserve { r with pubkey := value } =
      (value.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
        r.signature.toBytes.toList) := rfl

private theorem builderDepositRequest_update_withdrawalCredentials (r : BuilderDepositRequest)
  (value : Bytes32) :
    { r with withdrawalCredentials := value } = BuilderDepositRequest.mk r.pubkey value r.amount
      r.signature := rfl

private theorem builderDepositRequest_observe_update_withdrawalCredentials
  (r : BuilderDepositRequest) (value : Bytes32) :
    builderDepositRequestObserve { r with withdrawalCredentials := value } =
      (r.pubkey.toBytes.toList, value.toBytes.toList, r.amount.toNat,
        r.signature.toBytes.toList) := rfl

private theorem builderDepositRequest_update_amount (r : BuilderDepositRequest) (value : U64) :
    { r with amount := value } = BuilderDepositRequest.mk r.pubkey r.withdrawalCredentials value
      r.signature := rfl

private theorem builderDepositRequest_observe_update_amount (r : BuilderDepositRequest)
  (value : U64) :
    builderDepositRequestObserve { r with amount := value } =
      (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, value.toNat,
        r.signature.toBytes.toList) := rfl

private theorem builderDepositRequest_update_signature (r : BuilderDepositRequest)
  (value : Bytes96) :
    { r with signature := value } = BuilderDepositRequest.mk r.pubkey r.withdrawalCredentials
      r.amount value := rfl

private theorem builderDepositRequest_observe_update_signature (r : BuilderDepositRequest)
  (value : Bytes96) :
    builderDepositRequestObserve { r with signature := value } =
      (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
        value.toBytes.toList) := rfl

private theorem builderDepositRequest_pubkey_model (r : BuilderDepositRequest) :
    FixedBytes.ofBytes? r.pubkey.toBytes = some r.pubkey ∧
      r.pubkey.toBytes.size = 48 ∧ r.pubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem builderDepositRequest_withdrawalCredentials_model (r : BuilderDepositRequest) :
    FixedBytes.ofBytes? r.withdrawalCredentials.toBytes = some r.withdrawalCredentials ∧
      r.withdrawalCredentials.toBytes.size = 32 ∧ r.withdrawalCredentials.toNat < 2 ^ (8 * 32) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private theorem builderDepositRequest_amount_model (r : BuilderDepositRequest) :
    U64.ofNat? r.amount.toNat = some r.amount ∧
      r.amount.toNat < 2 ^ 64 ∧ r.amount.toNat = r.amount.toBitVec.toNat :=
  ⟨U64.ofNat?_toNat _, U64.toNat_lt _, U64.toNat_def _⟩

private theorem builderDepositRequest_signature_model (r : BuilderDepositRequest) :
    FixedBytes.ofBytes? r.signature.toBytes = some r.signature ∧
      r.signature.toBytes.size = 96 ∧ r.signature.toNat < 2 ^ (8 * 96) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

private def builderExitRequestConstructor : Address → Bytes48 → BuilderExitRequest :=
  BuilderExitRequest.mk

private def builderExitRequestSourceAddress : BuilderExitRequest → Address :=
  BuilderExitRequest.sourceAddress
private def builderExitRequestPubkey : BuilderExitRequest → Bytes48 := BuilderExitRequest.pubkey

private def builderExitRequestFields (r : BuilderExitRequest) : Address × Bytes48 :=
  (r.sourceAddress, r.pubkey)

private def builderExitRequestObserve (r : BuilderExitRequest) :
    List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.pubkey.toBytes.toList)

private theorem builderExitRequest_constructor (sourceAddress : Address) (pubkey : Bytes48) :
    builderExitRequestFields (builderExitRequestConstructor sourceAddress pubkey) = (sourceAddress,
      pubkey) := rfl

private theorem builderExitRequest_reconstruction (r : BuilderExitRequest) :
    BuilderExitRequest.mk r.sourceAddress r.pubkey = r := rfl

private theorem builderExitRequest_fields_determine (r s : BuilderExitRequest)
    (h : builderExitRequestFields r = builderExitRequestFields s) : r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem builderExitRequest_observations_determine (r s : BuilderExitRequest)
    (h : builderExitRequestObserve r = builderExitRequestObserve s) : r = s := by
  simp only [builderExitRequestObserve, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1⟩
  apply builderExitRequest_fields_determine
  simp only [builderExitRequestFields, Prod.mk.injEq]
  exact ⟨Address.toBytes_inj.mp (Bytes.ext h0),
    FixedBytes.toBytes_inj.mp (Bytes.ext h1)⟩

private theorem builderExitRequest_update_sourceAddress (r : BuilderExitRequest)
  (value : Address) :
    { r with sourceAddress := value } = BuilderExitRequest.mk value r.pubkey := rfl

private theorem builderExitRequest_observe_update_sourceAddress (r : BuilderExitRequest)
  (value : Address) :
    builderExitRequestObserve { r with sourceAddress := value } =
      (value.toBytes.toList, r.pubkey.toBytes.toList) := rfl

private theorem builderExitRequest_update_pubkey (r : BuilderExitRequest) (value : Bytes48) :
    { r with pubkey := value } = BuilderExitRequest.mk r.sourceAddress value := rfl

private theorem builderExitRequest_observe_update_pubkey (r : BuilderExitRequest)
  (value : Bytes48) :
    builderExitRequestObserve { r with pubkey := value } =
      (r.sourceAddress.toBytes.toList, value.toBytes.toList) := rfl

private theorem builderExitRequest_sourceAddress_model (r : BuilderExitRequest) :
    Address.ofBytes? r.sourceAddress.toBytes = some r.sourceAddress ∧
      r.sourceAddress.toBytes.size = 20 ∧ r.sourceAddress.toNat < 2 ^ (8 * 20) :=
  ⟨Address.ofBytes?_toBytes _, Address.size_toBytes _, Address.toNat_lt _⟩

private theorem builderExitRequest_pubkey_model (r : BuilderExitRequest) :
    FixedBytes.ofBytes? r.pubkey.toBytes = some r.pubkey ∧
      r.pubkey.toBytes.size = 48 ∧ r.pubkey.toNat < 2 ^ (8 * 48) :=
  ⟨FixedBytes.ofBytes?_toBytes _, FixedBytes.size_toBytes _, FixedBytes.toNat_lt _⟩

end STFSpec.Conformance.Stateless.RequestItemsCallerProofs
