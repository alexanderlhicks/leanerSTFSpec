/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual request-item schema clients

Library `EthConformance`. Private clients consume all five named dictionaries and
all fifteen complete certificates through the public Stateless facade.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.RequestItemSszCallerProofs

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

namespace DepositRequest

private abbrev actual : SszSchema DepositRequest := STFSpec.Stateless.DepositRequest.instSszSchema

private theorem descriptor : actual.type = .container [.byteVector 48, .byteVector 32, .uint 8,
  .byteVector 96, .uint 8] := rfl

private theorem names : actual.fieldNames = ["pubkey", "withdrawal_credentials", "amount",
  "signature", "index"] := rfl

private theorem validity (a : DepositRequest) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : DepositRequest) :
    actual.toValue a = .container [.bytes a.pubkey.toBytes.toByteArray,
      .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
      .bytes a.signature.toBytes.toByteArray, .uint a.index.toNat] := rfl

private theorem wf : actual.type.WellFormed := STFSpec.Stateless.DepositRequest.ssz_type_wellFormed

private theorem forward : ∀ (a : DepositRequest), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  STFSpec.Stateless.DepositRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : DepositRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := STFSpec.Stateless.DepositRequest.ssz_toValue_ofValue

private theorem full_recovery (pubkey : FixedBytes 48) (withdrawalCredentials : FixedBytes 32)
  (amount : U64) (signature : FixedBytes 96) (index : U64) :
    actual.ofValue? (.container [.bytes pubkey.toBytes.toByteArray,
      .bytes withdrawalCredentials.toBytes.toByteArray, .uint amount.toNat,
      .bytes signature.toBytes.toByteArray,
      .uint index.toNat]) = some (DepositRequest.mk pubkey withdrawalCredentials amount signature
      index) :=
  (forward (DepositRequest.mk pubkey withdrawalCredentials amount signature index) True.intro).1

private theorem recovered_reforward (v : SszValue) (a : DepositRequest)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem count_recovery (a : DepositRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.DepositRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _), Ssz.countRecoverable_iff (.uint _)
      (.uint _)]

private theorem fixed_size : actual.type.fixedSize? = some 192 := by
  dsimp only [actual, SszSchema.type, STFSpec.Stateless.DepositRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

end DepositRequest

namespace WithdrawalRequest

private abbrev actual : SszSchema WithdrawalRequest :=
  STFSpec.Stateless.WithdrawalRequest.instSszSchema

private theorem descriptor : actual.type = .container [.byteVector 20, .byteVector 48,
  .uint 8] := rfl

private theorem names : actual.fieldNames = ["source_address", "validator_pubkey", "amount"] := rfl

private theorem validity (a : WithdrawalRequest) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : WithdrawalRequest) :
    actual.toValue a = .container [.bytes a.sourceAddress.toBytes.toByteArray,
      .bytes a.validatorPubkey.toBytes.toByteArray, .uint a.amount.toNat] := rfl

private theorem wf : actual.type.WellFormed :=
  STFSpec.Stateless.WithdrawalRequest.ssz_type_wellFormed

private theorem forward : ∀ (a : WithdrawalRequest), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  STFSpec.Stateless.WithdrawalRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : WithdrawalRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v :=
        STFSpec.Stateless.WithdrawalRequest.ssz_toValue_ofValue

private theorem full_recovery (sourceAddress : Address) (validatorPubkey : FixedBytes 48)
  (amount : U64) :
    actual.ofValue? (.container [.bytes sourceAddress.toBytes.toByteArray,
      .bytes validatorPubkey.toBytes.toByteArray,
      .uint amount.toNat]) = some (WithdrawalRequest.mk sourceAddress validatorPubkey amount) :=
  (forward (WithdrawalRequest.mk sourceAddress validatorPubkey amount) True.intro).1

private theorem recovered_reforward (v : SszValue) (a : WithdrawalRequest)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem count_recovery (a : WithdrawalRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.WithdrawalRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _), Ssz.countRecoverable_iff (.uint _)
      (.uint _)]

private theorem fixed_size : actual.type.fixedSize? = some 76 := by
  dsimp only [actual, SszSchema.type, STFSpec.Stateless.WithdrawalRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

end WithdrawalRequest

namespace ConsolidationRequest

private abbrev actual : SszSchema ConsolidationRequest :=
  STFSpec.Stateless.ConsolidationRequest.instSszSchema

private theorem descriptor : actual.type = .container [.byteVector 20, .byteVector 48,
  .byteVector 48] := rfl

private theorem names : actual.fieldNames = ["source_address", "source_pubkey",
  "target_pubkey"] := rfl

private theorem validity (a : ConsolidationRequest) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : ConsolidationRequest) :
    actual.toValue a = .container [.bytes a.sourceAddress.toBytes.toByteArray,
      .bytes a.sourcePubkey.toBytes.toByteArray, .bytes a.targetPubkey.toBytes.toByteArray] := rfl

private theorem wf : actual.type.WellFormed :=
  STFSpec.Stateless.ConsolidationRequest.ssz_type_wellFormed

private theorem forward : ∀ (a : ConsolidationRequest), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  STFSpec.Stateless.ConsolidationRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : ConsolidationRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v :=
        STFSpec.Stateless.ConsolidationRequest.ssz_toValue_ofValue

private theorem full_recovery (sourceAddress : Address) (sourcePubkey : FixedBytes 48)
  (targetPubkey : FixedBytes 48) :
    actual.ofValue? (.container [.bytes sourceAddress.toBytes.toByteArray,
      .bytes sourcePubkey.toBytes.toByteArray,
      .bytes targetPubkey.toBytes.toByteArray]) = some (ConsolidationRequest.mk sourceAddress
      sourcePubkey targetPubkey) :=
  (forward (ConsolidationRequest.mk sourceAddress sourcePubkey targetPubkey) True.intro).1

private theorem recovered_reforward (v : SszValue) (a : ConsolidationRequest)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem count_recovery (a : ConsolidationRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.ConsolidationRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _)]

private theorem fixed_size : actual.type.fixedSize? = some 116 := by
  dsimp only [actual, SszSchema.type, STFSpec.Stateless.ConsolidationRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _)]

end ConsolidationRequest

namespace BuilderDepositRequest

private abbrev actual : SszSchema BuilderDepositRequest :=
  STFSpec.Stateless.BuilderDepositRequest.instSszSchema

private theorem descriptor : actual.type = .container [.byteVector 48, .byteVector 32, .uint 8,
  .byteVector 96] := rfl

private theorem names : actual.fieldNames = ["pubkey", "withdrawal_credentials", "amount",
  "signature"] := rfl

private theorem validity (a : BuilderDepositRequest) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : BuilderDepositRequest) :
    actual.toValue a = .container [.bytes a.pubkey.toBytes.toByteArray,
      .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
      .bytes a.signature.toBytes.toByteArray] := rfl

private theorem wf : actual.type.WellFormed :=
  STFSpec.Stateless.BuilderDepositRequest.ssz_type_wellFormed

private theorem forward : ∀ (a : BuilderDepositRequest), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  STFSpec.Stateless.BuilderDepositRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : BuilderDepositRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v :=
        STFSpec.Stateless.BuilderDepositRequest.ssz_toValue_ofValue

private theorem full_recovery (pubkey : FixedBytes 48) (withdrawalCredentials : FixedBytes 32)
  (amount : U64) (signature : FixedBytes 96) :
    actual.ofValue? (.container [.bytes pubkey.toBytes.toByteArray,
      .bytes withdrawalCredentials.toBytes.toByteArray, .uint amount.toNat,
      .bytes signature.toBytes.toByteArray]) = some (BuilderDepositRequest.mk pubkey
      withdrawalCredentials amount signature) :=
  (forward (BuilderDepositRequest.mk pubkey withdrawalCredentials amount signature) True.intro).1

private theorem recovered_reforward (v : SszValue) (a : BuilderDepositRequest)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem count_recovery (a : BuilderDepositRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderDepositRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _), Ssz.countRecoverable_iff (.uint _)
      (.uint _)]

private theorem fixed_size : actual.type.fixedSize? = some 184 := by
  dsimp only [actual, SszSchema.type, STFSpec.Stateless.BuilderDepositRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

end BuilderDepositRequest

namespace BuilderExitRequest

private abbrev actual : SszSchema BuilderExitRequest :=
  STFSpec.Stateless.BuilderExitRequest.instSszSchema

private theorem descriptor : actual.type = .container [.byteVector 20, .byteVector 48] := rfl

private theorem names : actual.fieldNames = ["source_address", "pubkey"] := rfl

private theorem validity (a : BuilderExitRequest) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : BuilderExitRequest) :
    actual.toValue a = .container [.bytes a.sourceAddress.toBytes.toByteArray,
      .bytes a.pubkey.toBytes.toByteArray] := rfl

private theorem wf : actual.type.WellFormed :=
  STFSpec.Stateless.BuilderExitRequest.ssz_type_wellFormed

private theorem forward : ∀ (a : BuilderExitRequest), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  STFSpec.Stateless.BuilderExitRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : BuilderExitRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v :=
        STFSpec.Stateless.BuilderExitRequest.ssz_toValue_ofValue

private theorem full_recovery (sourceAddress : Address) (pubkey : FixedBytes 48) :
    actual.ofValue? (.container [.bytes sourceAddress.toBytes.toByteArray,
      .bytes pubkey.toBytes.toByteArray]) = some (BuilderExitRequest.mk sourceAddress pubkey) :=
  (forward (BuilderExitRequest.mk sourceAddress pubkey) True.intro).1

private theorem recovered_reforward (v : SszValue) (a : BuilderExitRequest)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem count_recovery (a : BuilderExitRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderExitRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _)]

private theorem fixed_size : actual.type.fixedSize? = some 68 := by
  dsimp only [actual, SszSchema.type, STFSpec.Stateless.BuilderExitRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _)]

end BuilderExitRequest

end STFSpec.Conformance.Stateless.RequestItemSszCallerProofs
