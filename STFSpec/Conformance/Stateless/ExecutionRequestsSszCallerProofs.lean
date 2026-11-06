/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual aggregate schema clients

Library `EthConformance`. Private facade clients retain complete models and use
all three actual certificates. Count recovery uses only public Codec equations.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionRequestsSszCallerProofs

open STFSpec.Stateless STFSpec.Codec

private abbrev actual : SszSchema ExecutionRequests := ExecutionRequests.instSszSchema

private theorem inferred : (inferInstance : SszSchema ExecutionRequests) = actual := rfl

private theorem descriptor : actual.type = .progressiveContainer [true, true, true, true, true] [
  .progressiveList DepositRequest.instSszSchema.type,
  .progressiveList WithdrawalRequest.instSszSchema.type,
  .progressiveList ConsolidationRequest.instSszSchema.type,
  .progressiveList BuilderDepositRequest.instSszSchema.type,
  .progressiveList BuilderExitRequest.instSszSchema.type] := rfl

private theorem names : actual.fieldNames =
  ["deposits", "withdrawals", "consolidations", "builder_deposits", "builder_exits"] := rfl

private theorem validity (a : ExecutionRequests) : actual.valid a ↔ True := Iff.rfl

private theorem full_model (a : ExecutionRequests) : actual.toValue a = .container [
  .list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
  .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
  .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
  .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
  .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)] := rfl

private theorem wf : actual.type.WellFormed := ExecutionRequests.ssz_type_wellFormed

private theorem forward : ∀ (a : ExecutionRequests), actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) := ExecutionRequests.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : ExecutionRequests),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := ExecutionRequests.ssz_toValue_ofValue

private theorem all_arrays (ds : Array DepositRequest) (ws : Array WithdrawalRequest)
    (cs : Array ConsolidationRequest) (bs : Array BuilderDepositRequest)
    (es : Array BuilderExitRequest) :
    actual.ofValue? (.container [.list (ds.toList.map DepositRequest.instSszSchema.toValue),
      .list (ws.toList.map WithdrawalRequest.instSszSchema.toValue),
      .list (cs.toList.map ConsolidationRequest.instSszSchema.toValue),
      .list (bs.toList.map BuilderDepositRequest.instSszSchema.toValue),
      .list (es.toList.map BuilderExitRequest.instSszSchema.toValue)]) =
      some (ExecutionRequests.mk ds ws cs bs es) :=
  (forward (ExecutionRequests.mk ds ws cs bs es) trivial).1

private theorem array_recovery (a : ExecutionRequests) :
    (actual.ofValue? (actual.toValue a)).map (fun b =>
      (b.deposits, b.withdrawals, b.consolidations, b.builderDeposits, b.builderExits)) =
      some (a.deposits, a.withdrawals, a.consolidations, a.builderDeposits, a.builderExits) := by
  rw [(forward a trivial).1]
  rfl

private theorem reforward (v : SszValue) (a : ExecutionRequests)
    (ht : SszValue.WellTyped actual.type v) (hs : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, hs⟩

namespace DepositRequest

private abbrev actual : SszSchema DepositRequest := STFSpec.Stateless.DepositRequest.instSszSchema

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

private abbrev actual : SszSchema WithdrawalRequest := STFSpec.Stateless.WithdrawalRequest.instSszSchema

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

private abbrev actual : SszSchema ConsolidationRequest := STFSpec.Stateless.ConsolidationRequest.instSszSchema

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

private abbrev actual : SszSchema BuilderDepositRequest := STFSpec.Stateless.BuilderDepositRequest.instSszSchema

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

private abbrev actual : SszSchema BuilderExitRequest := STFSpec.Stateless.BuilderExitRequest.instSszSchema

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

private theorem list_recovery {α : Type} (s : SszSchema α) (xs : List α)
    (hf : s.type.fixedSize? ≠ some 0)
    (hr : ∀ a, Ssz.CountRecoverable s.type (s.toValue a)) :
    Ssz.CountRecoverable (.progressiveList s.type) (.list (xs.map s.toValue)) := by
  apply (Ssz.countRecoverable_iff _ _).mpr
  refine ⟨hf, ?_⟩
  intro v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  exact hr a

private theorem count_recovery (a : ExecutionRequests) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  rw [descriptor, full_model]
  apply (Ssz.countRecoverable_iff _ _).mpr
  constructor
  · rfl
  · simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact list_recovery STFSpec.Stateless.DepositRequest.instSszSchema a.deposits.toList
        (by rw [DepositRequest.fixed_size]; decide) DepositRequest.count_recovery
    · exact list_recovery STFSpec.Stateless.WithdrawalRequest.instSszSchema a.withdrawals.toList
        (by rw [WithdrawalRequest.fixed_size]; decide) WithdrawalRequest.count_recovery
    · exact list_recovery STFSpec.Stateless.ConsolidationRequest.instSszSchema a.consolidations.toList
        (by rw [ConsolidationRequest.fixed_size]; decide) ConsolidationRequest.count_recovery
    · exact list_recovery STFSpec.Stateless.BuilderDepositRequest.instSszSchema a.builderDeposits.toList
        (by rw [BuilderDepositRequest.fixed_size]; decide) BuilderDepositRequest.count_recovery
    · exact list_recovery STFSpec.Stateless.BuilderExitRequest.instSszSchema a.builderExits.toList
        (by rw [BuilderExitRequest.fixed_size]; decide) BuilderExitRequest.count_recovery

end STFSpec.Conformance.Stateless.ExecutionRequestsSszCallerProofs
