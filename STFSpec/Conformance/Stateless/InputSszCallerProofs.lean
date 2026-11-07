/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual stateless input schema clients

Library `EthConformance`. Private facade clients check actual providers, complete
models and the exact three certificates. Count and layout are separate domains.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.InputSszCallerProofs

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

private abbrev actual : SszSchema StatelessInput := StatelessInput.instSszSchema

private theorem inferred : (inferInstance : SszSchema StatelessInput) = actual := rfl

private theorem descriptor : actual.type = .container [NewPayloadRequest.instSszSchema.type,
    ExecutionWitness.instSszSchema.type, .uint 8] := rfl

private theorem names : actual.fieldNames = ["new_payload_request", "witness", "chain_id"] := rfl

private theorem validity (a : StatelessInput) : actual.valid a ↔
    NewPayloadRequest.instSszSchema.valid a.newPayloadRequest ∧
      ExecutionWitness.instSszSchema.valid a.witness := Iff.rfl

private theorem complete_model (a : StatelessInput) : actual.toValue a = .container [
    NewPayloadRequest.instSszSchema.toValue a.newPayloadRequest,
    ExecutionWitness.instSszSchema.toValue a.witness, .uint a.chainId.toNat] := rfl

private theorem wf : actual.type.WellFormed := StatelessInput.ssz_type_wellFormed

private theorem forward : ∀ a : StatelessInput, actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) := StatelessInput.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : StatelessInput),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := StatelessInput.ssz_toValue_ofValue

private theorem arbitrary_construction (r : NewPayloadRequest) (w : ExecutionWitness) (c : U64)
    (hr : NewPayloadRequest.instSszSchema.valid r)
    (hw : ExecutionWitness.instSszSchema.valid w) :
    actual.ofValue? (.container [NewPayloadRequest.instSszSchema.toValue r,
      ExecutionWitness.instSszSchema.toValue w, .uint c.toNat]) = some (StatelessInput.mk r w c) ∧
    SszValue.WellTyped actual.type (actual.toValue (StatelessInput.mk r w c)) :=
  forward (StatelessInput.mk r w c) ⟨hr, hw⟩

private theorem recovered_reforward (v : SszValue) (a : StatelessInput)
    (ht : SszValue.WellTyped actual.type v) (hs : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, hs⟩

private theorem whole_recovery (a : StatelessInput) (hv : actual.valid a) :
    (actual.ofValue? (actual.toValue a)).map (fun b ↦
      (b.newPayloadRequest, b.witness, b.chainId)) =
      some (a.newPayloadRequest, a.witness, a.chainId) := by
  rw [(forward a hv).1]
  rfl

private theorem head_slots :
    (match actual.type with
    | .container fs => fs.map (fun f ↦ f.fixedSize?.getD 4)
    | _ => []) = [4, 4, 8] := by decide

private theorem head_size : ([4, 4, 8] : List Nat).sum = 16 := by decide

private theorem emitted_starts (r w : Nat) :
    (([NewPayloadRequest.instSszSchema.type, ExecutionWitness.instSszSchema.type,
      .uint 8].zip [r, w, 8]).foldl
      (fun (s : Nat × List Nat) q ↦ match q.1.fixedSize? with
        | some _ => s
        | none => (s.1 + q.2, s.2 ++ [s.1])) (16, [])).2 = [16, 16 + r] := rfl

private theorem outer_start_bound (r : Nat) :
    (∀ o ∈ [16, 16 + r], o < 2 ^ 32) ↔ 16 + r < 2 ^ 32 := by
  constructor
  · intro h
    exact h (16 + r) (by simp)
  · intro h o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · decide
    · exact h

-- The final witness end is absent from this condition; child support stays separate.
private theorem unbounded_final_end (w : Nat) :
    (∀ o ∈ [16, 16 + (2 ^ 32 - 17)], o < 2 ^ 32) ∧
      16 + (2 ^ 32 - 17) + (w + 1) ≥ 2 ^ 32 := by
  constructor
  · decide
  · omega

private theorem rejected_second_start :
    ¬ (∀ o ∈ [16, 16 + (2 ^ 32 - 16)], o < 2 ^ 32) := by decide

private theorem count_recovery (a : StatelessInput) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue, StatelessInput.instSszSchema,
    NewPayloadRequest.instSszSchema,
    ExecutionWitness.instSszSchema,
    ExecutionPayload.instSszSchema, ExecutionRequests.instSszSchema,
    DepositRequest.instSszSchema, WithdrawalRequest.instSszSchema,
    ConsolidationRequest.instSszSchema, BuilderDepositRequest.instSszSchema,
    BuilderExitRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff (.progressiveByteList) (.bytes _),
    SszType.fixedSize?_eq (.progressiveByteList), SszType.fixedSize?_eq (.byteList _),
    SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _)]

end STFSpec.Conformance.Stateless.InputSszCallerProofs
