/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.Input
import STFSpec.Stateless.NewPayloadSsz
import STFSpec.Stateless.ExecutionWitnessSsz

/-!
# Stateless input SSZ schema

Library `EthStateless`. The ordinary three-field container delegates complete child
models and inverses and checks unsigned chain-ID reconstruction through Base.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless.StatelessInput

open Base Codec

private def fromValue? : SszValue → Option StatelessInput
  | .container [request, witness, .uint chainId] => do
      let request ← NewPayloadRequest.instSszSchema.ofValue? request
      let witness ← ExecutionWitness.instSszSchema.ofValue? witness
      let chainId ← U64.ofNat? chainId
      pure ⟨request, witness, chainId⟩
  | _ => none

/-- Actual ordinary input metadata; EELS `src/ethereum/forks/amsterdam/stateless.py:144–166`
and `src/ethereum/utils/ssz.py:174–320` at the pin. Validity composes actual children. -/
instance instSszSchema : SszSchema StatelessInput where
  type := .container [NewPayloadRequest.instSszSchema.type,
    ExecutionWitness.instSszSchema.type, .uint 8]
  fieldNames := ["new_payload_request", "witness", "chain_id"]
  valid a := NewPayloadRequest.instSszSchema.valid a.newPayloadRequest ∧
    ExecutionWitness.instSszSchema.valid a.witness
  toValue a := .container [NewPayloadRequest.instSszSchema.toValue a.newPayloadRequest,
    ExecutionWitness.instSszSchema.toValue a.witness, .uint a.chainId.toNat]
  ofValue? := fromValue?

/-- The actual ordinary descriptor and both actual children are well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  apply (SszType.wellFormed_iff _).mpr
  refine ⟨by decide, ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact NewPayloadRequest.ssz_type_wellFormed
  · exact ExecutionWitness.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr (by decide)

/-- Every wire-valid input reconstructs completely and has its declared type (Q81). -/
theorem ssz_ofValue_toValue (a : StatelessInput) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  have hr := NewPayloadRequest.ssz_ofValue_toValue a.newPayloadRequest h.1
  have hw := ExecutionWitness.ssz_ofValue_toValue a.witness h.2
  constructor
  · change fromValue? (.container [NewPayloadRequest.instSszSchema.toValue a.newPayloadRequest,
      ExecutionWitness.instSszSchema.toValue a.witness, .uint a.chainId.toNat]) = some a
    simp only [fromValue?]
    rw [hr.1]
    simp only [bind, Option.bind_some]
    rw [hw.1]
    simp only [Option.bind_some, U64.ofNat?_toNat]
    cases a
    rfl
  · apply (SszValue.wellTyped_iff _ _).mpr
    refine ⟨rfl, ?_⟩
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp]
    exact ⟨hr.2, hw.2, (SszValue.wellTyped_iff _ _).mpr (U64.toNat_lt a.chainId),
      by simp⟩

/-- Typed successful reconstruction retains actual child validity and the whole model.
Both actual child reverse certificates receive independently derived WT and success. -/
theorem ssz_toValue_ofValue (v : SszValue) (a : StatelessInput)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v := by
  have ht := h.1
  have hs := h.2
  change fromValue? v = some a at hs
  unfold fromValue? at hs
  split at hs
  next request witness chainId =>
    change SszValue.WellTyped (.container [NewPayloadRequest.instSszSchema.type,
      ExecutionWitness.instSszSchema.type, .uint 8])
      (.container [request, witness, .uint chainId]) at ht
    have typed : SszValue.WellTyped NewPayloadRequest.instSszSchema.type request ∧
        SszValue.WellTyped ExecutionWitness.instSszSchema.type witness ∧
        SszValue.WellTyped (.uint 8) (.uint chainId) := by
      simpa [SszValue.wellTyped_iff (.container _) (.container _)] using ht
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hs
    obtain ⟨request', hr, witness', hw, chainId', hc, he⟩ := hs
    cases he
    have er := NewPayloadRequest.ssz_toValue_ofValue request request' ⟨typed.1, hr⟩
    have ew := ExecutionWitness.ssz_toValue_ofValue witness witness' ⟨typed.2.1, hw⟩
    have ec := (U64.ofNat?_eq_some_iff _ _).mp hc
    refine ⟨⟨er.1, ew.1⟩, ?_⟩
    change SszValue.container [NewPayloadRequest.instSszSchema.toValue request',
      ExecutionWitness.instSszSchema.toValue witness', .uint chainId'.toNat] = _
    rw [er.2, ew.2, ec.2]
  next => contradiction

end STFSpec.Stateless.StatelessInput
