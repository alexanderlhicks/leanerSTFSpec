/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.ExecutionRequests
import STFSpec.Stateless.RequestItemSsz
import Init.Data.Array.Lemmas

/-!
# Execution-request aggregate SSZ schema

Library `EthStateless`. Five ordered progressive lists use the actual item
schemas. Certificates concern complete payload models and adapter inversion.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless.ExecutionRequests

open Codec

variable {α : Type}

private def members? (s : SszSchema α) : List SszValue → Option (List α)
  | [] => some []
  | v :: vs => do
      let a ← s.ofValue? v
      let rest ← members? s vs
      pure (a :: rest)

private def fromValue? : SszValue → Option ExecutionRequests
  | .container [.list ds, .list ws, .list cs, .list bs, .list es] => do
      let ds ← members? DepositRequest.instSszSchema ds
      let ws ← members? WithdrawalRequest.instSszSchema ws
      let cs ← members? ConsolidationRequest.instSszSchema cs
      let bs ← members? BuilderDepositRequest.instSszSchema bs
      let es ← members? BuilderExitRequest.instSszSchema es
      pure ⟨ds.toArray, ws.toArray, cs.toArray, bs.toArray, es.toArray⟩
  | _ => none

/-- Actual progressive aggregate metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:99–116` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity is mathematical wire
payload typing, without count, host or protocol conditions. -/
instance instSszSchema : SszSchema ExecutionRequests where
  type := .progressiveContainer [true, true, true, true, true] [
    .progressiveList DepositRequest.instSszSchema.type,
    .progressiveList WithdrawalRequest.instSszSchema.type,
    .progressiveList ConsolidationRequest.instSszSchema.type,
    .progressiveList BuilderDepositRequest.instSszSchema.type,
    .progressiveList BuilderExitRequest.instSszSchema.type]
  fieldNames := ["deposits", "withdrawals", "consolidations", "builder_deposits", "builder_exits"]
  valid _ := True
  toValue a := .container [
    .list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
    .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
    .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
    .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
    .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)]
  ofValue? := fromValue?

private theorem members?_forward (s : SszSchema α)
    (h : ∀ a, s.ofValue? (s.toValue a) = some a) (xs : List α) :
    members? s (xs.map s.toValue) = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [members?, h, ih]

private theorem members?_preserves (s : SszSchema α)
    (h : ∀ v a, SszValue.WellTyped s.type v ∧ s.ofValue? v = some a → s.toValue a = v)
    (xs : List SszValue) (ys : List α)
    (ht : ∀ v ∈ xs, SszValue.WellTyped s.type v)
    (hs : members? s xs = some ys) : ys.map s.toValue = xs := by
  induction xs generalizing ys with
  | nil =>
    simp only [members?, Option.some.injEq] at hs
    subst ys
    rfl
  | cons v xs ih =>
    cases hv : s.ofValue? v with
    | none => simp [members?, hv] at hs
    | some a =>
      cases hr : members? s xs with
      | none => simp [members?, hv, hr] at hs
      | some rest =>
        simp [members?, hv, hr] at hs
        subst ys
        rw [List.map_cons, h v a ⟨ht v (by simp), hv⟩]
        congr 1
        exact ih rest (fun x hx => ht x (by simp [hx])) hr

private theorem typed_members (s : SszSchema α)
    (h : ∀ a, SszValue.WellTyped s.type (s.toValue a)) (xs : List α) :
    SszValue.WellTyped (.progressiveList s.type) (.list (xs.map s.toValue)) := by
  apply (SszValue.wellTyped_iff _ _).mpr
  intro v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  exact h a

/-- The actual aggregate descriptor and every actual child are well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  apply (SszType.wellFormed_iff _).mpr
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact (SszType.wellFormed_iff _).mpr DepositRequest.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr WithdrawalRequest.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr ConsolidationRequest.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr BuilderDepositRequest.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr BuilderExitRequest.ssz_type_wellFormed

/-- Every wire-domain aggregate round trips completely and has a well-typed image (Q81).
The hypothesis is the actual dictionary's validity predicate. -/
theorem ssz_ofValue_toValue (a : ExecutionRequests) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  have _ := h
  constructor
  · change fromValue?
      (.container [.list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
        .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
        .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
        .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
        .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)]) = some a
    simp only [fromValue?]
    rw [members?_forward DepositRequest.instSszSchema
      (fun x => (DepositRequest.ssz_ofValue_toValue x trivial).1)]
    rw [members?_forward WithdrawalRequest.instSszSchema
      (fun x => (WithdrawalRequest.ssz_ofValue_toValue x trivial).1)]
    rw [members?_forward ConsolidationRequest.instSszSchema
      (fun x => (ConsolidationRequest.ssz_ofValue_toValue x trivial).1)]
    rw [members?_forward BuilderDepositRequest.instSszSchema
      (fun x => (BuilderDepositRequest.ssz_ofValue_toValue x trivial).1)]
    rw [members?_forward BuilderExitRequest.instSszSchema
      (fun x => (BuilderExitRequest.ssz_ofValue_toValue x trivial).1)]
    cases a
    simp
  · change SszValue.WellTyped (.progressiveContainer [true, true, true, true, true] [
    .progressiveList DepositRequest.instSszSchema.type,
    .progressiveList WithdrawalRequest.instSszSchema.type,
    .progressiveList ConsolidationRequest.instSszSchema.type,
    .progressiveList BuilderDepositRequest.instSszSchema.type,
    .progressiveList BuilderExitRequest.instSszSchema.type])
      (.container [.list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
        .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
        .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
        .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
        .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)])
    rw [SszValue.wellTyped_iff]
    simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact typed_members DepositRequest.instSszSchema
        (fun x => (DepositRequest.ssz_ofValue_toValue x trivial).2) a.deposits.toList
    · exact typed_members WithdrawalRequest.instSszSchema
        (fun x => (WithdrawalRequest.ssz_ofValue_toValue x trivial).2) a.withdrawals.toList
    · exact typed_members ConsolidationRequest.instSszSchema
        (fun x => (ConsolidationRequest.ssz_ofValue_toValue x trivial).2) a.consolidations.toList
    · exact typed_members BuilderDepositRequest.instSszSchema
        (fun x => (BuilderDepositRequest.ssz_ofValue_toValue x trivial).2) a.builderDeposits.toList
    · exact typed_members BuilderExitRequest.instSszSchema
        (fun x => (BuilderExitRequest.ssz_ofValue_toValue x trivial).2) a.builderExits.toList

/-- Well-typed successful reconstruction retains all five complete ordered lists (Q81).
Each child certificate receives both its actual typing and inverse-success premises. -/
theorem ssz_toValue_ofValue (v : SszValue) (a : ExecutionRequests)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v := by
  refine ⟨True.intro, ?_⟩
  have ht := h.1
  have hs := h.2
  change fromValue? v = some a at hs
  unfold fromValue? at hs
  split at hs
  next ds ws cs bs es =>
    change SszValue.WellTyped (.progressiveContainer [true, true, true, true, true] [
      .progressiveList DepositRequest.instSszSchema.type,
      .progressiveList WithdrawalRequest.instSszSchema.type,
      .progressiveList ConsolidationRequest.instSszSchema.type,
      .progressiveList BuilderDepositRequest.instSszSchema.type,
      .progressiveList BuilderExitRequest.instSszSchema.type])
      (.container [.list ds, .list ws, .list cs, .list bs, .list es]) at ht
    rw [SszValue.wellTyped_iff] at ht
    have hts : SszValue.WellTyped (.progressiveList DepositRequest.instSszSchema.type) (.list ds) ∧
        SszValue.WellTyped (.progressiveList WithdrawalRequest.instSszSchema.type) (.list ws) ∧
        SszValue.WellTyped (.progressiveList ConsolidationRequest.instSszSchema.type) (.list cs) ∧
        SszValue.WellTyped (.progressiveList BuilderDepositRequest.instSszSchema.type) (.list bs) ∧
        SszValue.WellTyped (.progressiveList BuilderExitRequest.instSszSchema.type)
          (.list es) := by
      simpa using ht
    cases h0 : members? DepositRequest.instSszSchema ds with
    | none => simp [h0] at hs
    | some x0 =>
      cases h1 : members? WithdrawalRequest.instSszSchema ws with
      | none => simp [h0, h1] at hs
      | some x1 =>
        cases h2 : members? ConsolidationRequest.instSszSchema cs with
        | none => simp [h0, h1, h2] at hs
        | some x2 =>
          cases h3 : members? BuilderDepositRequest.instSszSchema bs with
          | none => simp [h0, h1, h2, h3] at hs
          | some x3 =>
            cases h4 : members? BuilderExitRequest.instSszSchema es with
            | none => simp [h0, h1, h2, h3, h4] at hs
            | some x4 =>
              simp [h0, h1, h2, h3, h4] at hs
              subst a
              change SszValue.container
                [.list (x0.toArray.toList.map DepositRequest.instSszSchema.toValue),
                .list (x1.toArray.toList.map WithdrawalRequest.instSszSchema.toValue),
                .list (x2.toArray.toList.map ConsolidationRequest.instSszSchema.toValue),
                .list (x3.toArray.toList.map BuilderDepositRequest.instSszSchema.toValue),
                .list (x4.toArray.toList.map BuilderExitRequest.instSszSchema.toValue)] = _
              have p0 := members?_preserves DepositRequest.instSszSchema
                (fun v a h => (DepositRequest.ssz_toValue_ofValue v a h).2)
                ds x0 ((SszValue.wellTyped_iff _ _).mp hts.1) h0
              have p1 := members?_preserves WithdrawalRequest.instSszSchema
                (fun v a h => (WithdrawalRequest.ssz_toValue_ofValue v a h).2)
                ws x1 ((SszValue.wellTyped_iff _ _).mp hts.2.1) h1
              have p2 := members?_preserves ConsolidationRequest.instSszSchema
                (fun v a h => (ConsolidationRequest.ssz_toValue_ofValue v a h).2)
                cs x2 ((SszValue.wellTyped_iff _ _).mp hts.2.2.1) h2
              have p3 := members?_preserves BuilderDepositRequest.instSszSchema
                (fun v a h => (BuilderDepositRequest.ssz_toValue_ofValue v a h).2)
                bs x3 ((SszValue.wellTyped_iff _ _).mp hts.2.2.2.1) h3
              have p4 := members?_preserves BuilderExitRequest.instSszSchema
                (fun v a h => (BuilderExitRequest.ssz_toValue_ofValue v a h).2)
                es x4 ((SszValue.wellTyped_iff _ _).mp hts.2.2.2.2) h4
              rw [p0, p1, p2, p3, p4]
  next => contradiction

end STFSpec.Stateless.ExecutionRequests
