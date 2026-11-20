/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Defaulted pre-transaction account read clients

Library `EthConformance`: private clients consume only the public action equations,
model law and framing laws. Whole function retention is ordinary equality at Id;
no arbitrary Monad observer, failed-state projection or rollback is introduced.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.State.PreStateAccountDefaultCallerProofs

open STFSpec.State STFSpec.Base

private def exact_type : {m : Type → Type} → [Monad m] →
    Address → STFSpec.State.StateM m (Account) := @getPreStateAccount

private theorem literal_action {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) :
    ((getPreStateAccount a).run t).run = (do
      match ← ((getPreStateAccountOptional a).run t).run with
      | .ok (o, next) => pure (.ok (o.getD (emptyAccount t.block.consts), next))
      | .error e => pure (.error e)) := getPreStateAccount_action t a

private theorem complete_retention (t next : TxState Id) (a : Address) (o : Account)
    (h : ((getPreStateAccount a).run t).run = .ok (o, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.block.preState = t.block.preState ∧
      next.block.preState.getAccount? = t.block.preState.getAccount? ∧
      next.block.preState.getStorage = t.block.preState.getStorage ∧
      next.block.preState.getCode = t.block.preState.getCode ∧
      next.block.preState.stateRoot = t.block.preState.stateRoot ∧
      next.block.consts = t.block.consts ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.codeReads = t.obs.codeReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  obtain ⟨hb, hr, hs, hc, hcreated⟩ := getPreStateAccount_frames t a o next h
  exact ⟨hb, hr, congrArg BlockState.preState hb,
    congrArg (fun b ↦ b.preState.getAccount?) hb,
    congrArg (fun b ↦ b.preState.getStorage) hb,
    congrArg (fun b ↦ b.preState.getCode) hb,
    congrArg (fun b ↦ b.preState.stateRoot) hb,
    congrArg BlockState.consts hb, hs, hc, hcreated⟩

private theorem queried_member (t next : TxState Id) (a : Address) (o : Account)
    (h : ((getPreStateAccount a).run t).run = .ok (o, next)) :
    a ∈ next.obs.accountReads :=
  (getPreStateAccount_mem t a a o next h).mpr (Or.inl rfl)

private theorem old_member (t next : TxState Id) (a b : Address) (o : Account)
    (h : ((getPreStateAccount a).run t).run = .ok (o, next))
    (hb : b ∈ t.obs.accountReads) : b ∈ next.obs.accountReads :=
  (getPreStateAccount_mem t a b o next h).mpr (Or.inr hb)

private theorem only_members (t next : TxState Id) (a b : Address) (o : Account)
    (h : ((getPreStateAccount a).run t).run = .ok (o, next))
    (hb : b ∈ next.obs.accountReads) : b = a ∨ b ∈ t.obs.accountReads :=
  (getPreStateAccount_mem t a b o next h).mp hb

private theorem exact_error (t : TxState Id) (a : Address) (e : WitnessError)
    (hb : t.block.accountWrites[a]? = none)
    (hp : t.block.preState.getAccount? a = .error e) :
    ((getPreStateAccount a).run t).run = .error (.witness e) :=
  getPreStateAccount_error t a e hb hp

private theorem model_client (t next : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀) (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (o : Account)
    (h : ((getPreStateAccount a).run t).run = .ok (o, next)) :
    o = ((t.block.view σ₀).account? a).getD (emptyAccount t.block.consts) :=
  getPreStateAccount_model t σ₀ hwf hm a o next h

end STFSpec.Conformance.State.PreStateAccountDefaultCallerProofs
