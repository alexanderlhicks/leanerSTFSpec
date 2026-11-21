/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Code read clients

Library `EthConformance`. Private clients use the five public code-read laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` §7.1.
-/

namespace STFSpec.Conformance.State.CodeCallerProofs

open STFSpec.Base STFSpec.State

private def exact_type : {m : Type → Type} → [Monad m] →
    Hash32 → STFSpec.State.StateM m ByteArray := @getCode

private theorem reserved {m : Type → Type} [Monad m] (t : TxState m) :
    ((getCode t.block.consts.emptyCodeHash).run t).run =
      pure (.ok (ByteArray.empty, t)) := by
  rw [getCode_action, ite_eq_left rfl]

private theorem provider_action {m : Type → Type} [Monad m]
    (t : TxState m) (h : Hash32) (hh : h ≠ t.block.consts.emptyCodeHash)
    (ht : t.rev.codeWrites[h]? = none) (hb : t.block.codeWrites[h]? = none) :
    ((getCode h).run t).run = (do
      let next := { t with obs.codeReads := t.obs.codeReads.insert h }
      match ← t.block.preState.getCode h with
      | .ok bytes => pure (.ok (bytes, next))
      | .error e => pure (.error (.witness e))) := by
  rw [getCode_action, ite_eq_right hh, ht, hb]
  rfl

private theorem exact_error (t : TxState Id) (h : Hash32) (e : WitnessError)
    (hh : h ≠ t.block.consts.emptyCodeHash)
    (ht : t.rev.codeWrites[h]? = none) (hb : t.block.codeWrites[h]? = none)
    (hp : t.block.preState.getCode h = .error e) :
    ((getCode h).run t).run = .error (.witness e) :=
  getCode_error t h e hh ht hb hp

private theorem retained (t next : TxState Id) (h : Hash32) (code : ByteArray)
    (hs : ((getCode h).run t).run = .ok (code, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.block.preState = t.block.preState ∧ next.block.consts = t.block.consts ∧
      next.obs.accountReads = t.obs.accountReads ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  obtain ⟨hb, hr, ha, hs, hc⟩ := getCode_frames t h code next hs
  exact ⟨hb, hr, congrArg BlockState.preState hb, congrArg BlockState.consts hb, ha, hs, hc⟩

private theorem new_member_iff (t next : TxState Id) (h k : Hash32) (code : ByteArray)
    (hs : ((getCode h).run t).run = .ok (code, next)) (old : k ∉ t.obs.codeReads) :
    k ∈ next.obs.codeReads ↔ k = h ∧ h ≠ t.block.consts.emptyCodeHash ∧
      t.rev.codeWrites[h]? = none ∧ t.block.codeWrites[h]? = none := by
  rw [getCode_mem t h k code next hs]
  exact ⟨fun member ↦ member.elim (fun previous ↦ (old previous).elim) id, Or.inr⟩

private theorem model_client (t next : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀) (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (h : Hash32) (code : ByteArray)
    (hs : ((getCode h).run t).run = .ok (code, next)) :
    (t.view σ₀).code? t.block.consts h = some code :=
  getCode_model t σ₀ hwf hm h code next hs

end STFSpec.Conformance.State.CodeCallerProofs
