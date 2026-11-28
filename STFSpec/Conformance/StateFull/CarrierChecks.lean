/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateFull

/-!
# Full-state carrier checks

Library `EthConformance`. Clients check the supplied state and proof fields,
including a present account whose code is absent from an authentic table.
Spec guidance: `STFSpec/informal/modules/EthStateFull.md` §§3–5.
-/

namespace STFSpec.Conformance.StateFull.CarrierChecks

open STFSpec.Base STFSpec.State STFSpec.StateCommit STFSpec.StateFull

example (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
    (FullState.ofMath σ hwf hc).σ = σ := rfl

example (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
    (FullState.ofMath σ hwf hc).wf = hwf := rfl

example (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
    (FullState.ofMath σ hwf hc).codeAuthentic = hc := rfl

example (s : FullState) : FullState.ofMath s.σ s.wf s.codeAuthentic = s := by
  cases s
  rfl

private theorem authenticEmptyCode (accounts : Std.ExtTreeMap Address Account) :
    CodeAuthentic ⟨accounts, ∅, ∅⟩ := by
  intro h code found
  rw [MathState.code_mk, Std.ExtTreeMap.getElem?_empty] at found
  cases found

example : (FullState.ofMath ⟨∅, ∅, ∅⟩ MathState.wf_empty (authenticEmptyCode ∅)).σ =
    MathState.mk ∅ ∅ ∅ := rfl

private def address : Address := Address.ofNat 1
private def codeHash : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 1)
private def account : Account := ⟨1, U256.zero, codeHash⟩
private def accounts : Std.ExtTreeMap Address Account :=
  (∅ : Std.ExtTreeMap Address Account).insert address account

private theorem wfWithoutStorage : MathState.WF ⟨accounts, ∅, ∅⟩ := by
  rw [MathState.wf_iff]
  simp

private def missingCodeState : FullState :=
  FullState.ofMath ⟨accounts, ∅, ∅⟩ wfWithoutStorage (authenticEmptyCode accounts)

private theorem nonreserved : codeHash ≠ HashConsts.literals.emptyCodeHash := by decide

example : missingCodeState.σ.account? address = some account ∧
    account.codeHash = codeHash ∧
    missingCodeState.σ.code? HashConsts.literals codeHash = none := by
  constructor
  · rw [MathState.account?_eq_lookup]
    exact Std.ExtTreeMap.getElem?_insert_self
  · refine ⟨Account.codeHash_mk _ _ _, ?_⟩
    rw [MathState.code?_of_ne _ _ _ nonreserved]
    exact Std.ExtTreeMap.getElem?_empty

end STFSpec.Conformance.StateFull.CarrierChecks
