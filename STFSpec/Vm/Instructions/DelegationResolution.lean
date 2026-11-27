/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountDefault
import STFSpec.State.Code
import STFSpec.Vm.Core.Context
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.DelegationDesignator

/-!
# Resolve a delegation destination

Library `EthVmInstructions`. Read the target's own account and code before
charging the access to its delegate. Spec guidance in
`STFSpec/informal/modules/EthVmInstructions.md` R-DEL-3.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private def afterCode (costs : GasCosts) (g : GasMeter) (warm : AddrSet) (a : Address)
    (code : ByteArray) : Except ExceptionalHalt (Address × Bool × GasMeter × AddrSet) :=
  match getDelegatedCodeAddress (Bytes.ofByteArray code) with
  | none => .ok (a, false, g, warm)
  | some delegate =>
    let isWarm := decide (delegate ∈ warm)
    let price := if isWarm then costs.warmAccess else costs.coldAccountAccess
    match chargeGas g price with
    | .error halt => .error halt
    | .ok paid => .ok (delegate, true, paid, if isWarm then warm else warm.insert delegate)

/-- Resolve one designator and warm its destination after payment.
EELS `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:84–109`. -/
def resolveDelegatedCodeAddress {m : Type → Type} [Monad m] (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a : Address) : VmM m (Except ExceptionalHalt (Address × Bool × GasMeter × AddrSet)) := do
  let account ← liftState (getAccount a)
  let code ← liftState (getCode account.codeHash)
  pure (afterCode costs g warm a code)

/-- The whole ordered action with the supplied base monad and the two State lifts. -/
theorem resolveDelegatedCodeAddress_run {m : Type → Type} [Monad m] (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a : Address) (w : VmWorld m) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run =
      (((do
        let account ← liftState (getAccount a)
        let code ← liftState (getCode account.codeHash)
        pure (match getDelegatedCodeAddress (Bytes.ofByteArray code) with
          | none => .ok (a, false, g, warm)
          | some delegate =>
            let isWarm := decide (delegate ∈ warm)
            let price := if isWarm then costs.warmAccess else costs.coldAccountAccess
            match chargeGas g price with
            | .error halt => .error halt
            | .ok paid => .ok (delegate, true, paid, if isWarm then warm else warm.insert delegate))) :
        VmM m (Except ExceptionalHalt (Address × Bool × GasMeter × AddrSet))).run w).run := rfl

private theorem bindLiftId {α β : Type} (action : StateM Id α) (next : α → VmM Id β)
    (w : VmWorld Id) :
    (((do
      let value ← liftState action
      next value) : VmM Id β).run w).run =
      match (action.run w.tx).run with
      | .error error => .error (.state error)
      | .ok (value, tx) => ((next value).run { w with tx := tx }).run := by
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run]
  cases (action.run w.tx).run <;> rfl

private theorem runId (costs : GasCosts) (g : GasMeter) (warm : AddrSet)
    (a : Address) (w : VmWorld Id) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run =
      match ((getAccount a).run w.tx).run with
      | .error error => .error (.state error)
      | .ok (account, accountTx) =>
        match ((getCode account.codeHash).run accountTx).run with
        | .error error => .error (.state error)
        | .ok (code, codeTx) => .ok (afterCode costs g warm a code, { w with tx := codeTx }) := by
  unfold resolveDelegatedCodeAddress
  rw [bindLiftId]
  cases ((getAccount a).run w.tx).run with
  | error error => rfl
  | ok observed =>
    rcases observed with ⟨account, accountTx⟩
    simp only [bindLiftId, StateT.run_pure, ExceptT.run_pure]
    cases ((getCode account.codeHash).run accountTx).run <;> rfl

/-- An account read error is the complete outer State fault. -/
theorem resolveDelegatedCodeAddress_run_account_error (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a : Address) (w : VmWorld Id) (error : StateError)
    (readAccount : ((getAccount a).run w.tx).run = .error error) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run = .error (.state error) := by
  rw [runId, readAccount]

/-- A reached code read error is the complete outer State fault. -/
theorem resolveDelegatedCodeAddress_run_code_error (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a : Address) (w : VmWorld Id) (account : Account) (accountTx : TxState Id)
    (error : StateError) (readAccount : ((getAccount a).run w.tx).run = .ok (account, accountTx))
    (readCode : ((getCode account.codeHash).run accountTx).run = .error error) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run = .error (.state error) := by
  rw [runId, readAccount]
  simp only [readCode]

/-- Ordinary code leaves the entry address, meter and warmth intact after both reads. -/
theorem resolveDelegatedCodeAddress_run_ordinary (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a : Address) (w : VmWorld Id) (account : Account) (accountTx codeTx : TxState Id)
    (code : ByteArray) (readAccount : ((getAccount a).run w.tx).run = .ok (account, accountTx))
    (readCode : ((getCode account.codeHash).run accountTx).run = .ok (code, codeTx))
    (ordinary : getDelegatedCodeAddress (Bytes.ofByteArray code) = none) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run = .ok (.ok (a, false, g, warm), { w with tx := codeTx }) := by
  rw [runId, readAccount]
  simp only [readCode, afterCode, ordinary]

/-- A denied price preserves the reached world and returns the inner exceptional halt. -/
theorem resolveDelegatedCodeAddress_run_outOfGas (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a delegate : Address) (w : VmWorld Id) (account : Account)
    (accountTx codeTx : TxState Id) (code : ByteArray)
    (readAccount : ((getAccount a).run w.tx).run = .ok (account, accountTx))
    (readCode : ((getCode account.codeHash).run accountTx).run = .ok (code, codeTx))
    (designator : getDelegatedCodeAddress (Bytes.ofByteArray code) = some delegate)
    (short : g.gasLeft < (if delegate ∈ warm then costs.warmAccess else costs.coldAccountAccess)) :
    ((resolveDelegatedCodeAddress costs g warm a).run w).run = .ok (.error .outOfGas, { w with tx := codeTx }) := by
  have denied := (chargeGas_eq_error_iff g _ .outOfGas).mpr ⟨short, rfl⟩
  rw [runId, readAccount]
  simp only [readCode, afterCode, designator]
  by_cases isWarm : delegate ∈ warm
  all_goals
    simp [isWarm] at denied
    simp [isWarm, denied]

/-- Successful resolution charges the selected price and records cold warmth after payment. -/
theorem resolveDelegatedCodeAddress_run_paid (costs : GasCosts) (g : GasMeter)
    (warm : AddrSet) (a delegate : Address) (w : VmWorld Id) (account : Account)
    (accountTx codeTx : TxState Id) (code : ByteArray)
    (readAccount : ((getAccount a).run w.tx).run = .ok (account, accountTx))
    (readCode : ((getCode account.codeHash).run accountTx).run = .ok (code, codeTx))
    (designator : getDelegatedCodeAddress (Bytes.ofByteArray code) = some delegate)
    (enough : (if delegate ∈ warm then costs.warmAccess else costs.coldAccountAccess) ≤ g.gasLeft) :
    let price := if delegate ∈ warm then costs.warmAccess else costs.coldAccountAccess
    let paid := { g with gasLeft := g.gasLeft - price }
    let warmed := if delegate ∈ warm then warm else warm.insert delegate
    ((resolveDelegatedCodeAddress costs g warm a).run w).run = .ok (.ok (delegate, true, paid, warmed), { w with tx := codeTx }) ∧
      paid.phi + price = g.phi := by
  dsimp only
  have paid := chargeGas_of_le g _ enough
  refine ⟨?_, chargeGas_phi g _ _ paid⟩
  rw [runId, readAccount]
  simp only [readCode, afterCode, designator]
  by_cases isWarm : delegate ∈ warm
  all_goals
    simp [isWarm] at paid
    simp [isWarm, paid]

end STFSpec.Vm.Instructions
