/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountDefault
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# SELFBALANCE

Library `EthVmInstructions`. Charge the selected tariff, read the
defaulted current-target account, and push its balance.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private def paidPushReference (ctx : FrameCtx) (f : Frame) (meter : GasMeter)
    (word : U256) : StepResult ctx :=
  match f.stack.push word with
  | .error error => .halt { f with gasMeter := meter } error
  | .ok stack => .continue { f with pc := f.pc + 1, stack, gasMeter := meter }

private def paidPush (ctx : FrameCtx) (f : Frame) (meter : GasMeter) (word : U256) :
    StepResult ctx :=
  if full : f.stack.size = 1024 then
    .halt { f with gasMeter := meter } .stackOverflow
  else
    match pushed : f.stack.push word with
    | .error error => False.elim (full ((Stack.push_eq_error_iff f.stack word error).mp pushed).1)
    | .ok stack => .continue { f with pc := f.pc + 1, stack, gasMeter := meter }

private theorem paidPush_eq (ctx : FrameCtx) (f : Frame) (meter : GasMeter) (word : U256) :
    paidPush ctx f meter word = paidPushReference ctx f meter word := by
  unfold paidPush paidPushReference
  by_cases full : f.stack.size = 1024
  · rw [dite_eq_left full, (Stack.push_eq_error_iff f.stack word .stackOverflow).mpr ⟨full, rfl⟩]
  · rw [dite_eq_right full]
    split
    · rename_i error failed
      exact False.elim (full ((Stack.push_eq_error_iff f.stack word error).mp failed).1)
    · rename_i stack pushed
      rw [pushed]

/-- Charge the SELFBALANCE tariff, then read the current target and push its balance.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:513–538`. -/
def selfBalance {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance with
  | .error error => pure (.halt f error)
  | .ok meter => do
    let account ← liftState (getAccount ctx.currentTarget)
    pure (paidPush ctx f meter account.balance)

private theorem outOfGas {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (denied : f.gasMeter.gasLeft < ctx.config.costs.opcodeSelfBalance) :
    ((selfBalance ctx f).run w).run = pure (.ok (.halt f .outOfGas, w)) := by
  rw [selfBalance, (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeSelfBalance
    .outOfGas).mpr ⟨denied, rfl⟩]
  rfl

private theorem paidAction {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter) :
    ((selfBalance ctx f).run w).run =
      (((do
        let account ← liftState (getAccount ctx.currentTarget)
        pure (paidPushReference ctx f meter account.balance) : VmM m (StepResult ctx)).run w).run) := by
  simp only [selfBalance, paid, paidPush_eq]

private theorem idPaidResult (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter) :
    ((selfBalance ctx f).run w).run =
      match ((getAccount ctx.currentTarget).run w.tx).run with
      | .error error => .error (.state error)
      | .ok (account, next) =>
        .ok (paidPushReference ctx f meter account.balance, { w with tx := next }) := by
  rw [paidAction ctx f w meter paid]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run]
  cases seen : ((getAccount ctx.currentTarget).run w.tx).run <;> rfl

private theorem paidOverflow (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter)
    (full : f.stack.size = 1024) (account : Account) (next : TxState Id)
    (read : ((getAccount ctx.currentTarget).run w.tx).run = .ok (account, next)) :
    ((selfBalance ctx f).run w).run =
      .ok (.halt { f with gasMeter := meter } .stackOverflow, { w with tx := next }) := by
  rw [idPaidResult ctx f w meter paid, read]
  simp [paidPushReference, (Stack.push_eq_error_iff f.stack account.balance .stackOverflow).mpr ⟨full, rfl⟩]

private theorem paidOverflowObservation (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (meter : GasMeter) (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter)
    (full : f.stack.size = 1024) (account : Account) (next : TxState Id)
    (read : ((getAccount ctx.currentTarget).run w.tx).run = .ok (account, next)) :
    (((selfBalance ctx f).run w).run =
      .ok (.halt { f with gasMeter := meter } .stackOverflow, { w with tx := next })) ∧
    ∀ a, a ∈ next.obs.accountReads ↔ a = ctx.currentTarget ∨ a ∈ w.tx.obs.accountReads := by
  exact ⟨paidOverflow ctx f w meter paid full account next read,
    fun a ↦ getAccount_mem w.tx ctx.currentTarget a account next read⟩

private theorem providerFailure (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter)
    (error : StateError)
    (read : ((getAccount ctx.currentTarget).run w.tx).run = .error error) :
    ((selfBalance ctx f).run w).run = .error (.state error) := by
  rw [idPaidResult ctx f w meter paid, read]

private theorem exactProviderFailure (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter)
    (error : WitnessError) (txMiss : w.tx.rev.accountWrites[ctx.currentTarget]? = none)
    (blockMiss : w.tx.block.accountWrites[ctx.currentTarget]? = none)
    (failed : w.tx.block.preState.getAccount? ctx.currentTarget = .error error) :
    ((selfBalance ctx f).run w).run = .error (.state (.witness error)) :=
  providerFailure ctx f w meter paid (.witness error)
    (getAccount_error w.tx ctx.currentTarget error txMiss blockMiss failed)

private theorem paidSuccess (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (meter : GasMeter)
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance = .ok meter)
    (account : Account) (next : TxState Id) (stack : Stack)
    (read : ((getAccount ctx.currentTarget).run w.tx).run = .ok (account, next))
    (pushed : f.stack.push account.balance = .ok stack) :
    ((selfBalance ctx f).run w).run =
      .ok (.continue { f with pc := f.pc + 1, stack, gasMeter := meter }, { w with tx := next }) ∧
    stack.toList = account.balance :: f.stack.toList := by
  refine ⟨?_, ((Stack.push_eq_ok_iff f.stack stack account.balance).mp pushed).2⟩
  rw [idPaidResult ctx f w meter paid, read]
  simp [paidPushReference, pushed]

private theorem readFrames (ctx : FrameCtx) (w : VmWorld Id) (account : Account) (next : TxState Id)
    (read : ((getAccount ctx.currentTarget).run w.tx).run = .ok (account, next)) :
    next.block = w.tx.block ∧ next.rev = w.tx.rev ∧
      next.obs.storageReads = w.tx.obs.storageReads ∧ next.obs.codeReads = w.tx.obs.codeReads ∧
      next.obs.createdAccounts = w.tx.obs.createdAccounts :=
  getAccount_frames w.tx ctx.currentTarget account next read

private theorem continuePotential (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((selfBalance ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSelfBalance = f.gasMeter.phi := by
  cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeSelfBalance with
  | error error =>
    simp only [selfBalance, paid] at ran
    change Except.ok (StepResult.halt f error, w) = _ at ran
    have impossible := (Prod.mk.inj (Except.ok.inj ran)).1
    cases impossible
  | ok meter =>
    rw [idPaidResult ctx f w meter paid] at ran
    cases observed : ((getAccount ctx.currentTarget).run w.tx).run with
    | error error =>
      simp only [observed] at ran
      contradiction
    | ok result =>
      rcases result with ⟨account, next⟩
      cases pushed : f.stack.push account.balance with
      | error error =>
        simp only [observed, paidPushReference, pushed] at ran
        have impossible := (Prod.mk.inj (Except.ok.inj ran)).1
        cases impossible
      | ok stack =>
        simp only [observed, paidPushReference, pushed] at ran
        have frame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
        rw [← frame]
        exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeSelfBalance meter paid

end STFSpec.Vm.Instructions
