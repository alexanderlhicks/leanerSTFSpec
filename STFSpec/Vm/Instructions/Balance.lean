/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.AccountDefault
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# BALANCE

Library `EthVmInstructions`. Observe entry warmth, charge, then read the
defaulted account. See `STFSpec/informal/modules/EthVmInstructions.md` §§2/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private theorem room_after_pop (stack tail : Stack) (word : U256)
    (popped : stack.pop = .ok (word, tail)) : tail.size < 1024 := by
  have bound := stack.size_le
  rw [Stack.size_eq_length_toList, (Stack.pop_eq_ok_iff stack tail word).mp popped,
    List.length_cons] at bound
  rw [Stack.size_eq_length_toList]
  omega

private def popFrameReference (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  match f.stack.pop with
  | .error error => .error (f, error)
  | .ok (word, tail) => .ok (word, { f with stack := tail })

private theorem pop_error_on_nonempty (f : Frame) (error : ExceptionalHalt)
    (nonempty : 0 < f.stack.size) (failed : f.stack.pop = .error error) : False := by
  have empty := ((Stack.pop_eq_error_iff f.stack error).mp failed).1
  simp [Stack.size_eq_length_toList, empty] at nonempty

private def popFrame (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  if nonempty : 0 < f.stack.size then
    match popped : f.stack.pop with
    | .error error => False.elim (pop_error_on_nonempty f error nonempty popped)
    | .ok (word, tail) => .ok (word, { f with stack := tail })
  else
    popFrameReference f

private theorem popFrame_eq (f : Frame) : popFrame f = popFrameReference f := by
  unfold popFrame
  split
  · rename_i nonempty
    unfold popFrameReference
    split
    · rename_i error failed
      exact False.elim (pop_error_on_nonempty f error nonempty failed)
    · rename_i word tail popped
      rw [popped]
  · rfl

private theorem poppedFrame_room (f residual : Frame) (word : U256)
    (popped : popFrame f = .ok (word, residual)) : residual.stack.size < 1024 := by
  rw [popFrame_eq] at popped
  cases observed : f.stack.pop with
  | error error => simp [popFrameReference, observed] at popped
  | ok result =>
    rcases result with ⟨value, tail⟩
    have same : (value, { f with stack := tail }) = (word, residual) := by
      apply Except.ok.inj
      simpa only [popFrameReference, observed] using popped
    rw [← (Prod.mk.inj same).2]
    exact room_after_pop f.stack tail value observed

private theorem push_error_with_room (tail : Stack) (word : U256) (room : tail.size < 1024)
    (error : ExceptionalHalt) (failed : tail.push word = .error error) : False :=
  (Nat.ne_of_lt room) ((Stack.push_eq_error_iff tail word error).mp failed).1

private def pushBalance (tail : Stack) (word : U256) (room : tail.size < 1024) : Stack :=
  match pushed : tail.push word with
  | .ok stack => stack
  | .error error => False.elim (push_error_with_room tail word room error pushed)

private theorem pushBalance_actual (tail : Stack) (word : U256) (room : tail.size < 1024) :
    tail.push word = .ok (pushBalance tail word room) := by
  unfold pushBalance
  split
  · rename_i stack pushed
    exact pushed
  · rename_i error failed
    exact False.elim (push_error_with_room tail word room error failed)

private def paidResult (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (addresses : AddrSet) (meter : GasMeter) (value : U256) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, returnData, _, slots⟩ =>
    .continue ⟨pc + 1, pushBalance stack value room, memory, meter, logs, deleted,
      returnData, addresses, slots⟩

private theorem paidResult_eq (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (addresses : AddrSet) (meter : GasMeter) (value : U256) :
    paidResult ctx f room addresses meter value =
      .continue { f with
        pc := f.pc + 1
        stack := pushBalance f.stack value room
        gasMeter := meter
        accessedAddresses := addresses } := by
  cases f
  rfl

private def warmAndPrice (cfg : VmConfig) (warm : AddrSet) (address : Address) : AddrSet × Nat :=
  if address ∈ warm then (warm, cfg.costs.warmAccess)
  else (warm.insert address, cfg.costs.coldAccountAccess)

private def balanceAfterPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (room : f.stack.size < 1024) : VmM m (StepResult ctx) :=
  let address := Address.ofU256Masked word
  let (addresses, price) := warmAndPrice ctx.config f.accessedAddresses address
  match chargeGas f.gasMeter price with
  | .error error => pure (.halt { f with accessedAddresses := addresses } error)
  | .ok meter => do
    let account ← liftState (getAccount address)
    pure (paidResult ctx f room addresses meter account.balance)

/-- Pop and mask the address, charge for its original warmth, then read its balance.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:58–86` at the pin. -/
def balance {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (word, residual) => balanceAfterPop ctx residual word (poppedFrame_room f residual word popped)

private theorem balance_of_error {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (error : ExceptionalHalt) (missing : f.stack.pop = .error error) :
    (balance ctx f : VmM m (StepResult ctx)) = pure (.halt f error) := by
  have popped : popFrame f = .error (f, error) := by simp [popFrame_eq, popFrameReference, missing]
  unfold balance
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i word residual observed
    rw [popped] at observed
    contradiction

private theorem balance_of_pop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail)) :
    (balance ctx f : VmM m (StepResult ctx)) =
      balanceAfterPop ctx { f with stack := tail } word (room_after_pop f.stack tail word popped) := by
  have framePop : popFrame f = .ok (word, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold balance
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

/-- An absent operand halts before looking at warmth, charging or running State. -/
theorem balance_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (missing : f.stack.pop = .error .stackUnderflow) :
    ((balance ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  rw [balance_of_error _ _ _ missing]
  rfl

/-- A denied warm charge keeps the residual stack and original warm set and world. -/
theorem balance_run_warm_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (warm : Address.ofU256Masked word ∈ f.accessedAddresses)
    (short : f.gasMeter.gasLeft < ctx.config.costs.warmAccess) :
    ((balance ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.warmAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [balance_of_pop _ _ _ _ popped]
  simp only [balanceAfterPop, warmAndPrice, warm, ite_true, denied]
  rfl

/-- A denied cold charge retains the warmed address and does not run State. -/
theorem balance_run_cold_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (cold : Address.ofU256Masked word ∉ f.accessedAddresses)
    (short : f.gasMeter.gasLeft < ctx.config.costs.coldAccountAccess) :
    ((balance ctx f).run w).run = pure (.ok (.halt { f with
      stack := tail
      accessedAddresses := f.accessedAddresses.insert (Address.ofU256Masked word) } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.coldAccountAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [balance_of_pop _ _ _ _ popped]
  simp only [balanceAfterPop, warmAndPrice, cold, ite_false, denied]
  rfl

/-- Payment runs the actual lifted read and the admitted push under the supplied Monad. -/
theorem balance_run_paid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft) :
    let address := Address.ofU256Masked word
    let addresses := if address ∈ f.accessedAddresses then f.accessedAddresses
      else f.accessedAddresses.insert address
    let price := if address ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess
    ∃ push : U256 → Stack, (∀ value, tail.push value = .ok (push value)) ∧
      ((balance ctx f).run w).run =
        (((do
          let account ← liftState (getAccount address)
          pure (.continue { f with
            pc := f.pc + 1
            stack := push account.balance
            accessedAddresses := addresses
            gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } })) :
          VmM m (StepResult ctx)).run w).run := by
  intro address addresses price
  let room := room_after_pop f.stack tail word popped
  refine ⟨fun value ↦ pushBalance tail value room, fun value ↦ pushBalance_actual tail value room, ?_⟩
  have selected : warmAndPrice ctx.config f.accessedAddresses address = (addresses, price) := by
    by_cases warm : address ∈ f.accessedAddresses <;>
      simp [warmAndPrice, addresses, price, warm]
  have paid := chargeGas_of_le f.gasMeter price enough
  rw [balance_of_pop _ _ _ _ popped]
  simp only [balanceAfterPop]
  change (((match chargeGas f.gasMeter (warmAndPrice ctx.config f.accessedAddresses address).2 with
    | .error error => pure (.halt { f with
      stack := tail
      accessedAddresses := (warmAndPrice ctx.config f.accessedAddresses address).1 } error)
    | .ok meter => do
      let account ← liftState (getAccount address)
      pure (paidResult ctx { f with stack := tail } room
        (warmAndPrice ctx.config f.accessedAddresses address).1 meter account.balance)) :
        VmM m (StepResult ctx)).run w).run = _
  rw [selected]
  simp only [paid, paidResult_eq]

/-- A paid Id State fault is the complete original error wrapped by VmFault.state. -/
theorem balance_run_state_fault (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (error : StateError)
    (failed : ((getAccount (Address.ofU256Masked word)).run w.tx).run = .error error) :
    ((balance ctx f).run w).run = .error (.state error) := by
  obtain ⟨_, _, ran⟩ := balance_run_paid ctx f w word tail popped enough
  rw [ran]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run, failed]
  rfl

/-- Provider failure after both overlay misses remains a nested nominal witness error. -/
theorem balance_run_provider_fault (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (error : WitnessError)
    (txMiss : w.tx.rev.accountWrites[Address.ofU256Masked word]? = none)
    (blockMiss : w.tx.block.accountWrites[Address.ofU256Masked word]? = none)
    (provider : w.tx.block.preState.getAccount? (Address.ofU256Masked word) = .error error) :
    ((balance ctx f).run w).run = .error (.state (.witness error)) :=
  balance_run_state_fault ctx f w word tail popped enough (.witness error)
    (getAccount_error w.tx _ error txMiss blockMiss provider)

/-- A paid Id read returns its actual transaction and pushes the exact observed balance. -/
theorem balance_run_success (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (account : Account) (next : TxState Id)
    (read : ((getAccount (Address.ofU256Masked word)).run w.tx).run = .ok (account, next)) :
    let address := Address.ofU256Masked word
    let addresses := if address ∈ f.accessedAddresses then f.accessedAddresses
      else f.accessedAddresses.insert address
    let price := if address ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess
    let meter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price }
    ∃ stack, tail.push account.balance = .ok stack ∧ stack.toList = account.balance :: tail.toList ∧
      ((balance ctx f).run w).run = .ok (.continue { f with
        pc := f.pc + 1
        stack := stack
        accessedAddresses := addresses
        gasMeter := meter }, { w with tx := next }) ∧
      meter.phi + price = f.gasMeter.phi := by
  intro address addresses price meter
  obtain ⟨push, pushed, ran⟩ := balance_run_paid ctx f w word tail popped enough
  have app := pushed account.balance
  refine ⟨push account.balance, app, ((Stack.push_eq_ok_iff tail _ _).mp app).2, ?_,
    chargeGas_phi _ _ _ (chargeGas_of_le f.gasMeter price enough)⟩
  rw [ran]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run, read]
  rfl

private theorem paid_continuation_lookup (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (ran : ((balance ctx f).run w).run = .ok (.continue f', w')) :
    ∃ account next, ((getAccount (Address.ofU256Masked word)).run w.tx).run = .ok (account, next) ∧
      w' = { w with tx := next } ∧ f'.stack.toList = account.balance :: tail.toList := by
  cases read : ((getAccount (Address.ofU256Masked word)).run w.tx).run with
  | error error =>
    rw [balance_run_state_fault ctx f w word tail popped enough error read] at ran
    contradiction
  | ok result =>
    rcases result with ⟨account, next⟩
    obtain ⟨stack, _, model, whole, _⟩ :=
      balance_run_success ctx f w word tail popped enough account next read
    rw [whole] at ran
    obtain ⟨continued, world⟩ := Prod.mk.inj (Except.ok.inj ran)
    have nextFrame := StepResult.continue.inj continued
    refine ⟨account, next, rfl, world.symm, ?_⟩
    rw [← nextFrame]
    exact model

/-- The paid continuation retains State fields and adds precisely the masked address read. -/
theorem balance_run_observations (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (ran : ((balance ctx f).run w).run = .ok (.continue f', w')) :
    w'.tx.block = w.tx.block ∧ w'.tx.rev = w.tx.rev ∧
      w'.tx.obs.storageReads = w.tx.obs.storageReads ∧
      w'.tx.obs.codeReads = w.tx.obs.codeReads ∧
      w'.tx.obs.createdAccounts = w.tx.obs.createdAccounts ∧
      ∀ a : Address, a ∈ w'.tx.obs.accountReads ↔
        a = Address.ofU256Masked word ∨ a ∈ w.tx.obs.accountReads := by
  obtain ⟨account, next, read, world, _⟩ :=
    paid_continuation_lookup ctx f f' w w' word tail popped enough ran
  obtain ⟨block, rev, storage, code, created⟩ := getAccount_frames w.tx _ account next read
  rw [world]
  exact ⟨block, rev, storage, code, created, fun a ↦ getAccount_mem w.tx _ a account next read⟩

/-- On the existing State lookup domain, the stack reflects the defaulted transaction-view balance. -/
theorem balance_run_model (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (ran : ((balance ctx f).run w).run = .ok (.continue f', w'))
    (σ₀ : MathState) (hwf : MathState.WF σ₀)
    (lookups : ModelsLookups w.tx.block.consts w.tx.block.preState σ₀) :
    f'.stack.toList = (((w.tx.view σ₀).account? (Address.ofU256Masked word)).getD
      (emptyAccount w.tx.block.consts)).balance :: tail.toList := by
  obtain ⟨account, next, read, _, top⟩ :=
    paid_continuation_lookup ctx f f' w w' word tail popped enough ran
  rw [top, getAccount_model w.tx σ₀ hwf lookups _ account next read]

private def accountCodeHashWord (consts : HashConsts) (account : Account) : U256 :=
  if account = emptyAccount consts then U256.zero
  else U256.ofBeBytes32 account.codeHash.toBytes32

private theorem empty_code_hash_word (consts : HashConsts) :
    accountCodeHashWord consts (emptyAccount consts) = U256.zero := by
  simp [accountCodeHashWord]

private theorem nonempty_code_hash_bytes (consts : HashConsts) (account : Account)
    (nonempty : account ≠ emptyAccount consts) :
    (accountCodeHashWord consts account).toBeBytes32 = account.codeHash.toBytes32 := by
  simp [accountCodeHashWord, nonempty, U256.toBeBytes32_ofBeBytes32]

private def extcodehashAfterPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (room : f.stack.size < 1024) : VmM m (StepResult ctx) :=
  let address := Address.ofU256Masked word
  let (addresses, price) := warmAndPrice ctx.config f.accessedAddresses address
  match chargeGas f.gasMeter price with
  | .error error => pure (.halt { f with accessedAddresses := addresses } error)
  | .ok meter => fun w ↦
    let consts := w.tx.block.consts
    (do
      let account ← liftState (getAccount address)
      pure (paidResult ctx f room addresses meter (accountCodeHashWord consts account))
      : VmM m (StepResult ctx)).run w

/-- Charge for the masked address, read the account, and push its code hash
as a word. An account equal to the supplied empty account yields zero.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:476–510`. -/
def extcodehash {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (word, residual) => extcodehashAfterPop ctx residual word (poppedFrame_room f residual word popped)

private theorem extcodehash_of_pop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail)) :
    (extcodehash ctx f : VmM m (StepResult ctx)) =
      extcodehashAfterPop ctx { f with stack := tail } word (room_after_pop f.stack tail word popped) := by
  have framePop : popFrame f = .ok (word, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold extcodehash
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private theorem extcodehash_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (missing : f.stack.pop = .error .stackUnderflow) :
    ((extcodehash ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  have popped : popFrame f = .error (f, .stackUnderflow) := by
    simp [popFrame_eq, popFrameReference, missing]
  unfold extcodehash
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i word residual observed
    rw [popped] at observed
    contradiction

private theorem extcodehash_run_warm_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (warm : Address.ofU256Masked word ∈ f.accessedAddresses)
    (short : f.gasMeter.gasLeft < ctx.config.costs.warmAccess) :
    ((extcodehash ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.warmAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [extcodehash_of_pop _ _ _ _ popped]
  simp only [extcodehashAfterPop, warmAndPrice, warm, ite_true, denied]
  rfl

private theorem extcodehash_run_cold_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (cold : Address.ofU256Masked word ∉ f.accessedAddresses)
    (short : f.gasMeter.gasLeft < ctx.config.costs.coldAccountAccess) :
    ((extcodehash ctx f).run w).run = pure (.ok (.halt { f with
      stack := tail
      accessedAddresses := f.accessedAddresses.insert (Address.ofU256Masked word) } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.coldAccountAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [extcodehash_of_pop _ _ _ _ popped]
  simp only [extcodehashAfterPop, warmAndPrice, cold, ite_false, denied]
  rfl

private theorem extcodehash_run_paid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft) :
    let address := Address.ofU256Masked word
    let addresses := if address ∈ f.accessedAddresses then f.accessedAddresses
      else f.accessedAddresses.insert address
    let price := if address ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess
    ∃ push : U256 → Stack, (∀ value, tail.push value = .ok (push value)) ∧
      ((extcodehash ctx f).run w).run =
        (((do
          let account ← liftState (getAccount address)
          pure (.continue { f with
            pc := f.pc + 1
            stack := push (accountCodeHashWord w.tx.block.consts account)
            accessedAddresses := addresses
            gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } })) :
          VmM m (StepResult ctx)).run w).run := by
  intro address addresses price
  let room := room_after_pop f.stack tail word popped
  refine ⟨fun value ↦ pushBalance tail value room, fun value ↦ pushBalance_actual tail value room, ?_⟩
  have selected : warmAndPrice ctx.config f.accessedAddresses address = (addresses, price) := by
    by_cases warm : address ∈ f.accessedAddresses <;>
      simp [warmAndPrice, addresses, price, warm]
  have paid := chargeGas_of_le f.gasMeter price enough
  rw [extcodehash_of_pop _ _ _ _ popped]
  simp only [extcodehashAfterPop]
  change (((match chargeGas f.gasMeter (warmAndPrice ctx.config f.accessedAddresses address).2 with
    | .error error => pure (.halt { f with
      stack := tail
      accessedAddresses := (warmAndPrice ctx.config f.accessedAddresses address).1 } error)
    | .ok meter => fun source ↦
      (do
        let account ← liftState (getAccount address)
        pure (paidResult ctx { f with stack := tail } room
          (warmAndPrice ctx.config f.accessedAddresses address).1 meter
          (accountCodeHashWord source.tx.block.consts account)) : VmM m (StepResult ctx)).run source
        ) : VmM m (StepResult ctx)).run w).run = _
  rw [selected]
  simp only [paid, paidResult_eq, StateT.run]

private theorem extcodehash_run_state_fault (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (error : StateError)
    (failed : ((getAccount (Address.ofU256Masked word)).run w.tx).run = .error error) :
    ((extcodehash ctx f).run w).run = .error (.state error) := by
  obtain ⟨_, _, ran⟩ := extcodehash_run_paid ctx f w word tail popped enough
  rw [ran]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run, failed]
  rfl

private theorem extcodehash_run_success (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (account : Account) (next : TxState Id)
    (read : ((getAccount (Address.ofU256Masked word)).run w.tx).run = .ok (account, next)) :
    let address := Address.ofU256Masked word
    let addresses := if address ∈ f.accessedAddresses then f.accessedAddresses
      else f.accessedAddresses.insert address
    let price := if address ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess
    let meter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price }
    let value := accountCodeHashWord w.tx.block.consts account
    ∃ stack, tail.push value = .ok stack ∧ stack.toList = value :: tail.toList ∧
      ((extcodehash ctx f).run w).run = .ok (.continue { f with
        pc := f.pc + 1
        stack := stack
        accessedAddresses := addresses
        gasMeter := meter }, { w with tx := next }) ∧
      meter.phi + price = f.gasMeter.phi := by
  intro address addresses price meter value
  obtain ⟨push, pushed, ran⟩ := extcodehash_run_paid ctx f w word tail popped enough
  have pushedValue := pushed value
  refine ⟨push value, pushedValue, ((Stack.push_eq_ok_iff tail _ _).mp pushedValue).2, ?_,
    chargeGas_phi _ _ _ (chargeGas_of_le f.gasMeter price enough)⟩
  rw [ran]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run, read]
  rfl

private theorem extcodehash_run_observations (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (enough : (if Address.ofU256Masked word ∈ f.accessedAddresses then ctx.config.costs.warmAccess
      else ctx.config.costs.coldAccountAccess) ≤ f.gasMeter.gasLeft)
    (ran : ((extcodehash ctx f).run w).run = .ok (.continue f', w')) :
    w'.tx.block = w.tx.block ∧ w'.tx.rev = w.tx.rev ∧
      w'.tx.obs.storageReads = w.tx.obs.storageReads ∧
      w'.tx.obs.codeReads = w.tx.obs.codeReads ∧
      w'.tx.obs.createdAccounts = w.tx.obs.createdAccounts ∧
      ∀ a : Address, a ∈ w'.tx.obs.accountReads ↔
        a = Address.ofU256Masked word ∨ a ∈ w.tx.obs.accountReads := by
  cases read : ((getAccount (Address.ofU256Masked word)).run w.tx).run with
  | error error =>
    rw [extcodehash_run_state_fault ctx f w word tail popped enough error read] at ran
    contradiction
  | ok result =>
    rcases result with ⟨account, next⟩
    obtain ⟨_, _, _, action, _⟩ := extcodehash_run_success ctx f w word tail popped enough account next read
    rw [action] at ran
    have world := (Prod.mk.inj (Except.ok.inj ran)).2
    rw [← world]
    obtain ⟨block, rev, storage, code, created⟩ := getAccount_frames w.tx _ account next read
    exact ⟨block, rev, storage, code, created, fun a ↦ getAccount_mem w.tx _ a account next read⟩

end STFSpec.Vm.Instructions
