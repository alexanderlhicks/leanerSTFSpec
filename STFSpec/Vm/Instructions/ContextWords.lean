/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Instructions.Handler

/-!
# Bounded context-word handlers

Library `EthVmInstructions`. The handlers charge execution gas before pushing
one word from the supplied context. A successful push advances the PC by one.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def pushContextWordReference (price : Nat) (read : FrameCtx → U256) (ctx : FrameCtx)
    (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter price with
  | .error error => .halt f error
  | .ok paid =>
    match f.stack.push (read ctx) with
    | .error error => .halt { f with gasMeter := paid } error
    | .ok stack => .continue { f with gasMeter := paid, pc := f.pc + 1, stack }

private theorem pushImpossible (s : Stack) (word : U256) (error : ExceptionalHalt)
    (space : s.size ≠ 1024) (failed : s.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff s word error).mp failed).1

private def pushContextWordResult (price : Nat) (read : FrameCtx → U256) (ctx : FrameCtx)
    (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter price with
  | .error error => .halt f error
  | .ok paid =>
    if full : f.stack.size = 1024 then
      .halt { f with gasMeter := paid } .stackOverflow
    else
      match pushed : f.stack.push (read ctx) with
      | .error error => False.elim (pushImpossible f.stack (read ctx) error full pushed)
      | .ok stack => .continue { f with gasMeter := paid, pc := f.pc + 1, stack }

private theorem pushContextWordResult_eq_reference (price : Nat) (read : FrameCtx → U256) (ctx : FrameCtx)
    (f : Frame) : pushContextWordResult price read ctx f = pushContextWordReference price read ctx f := by
  unfold pushContextWordResult pushContextWordReference
  cases charged : chargeGas f.gasMeter price with
  | error _ => rfl
  | ok _ =>
    by_cases full : f.stack.size = 1024
    · have rejected := (Stack.push_eq_error_iff f.stack (read ctx) .stackOverflow).mpr ⟨full, rfl⟩
      simp only [dite_eq_left full, rejected]
    · simp only [dite_eq_right full]
      split
      · rename_i error rejected
        exact False.elim (pushImpossible f.stack (read ctx) error full rejected)
      · rename_i stack pushed
        simp only [pushed]

private def pushContextWord {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) : Handler m :=
  fun ctx f ↦ pure (pushContextWordResult (price ctx) read ctx f)

private def chargedFrame (f : Frame) (price : Nat) : Frame :=
  { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }

private theorem contextWord_run_oog {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < price ctx) :
    ((pushContextWord price read ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  change pure (Except.ok (pushContextWordResult (price ctx) read ctx f, w)) = _
  have denied := (chargeGas_eq_error_iff f.gasMeter (price ctx) .outOfGas).mpr ⟨short, rfl⟩
  rw [pushContextWordResult_eq_reference]
  simp only [pushContextWordReference, denied]

private theorem contextWord_run_overflow {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : price ctx ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((pushContextWord price read ctx f).run w).run =
      pure (Except.ok (.halt (chargedFrame f (price ctx)) .stackOverflow, w)) := by
  change pure (Except.ok (pushContextWordResult (price ctx) read ctx f, w)) = _
  have paid := chargeGas_of_le f.gasMeter (price ctx) enough
  have rejected := (Stack.push_eq_error_iff f.stack (read ctx) .stackOverflow).mpr ⟨full, rfl⟩
  rw [pushContextWordResult_eq_reference]
  simp only [pushContextWordReference, paid, rejected]
  rfl

private theorem contextWord_run_success {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : price ctx ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    ∃ stack : Stack, f.stack.push (read ctx) = .ok stack ∧
      stack.toList = read ctx :: f.stack.toList ∧
      ((pushContextWord price read ctx f).run w).run =
        pure (Except.ok (.continue { chargedFrame f (price ctx) with pc := f.pc + 1, stack }, w)) := by
  have paid := chargeGas_of_le f.gasMeter (price ctx) enough
  cases pushed : f.stack.push (read ctx) with
  | error error =>
    exact False.elim (pushImpossible f.stack (read ctx) error (Nat.ne_of_lt space) pushed)
  | ok stack =>
    refine ⟨stack, rfl, ((Stack.push_eq_ok_iff f.stack stack _).mp pushed).2, ?_⟩
    change pure (Except.ok (pushContextWordResult (price ctx) read ctx f, w)) = _
    rw [pushContextWordResult_eq_reference]
    simp only [pushContextWordReference, paid, pushed]
    rfl

private theorem contextWord_continue_phi (price : FrameCtx → Nat) (read : FrameCtx → U256)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((pushContextWord price read ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + price ctx = f.gasMeter.phi := by
  change Except.ok (pushContextWordResult (price ctx) read ctx f, w) = .ok (.continue f', w') at observed
  have outcome := (Prod.mk.inj (Except.ok.inj observed)).1
  rw [pushContextWordResult_eq_reference] at outcome
  cases charged : chargeGas f.gasMeter (price ctx) with
  | error _ =>
    simp only [pushContextWordReference, charged] at outcome
    contradiction
  | ok meter =>
    cases pushed : f.stack.push (read ctx) with
    | error _ =>
      simp only [pushContextWordReference, charged, pushed] at outcome
      contradiction
    | ok _ =>
      simp only [pushContextWordReference, charged, pushed, StepResult.continue.injEq] at outcome
      subst f'
      exact chargeGas_phi f.gasMeter (price ctx) meter charged

private theorem contextWord_continue_progress (price : FrameCtx → Nat) (read : FrameCtx → U256)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((pushContextWord price read ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ price ctx) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have exactPrice := contextWord_continue_phi price read ctx f f' w w' observed
  omega

private theorem addressWord (x : Address) : x.toU256.toNat = x.toNat :=
  Address.toNat_toU256 x

private theorem bytes32Word (x : Bytes32) : (U256.ofBeBytes32 x).toNat = x.toNat :=
  U256.toNat_ofBeBytes32 x

private theorem u64Word (x : U64) : (U256.ofNat x.toNat).toNat = x.toNat :=
  U256.toNat_ofNat_of_lt (Nat.lt_trans (U64.toNat_lt x) (by decide))

/-- Charge and push the current target address.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:35–55`. -/
def address {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeAddress) (·.currentTarget.toU256)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem address_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeAddress) :
    ((address ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeAddress) (·.currentTarget.toU256) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem address_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeAddress ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((address ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAddress } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeAddress) (·.currentTarget.toU256) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem address_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeAddress ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.currentTarget.toU256
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((address ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAddress } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeAddress) (·.currentTarget.toU256) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem address_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((address ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAddress = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeAddress) (·.currentTarget.toU256) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem address_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((address ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeAddress) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeAddress) (·.currentTarget.toU256) ctx f f' w w' observed positive

/-- Charge and push the transaction origin.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:89–110`. -/
def origin {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem origin_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeOrigin) :
    ((origin ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem origin_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeOrigin ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((origin ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeOrigin } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem origin_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeOrigin ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.txEnv.origin.toU256
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((origin ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeOrigin } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem origin_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((origin ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeOrigin = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem origin_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((origin ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeOrigin) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256) ctx f f' w w' observed positive

/-- Charge and push the caller address.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:113–133`. -/
def caller {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeCaller) (·.caller.toU256)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem caller_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeCaller) :
    ((caller ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeCaller) (·.caller.toU256) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem caller_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCaller ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((caller ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCaller } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeCaller) (·.caller.toU256) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem caller_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCaller ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.caller.toU256
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((caller ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCaller } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeCaller) (·.caller.toU256) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem caller_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((caller ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeCaller = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeCaller) (·.caller.toU256) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem caller_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((caller ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeCaller) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeCaller) (·.caller.toU256) ctx f f' w w' observed positive

/-- Charge and push the supplied call value.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:136–156`. -/
def callvalue {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeCallValue) (·.value)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem callvalue_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeCallValue) :
    ((callvalue ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeCallValue) (·.value) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem callvalue_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCallValue ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((callvalue ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCallValue } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeCallValue) (·.value) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem callvalue_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCallValue ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.value
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((callvalue ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCallValue } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeCallValue) (·.value) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem callvalue_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((callvalue ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeCallValue = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeCallValue) (·.value) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem callvalue_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((callvalue ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeCallValue) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeCallValue) (·.value) ctx f f' w w' observed positive

/-- Charge and push the block beneficiary address.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:71–102`. -/
def coinbase {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem coinbase_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeCoinbase) :
    ((coinbase ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem coinbase_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCoinbase ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((coinbase ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCoinbase } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem coinbase_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeCoinbase ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.blockEnv.coinbase.toU256
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((coinbase ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeCoinbase } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem coinbase_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((coinbase ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeCoinbase = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem coinbase_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((coinbase ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeCoinbase) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256) ctx f f' w w' observed positive

/-- Charge and push the block timestamp.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:105–136`. -/
def timestamp {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeTimestamp) (·.blockEnv.time)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem timestamp_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeTimestamp) :
    ((timestamp ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeTimestamp) (·.blockEnv.time) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem timestamp_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeTimestamp ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((timestamp ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeTimestamp } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeTimestamp) (·.blockEnv.time) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem timestamp_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeTimestamp ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := ctx.blockEnv.time
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((timestamp ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeTimestamp } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeTimestamp) (·.blockEnv.time) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem timestamp_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((timestamp ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeTimestamp = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeTimestamp) (·.blockEnv.time) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem timestamp_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((timestamp ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeTimestamp) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeTimestamp) (·.blockEnv.time) ctx f f' w w' observed positive

/-- Charge and push the full big-endian randomness word.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:172–202`. -/
def prevRandao {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem prevRandao_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodePrevRandao) :
    ((prevRandao ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem prevRandao_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodePrevRandao ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((prevRandao ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodePrevRandao } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem prevRandao_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodePrevRandao ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := U256.ofBeBytes32 ctx.blockEnv.prevRandao
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((prevRandao ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodePrevRandao } }, w)) :=
  contextWord_run_success (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem prevRandao_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((prevRandao ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodePrevRandao = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem prevRandao_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((prevRandao ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodePrevRandao) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao) ctx f f' w w' observed positive

/-- Charge and push the block chain identifier.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:238–265`. -/
def chainId {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem chainId_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeChainId) :
    ((chainId ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem chainId_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeChainId ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((chainId ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeChainId } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem chainId_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeChainId ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := U256.ofNat ctx.blockEnv.chainId.toNat
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((chainId ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeChainId } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem chainId_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((chainId ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeChainId = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem chainId_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((chainId ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeChainId) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat) ctx f f' w w' observed positive

/-- Charge and push the block slot number.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:268–298`. -/
def slotNumber {m : Type → Type} [Monad m] : Handler m :=
  pushContextWord (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat)

/-- Gas denial keeps the entry frame and supplied world. -/
theorem slotNumber_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeSlotNum) :
    ((slotNumber ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  contextWord_run_oog (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat) ctx f w short

/-- A full stack halts after payment with the entry stack and PC. -/
theorem slotNumber_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSlotNum ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((slotNumber ctx f).run w).run = pure (Except.ok (.halt { f with
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSlotNum } }
      .stackOverflow, w)) :=
  contextWord_run_overflow (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat) ctx f w enough full

/-- The actual push determines the continuing stack and frame. -/
theorem slotNumber_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSlotNum ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    let word := U256.ofNat ctx.blockEnv.slotNumber.toNat
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      ((slotNumber ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSlotNum } }, w)) :=
  contextWord_run_success (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat) ctx f w enough space

/-- Continuation spends the exact selected execution price in Id. -/
theorem slotNumber_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((slotNumber ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSlotNum = f.gasMeter.phi :=
  contextWord_continue_phi (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat) ctx f f' w w' observed

/-- Positive execution price gives strict local progress on continuation. -/
theorem slotNumber_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((slotNumber ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeSlotNum) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  contextWord_continue_progress (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat) ctx f f' w w' observed positive

end STFSpec.Vm.Instructions
