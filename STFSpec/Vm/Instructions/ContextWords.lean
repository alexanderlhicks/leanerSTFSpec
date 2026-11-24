/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Instructions.Handler

/-!
# Fixed frame and block context words

Library `EthVmInstructions`. Each handler charges for and pushes one word
from the immutable frame context. See `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/7.
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

private theorem push_error_contradicts_space (s : Stack) (word : U256) (error : ExceptionalHalt)
    (space : s.size ≠ 1024) (failed : s.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff s word error).mp failed).1

private def pushContextWord (price : Nat) (read : FrameCtx → U256) (ctx : FrameCtx)
    (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter price with
  | .error error => .halt f error
  | .ok paid =>
    if full : f.stack.size = 1024 then
      .halt { f with gasMeter := paid } .stackOverflow
    else
      match pushed : f.stack.push (read ctx) with
      | .error error => False.elim (push_error_contradicts_space f.stack (read ctx) error full pushed)
      | .ok stack => .continue { f with gasMeter := paid, pc := f.pc + 1, stack }

private theorem pushContextWord_eq_reference (price : Nat) (read : FrameCtx → U256) (ctx : FrameCtx)
    (f : Frame) : pushContextWord price read ctx f = pushContextWordReference price read ctx f := by
  unfold pushContextWord pushContextWordReference
  cases charged : chargeGas f.gasMeter price with
  | error _ => rfl
  | ok _ =>
    by_cases full : f.stack.size = 1024
    · have rejected := (Stack.push_eq_error_iff f.stack (read ctx) .stackOverflow).mpr ⟨full, rfl⟩
      simp only [dite_eq_left full, rejected]
    · simp only [dite_eq_right full]
      split
      · rename_i error rejected
        exact False.elim (push_error_contradicts_space f.stack (read ctx) error full rejected)
      · rename_i stack pushed
        simp only [pushed]

private def runContextWord {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) : Handler m :=
  fun ctx f ↦ pure (pushContextWord (price ctx) read ctx f)

/-- Charge and push the word embedding of the current execution target.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:35–55`. -/
def address {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeAddress) (·.currentTarget.toU256)

/-- Charge and push the word embedding of the original transaction sender.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:89–110`. -/
def origin {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeOrigin) (·.txEnv.origin.toU256)

/-- Charge and push the word embedding of the frame caller.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:113–133`. -/
def caller {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeCaller) (·.caller.toU256)

/-- Charge and push the value held by the current frame context.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:136–156`. -/
def callvalue {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeCallValue) (·.value)

private def chargedFrame (f : Frame) (price : Nat) : Frame :=
  { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }

private theorem runContextWord_denied {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < price ctx) :
    ((runContextWord price read ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  change pure (Except.ok (pushContextWord (price ctx) read ctx f, w)) = _
  have denied := (chargeGas_eq_error_iff f.gasMeter (price ctx) .outOfGas).mpr ⟨short, rfl⟩
  rw [pushContextWord_eq_reference]
  simp only [pushContextWordReference, denied]

private theorem runContextWord_full {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : price ctx ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((runContextWord price read ctx f).run w).run =
      pure (Except.ok (.halt (chargedFrame f (price ctx)) .stackOverflow, w)) := by
  change pure (Except.ok (pushContextWord (price ctx) read ctx f, w)) = _
  have paid := chargeGas_of_le f.gasMeter (price ctx) enough
  have rejected := (Stack.push_eq_error_iff f.stack (read ctx) .stackOverflow).mpr ⟨full, rfl⟩
  rw [pushContextWord_eq_reference]
  simp only [pushContextWordReference, paid, rejected]
  rfl

private theorem runContextWord_success {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (read : FrameCtx → U256) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : price ctx ≤ f.gasMeter.gasLeft) (space : f.stack.size < 1024) :
    ∃ stack : Stack, f.stack.push (read ctx) = .ok stack ∧
      stack.toList = read ctx :: f.stack.toList ∧
      ((runContextWord price read ctx f).run w).run =
        pure (Except.ok (.continue { chargedFrame f (price ctx) with pc := f.pc + 1, stack }, w)) := by
  have paid := chargeGas_of_le f.gasMeter (price ctx) enough
  cases pushed : f.stack.push (read ctx) with
  | error error =>
    exact False.elim (push_error_contradicts_space f.stack (read ctx) error (Nat.ne_of_lt space) pushed)
  | ok stack =>
    refine ⟨stack, rfl, ((Stack.push_eq_ok_iff f.stack stack _).mp pushed).2, ?_⟩
    change pure (Except.ok (pushContextWord (price ctx) read ctx f, w)) = _
    rw [pushContextWord_eq_reference]
    simp only [pushContextWordReference, paid, pushed]
    rfl

private theorem runContextWord_continue_phi (price : FrameCtx → Nat) (read : FrameCtx → U256)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((runContextWord price read ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + price ctx = f.gasMeter.phi := by
  change Except.ok (pushContextWord (price ctx) read ctx f, w) = .ok (.continue f', w') at observed
  have outcome := (Prod.mk.inj (Except.ok.inj observed)).1
  rw [pushContextWord_eq_reference] at outcome
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

private theorem runContextWord_continue_progress (price : FrameCtx → Nat) (read : FrameCtx → U256)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (observed : ((runContextWord price read ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ price ctx) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have exactPrice := runContextWord_continue_phi price read ctx f f' w w' observed
  omega

/-- Charge and push the word embedding of the current block beneficiary.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:71–102`. -/
def coinbase {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeCoinbase) (·.blockEnv.coinbase.toU256)

/-- Charge and push the timestamp word held by the current block context.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:105–136`. -/
def timestamp {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeTimestamp) (·.blockEnv.time)

/-- Charge and push all 32 randomness bytes as one unsigned big-endian word.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:172–202`. -/
def prevRandao {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodePrevRandao) (fun ctx ↦ U256.ofBeBytes32 ctx.blockEnv.prevRandao)

/-- Charge and push the widened chain identifier.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:238–265`. -/
def chainId {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeChainId) (fun ctx ↦ U256.ofNat ctx.blockEnv.chainId.toNat)

/-- Charge and push the widened block slot number.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:268–298`. -/
def slotNumber {m : Type → Type} [Monad m] : Handler m :=
  runContextWord (·.config.costs.opcodeSlotNum) (fun ctx ↦ U256.ofNat ctx.blockEnv.slotNumber.toNat)

end STFSpec.Vm.Instructions
