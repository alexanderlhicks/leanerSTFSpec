/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# GASPRICE and BASEFEE

Library `EthVmInstructions`. Both instructions charge before narrowing their
selected fee and push the checked word before advancing the PC.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def pushPaidReference (ctx : FrameCtx) (frame : Frame) (word : U256) : StepResult ctx :=
  match frame.stack.push word with
  | .error error => .halt frame error
  | .ok stack => .continue { frame with stack, pc := frame.pc + 1 }

private theorem push_error_contradicts_space (stack : Stack) (word : U256) (error : ExceptionalHalt)
    (space : stack.size ≠ 1024) (failed : stack.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff stack word error).mp failed).1

private def pushPaid (ctx : FrameCtx) (frame : Frame) (word : U256) : StepResult ctx :=
  if full : frame.stack.size = 1024 then
    .halt frame .stackOverflow
  else
    match pushed : frame.stack.push word with
    | .error error => False.elim (push_error_contradicts_space frame.stack word error full pushed)
    | .ok stack => .continue { frame with stack, pc := frame.pc + 1 }

private theorem pushPaid_eq_reference (ctx : FrameCtx) (frame : Frame) (word : U256) :
    pushPaid ctx frame word = pushPaidReference ctx frame word := by
  unfold pushPaid pushPaidReference
  by_cases full : frame.stack.size = 1024
  · have rejected := (Stack.push_eq_error_iff frame.stack word .stackOverflow).mpr ⟨full, rfl⟩
    simp only [dite_eq_left full, rejected]
  · simp only [dite_eq_right full]
    split
    · rename_i error failed
      exact False.elim (push_error_contradicts_space frame.stack word error full failed)
    · rename_i stack pushed
      simp only [pushed]

private def runFee {m : Type → Type} [Monad m] (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame : Frame) : VmM m (StepResult ctx) :=
  match chargeGas frame.gasMeter price with
  | .error error => pure (.halt frame error)
  | .ok paid =>
    match U256.ofNat? fee with
    | none => fun _ ↦ ExceptT.mk (pure (.error (.u256Overflow site)))
    | some word => pure (pushPaid ctx { frame with gasMeter := paid } word)

/-- Charge and push the checked effective transaction gas price.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:307–327`. -/
def gasprice {m : Type → Type} [Monad m] : Handler m :=
  fun ctx frame ↦ runFee .gasPrice ctx.config.costs.opcodeGasPrice ctx.txEnv.effectiveGasPrice ctx frame

/-- Charge and push the checked current block base fee.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:539–559`. -/
def baseFee {m : Type → Type} [Monad m] : Handler m :=
  fun ctx frame ↦ runFee .baseFee ctx.config.costs.opcodeBaseFee ctx.blockEnv.baseFeePerGas ctx frame

private theorem runFee_denied {m : Type → Type} [Monad m] (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (short : frame.gasMeter.gasLeft < price) :
    ((runFee site price fee ctx frame).run world).run = pure (.ok (.halt frame .outOfGas, world)) := by
  have rejected := (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩
  simp only [runFee, rejected]
  rfl

private theorem runFee_conversion_fault {m : Type → Type} [Monad m]
    (site : OverflowSite) (price fee : Nat) (ctx : FrameCtx) (frame : Frame) (world : VmWorld m)
    (enough : price ≤ frame.gasMeter.gasLeft) (oversized : 2 ^ 256 ≤ fee) :
    ((runFee site price fee ctx frame).run world).run = pure (.error (.u256Overflow site)) := by
  simp only [runFee, chargeGas_of_le _ _ enough, (U256.ofNat?_eq_none_iff _).mpr oversized]
  rfl

private theorem word_of_fitting_fee (fee : Nat) (fits : fee < 2 ^ 256) :
    U256.ofNat? fee = some (U256.ofNat fee) :=
  (U256.ofNat?_eq_some_iff fee _).mpr ⟨fits, U256.toNat_ofNat_of_lt fits⟩

private theorem runFee_full {m : Type → Type} [Monad m] (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m)
    (enough : price ≤ frame.gasMeter.gasLeft) (fits : fee < 2 ^ 256) (full : frame.stack.size = 1024) :
    ((runFee site price fee ctx frame).run world).run =
      pure (.ok (.halt { frame with gasMeter.gasLeft := frame.gasMeter.gasLeft - price }
        .stackOverflow, world)) := by
  have rejected := (Stack.push_eq_error_iff frame.stack (U256.ofNat fee) .stackOverflow).mpr ⟨full, rfl⟩
  simp only [runFee, chargeGas_of_le _ _ enough, word_of_fitting_fee _ fits, pushPaid_eq_reference,
    pushPaidReference, rejected]
  rfl

private theorem runFee_success {m : Type → Type} [Monad m] (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (enough : price ≤ frame.gasMeter.gasLeft)
    (fits : fee < 2 ^ 256) (space : frame.stack.size < 1024) :
    ∃ stack, stack.toList = U256.ofNat fee :: frame.stack.toList ∧
      ((runFee site price fee ctx frame).run world).run =
        pure (.ok (.continue { frame with
          stack := stack
          pc := frame.pc + 1
          gasMeter.gasLeft := frame.gasMeter.gasLeft - price }, world)) := by
  cases pushed : frame.stack.push (U256.ofNat fee) with
  | error error =>
    exact False.elim (push_error_contradicts_space _ _ error (Nat.ne_of_lt space) pushed)
  | ok stack =>
    refine ⟨stack, ((Stack.push_eq_ok_iff _ _ _).mp pushed).2, ?_⟩
    simp only [runFee, chargeGas_of_le _ _ enough, word_of_fitting_fee _ fits, pushPaid_eq_reference,
      pushPaidReference, pushed]
    rfl

private theorem runFee_continue_phi (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame next : Frame) (world nextWorld : VmWorld Id)
    (result : ((runFee site price fee ctx frame).run world).run = .ok (.continue next, nextWorld)) :
    next.gasMeter.phi + price = frame.gasMeter.phi := by
  cases charged : chargeGas frame.gasMeter price with
  | error error =>
    simp only [runFee, charged] at result
    change Except.ok (StepResult.halt (ctx := ctx) frame error, world) = _ at result
    have impossible := (Prod.mk.inj (Except.ok.inj result)).1
    cases impossible
  | ok meter =>
    cases converted : U256.ofNat? fee with
    | none =>
      simp only [runFee, charged, converted] at result
      contradiction
    | some word =>
      simp only [runFee, charged, converted, pushPaid_eq_reference, pushPaidReference] at result
      cases pushed : frame.stack.push word with
      | error error =>
        rw [pushed] at result
        change Except.ok (StepResult.halt (ctx := ctx) { frame with gasMeter := meter } error, world) = _ at result
        have impossible := (Prod.mk.inj (Except.ok.inj result)).1
        cases impossible
      | ok stack =>
        rw [pushed] at result
        have nextFrame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj result)).1
        subst next
        exact chargeGas_phi frame.gasMeter price meter charged

private theorem runFee_continue_progress (site : OverflowSite) (price fee : Nat)
    (ctx : FrameCtx) (frame next : Frame) (world nextWorld : VmWorld Id)
    (result : ((runFee site price fee ctx frame).run world).run = .ok (.continue next, nextWorld))
    (positive : 1 ≤ price) : next.gasMeter.phi + 1 ≤ frame.gasMeter.phi := by
  have accounting := runFee_continue_phi site price fee ctx frame next world nextWorld result
  omega

end STFSpec.Vm.Instructions
