/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Instructions.Handler

/-!
# PUSH0 through PUSH32

Library `EthVmInstructions`. Q91 specifies the padded code read at a Nat offset.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def immediateWord (code : Bytes) (pc : Nat) (n : Fin 33) : U256 :=
  U256.ofNat (Uint.ofBeBytes (code.extractPadded (pc + 1) n.val))

private theorem immediateWord_decodes (code : Bytes) (pc : Nat) (n : Fin 33) :
    U256.ofBeBytes? (code.extractPadded (pc + 1) n.val) = some (immediateWord code pc n) := by
  let window := code.extractPadded (pc + 1) n.val
  have size : window.size = n.val := Bytes.size_extractPadded _ _ _
  have widthBound := n.isLt
  have count : window.size ≤ 32 := by omega
  have valueBound : Uint.ofBeBytes window < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt window)
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact (U256.ofBeBytes?_eq_some_iff window (immediateWord code pc n)).mpr
    ⟨count, U256.toNat_ofNat_of_lt valueBound⟩

private def pushCost (ctx : FrameCtx) (n : Fin 33) : Nat :=
  if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush

private def pushReference (n : Fin 33) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter (pushCost ctx n) with
  | .error e => .halt f e
  | .ok paid =>
    let afterPayment := { f with gasMeter := paid }
    let window := ctx.code.extractPadded (f.pc + 1) n.val
    let word := (U256.ofBeBytes? window).getD U256.zero
    match f.stack.push word with
    | .error e => .halt afterPayment e
    | .ok stack => .continue { afterPayment with pc := f.pc + 1 + n.val, stack }

private theorem push_cannot_fail (s : Stack) (word : U256) (e : ExceptionalHalt)
    (notFull : s.size ≠ 1024) (failed : s.push word = .error e) : False :=
  notFull ((Stack.push_eq_error_iff s word e).mp failed).1

/-- Check capacity after payment, before taking ownership of the entry stack. -/
private def pushLinear (n : Fin 33) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter (pushCost ctx n) with
  | .error e => .halt f e
  | .ok paid =>
    if full : f.stack.size = 1024 then
      .halt { f with gasMeter := paid } .stackOverflow
    else
      let word := immediateWord ctx.code f.pc n
      match pushed : f.stack.push word with
      | .error e => False.elim (push_cannot_fail f.stack word e full pushed)
      | .ok stack => .continue { f with pc := f.pc + 1 + n.val, stack, gasMeter := paid }

private theorem pushLinear_eq_reference (n : Fin 33) (ctx : FrameCtx) (f : Frame) :
    pushLinear n ctx f = pushReference n ctx f := by
  unfold pushLinear pushReference
  cases charged : chargeGas f.gasMeter (pushCost ctx n) with
  | error _ => rfl
  | ok _ =>
    dsimp only
    simp only [immediateWord_decodes, Option.getD_some]
    by_cases full : f.stack.size = 1024
    · have rejected := (Stack.push_eq_error_iff f.stack (immediateWord ctx.code f.pc n)
                          .stackOverflow).mpr ⟨full, rfl⟩
      simp only [dite_eq_left full, rejected]
    · simp only [dite_eq_right full]
      split
      · rename_i error failed
        exact False.elim (push_cannot_fail f.stack (immediateWord ctx.code f.pc n)
                            error full failed)
      · rename_i stack pushed
        simp only [pushed]

/-- Charge the selected execution price and push the padded big-endian code immediate.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:49–79`. Q91 supplies the offset domain. -/
def pushN (n : Fin 33) {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (pushLinear n ctx f)

/-- Gas shortage halts before the immediate read, with the whole entry frame and world. -/
theorem pushN_run_oog (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f.gasMeter.gasLeft < price →
      ((pushN n ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  dsimp only
  intro short
  have denied := (chargeGas_eq_error_iff f.gasMeter (pushCost ctx n) .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (pushLinear n ctx f, w)) = _
  rw [pushLinear_eq_reference]
  simp only [pushReference, denied]

/-- A full stack halts after payment, with the entry stack, PC and supplied world. -/
theorem pushN_run_overflow (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (full : f.stack.size = 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    price ≤ f.gasMeter.gasLeft →
      ((pushN n ctx f).run w).run = pure (Except.ok
        (.halt { f with gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - price } } .stackOverflow, w)) := by
  dsimp only
  intro enough
  have paid := chargeGas_of_le f.gasMeter (pushCost ctx n) enough
  have rejected := (Stack.push_eq_error_iff f.stack (immediateWord ctx.code f.pc n)
                        .stackOverflow).mpr ⟨full, rfl⟩
  change pure (Except.ok (pushLinear n ctx f, w)) = _
  rw [pushLinear_eq_reference]
  simp only [pushReference, paid, immediateWord_decodes, Option.getD_some, rejected]
  rfl

/-- With space and enough gas, push the immediate and advance the PC by one plus the width. -/
theorem pushN_run_success (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (space : f.stack.size < 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    let word := U256.ofNat (Uint.ofBeBytes (ctx.code.extractPadded (f.pc + 1) n.val))
    price ≤ f.gasMeter.gasLeft →
      ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
        ((pushN n ctx f).run w).run = pure (Except.ok
          (.continue { f with
            pc := f.pc + 1 + n.val
            stack
            gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) := by
  dsimp only
  intro enough
  have paid := chargeGas_of_le f.gasMeter (pushCost ctx n) enough
  cases pushed : f.stack.push (immediateWord ctx.code f.pc n) with
  | error e =>
    exact False.elim (push_cannot_fail f.stack (immediateWord ctx.code f.pc n)
      e (Nat.ne_of_lt space) pushed)
  | ok stack =>
    have model := ((Stack.push_eq_ok_iff f.stack stack _).mp pushed).2
    refine ⟨stack, ?_, model, ?_⟩
    · exact pushed
    · change pure (Except.ok (pushLinear n ctx f, w)) = _
      rw [pushLinear_eq_reference]
      simp only [pushReference, paid, immediateWord_decodes, Option.getD_some, pushed]
      rfl

/-- Exact selected execution charge on a continuing Id run. -/
theorem pushN_continue_phi (n : Fin 33) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pushN n ctx f).run w).run = .ok (.continue f', w')) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f'.gasMeter.phi + price = f.gasMeter.phi := by
  change f'.gasMeter.phi + pushCost ctx n = f.gasMeter.phi
  change Except.ok (pushLinear n ctx f, w) = .ok (.continue f', w') at run
  have outcome := (Prod.mk.inj (Except.ok.inj run)).1
  rw [pushLinear_eq_reference] at outcome
  cases charged : chargeGas f.gasMeter (pushCost ctx n) with
  | error _ =>
    simp only [pushReference, charged] at outcome
    contradiction
  | ok meter =>
    cases pushed : f.stack.push (immediateWord ctx.code f.pc n) with
    | error _ =>
      simp only [pushReference, charged, immediateWord_decodes, Option.getD_some, pushed] at outcome
      contradiction
    | ok _ =>
      simp only [pushReference, charged, immediateWord_decodes, Option.getD_some, pushed,
        StepResult.continue.injEq] at outcome
      subst f'
      exact chargeGas_phi f.gasMeter (pushCost ctx n) meter charged

/-- A positive selected price gives strict potential decrease on a continuing Id run. -/
theorem pushN_continue_progress
    (n : Fin 33) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pushN n ctx f).run w).run = .ok (.continue f', w')) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  dsimp only
  intro positive
  have accounting := pushN_continue_phi n ctx f f' w w' run
  dsimp only at accounting
  omega

end STFSpec.Vm.Instructions
