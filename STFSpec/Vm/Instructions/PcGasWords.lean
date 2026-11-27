/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# PC and GAS

Library `EthVmInstructions`. Charge before checking the entry PC or paid
execution balance for conversion to a stack word.
See `STFSpec/informal/modules/EthVmInstructions.md`.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def pushMachineReference (ctx : FrameCtx) (paid : Frame) (word : U256) : StepResult ctx :=
  match paid.stack.push word with
  | .error error => .halt paid error
  | .ok stack => .continue { paid with stack, pc := paid.pc + 1 }

private theorem machine_push_fits (stack : Stack) (word : U256) (error : ExceptionalHalt)
    (space : stack.size ≠ 1024) (failed : stack.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff stack word error).mp failed).1

private def pushMachine (ctx : FrameCtx) (paid : Frame) (word : U256) : StepResult ctx :=
  if full : paid.stack.size = 1024 then
    .halt paid .stackOverflow
  else
    match pushed : paid.stack.push word with
    | .error error => False.elim (machine_push_fits paid.stack word error full pushed)
    | .ok stack => .continue { paid with stack, pc := paid.pc + 1 }

private theorem pushMachine_eq_reference (ctx : FrameCtx) (paid : Frame) (word : U256) :
    pushMachine ctx paid word = pushMachineReference ctx paid word := by
  unfold pushMachine pushMachineReference
  by_cases full : paid.stack.size = 1024
  · have rejected := (Stack.push_eq_error_iff paid.stack word .stackOverflow).mpr ⟨full, rfl⟩
    simp only [dite_eq_left full, rejected]
  · simp only [dite_eq_right full]
    split
    · rename_i error failed
      exact False.elim (machine_push_fits paid.stack word error full failed)
    · rename_i stack pushed
      simp only [pushed]

private def runMachine {m : Type → Type} [Monad m] (site : OverflowSite) (price : Nat)
    (select : Frame → GasMeter → Nat) (ctx : FrameCtx) (entry : Frame) : VmM m (StepResult ctx) :=
  match chargeGas entry.gasMeter price with
  | .error error => pure (.halt entry error)
  | .ok paid =>
    match U256.ofNat? (select entry paid) with
    | none => fun _ ↦ ExceptT.mk (pure (.error (.u256Overflow site)))
    | some word => pure (pushMachine ctx { entry with gasMeter := paid } word)

/-- Charge and push the checked entry program counter.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:101–122`. -/
def pc {m : Type → Type} [Monad m] : Handler m :=
  fun ctx entry ↦ runMachine .pc ctx.config.costs.opcodePc (fun entry _ ↦ entry.pc) ctx entry

/-- Charge and push the checked paid execution balance.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:125–146`. -/
def gasLeft {m : Type → Type} [Monad m] : Handler m :=
  fun ctx entry ↦ runMachine .gasLeft ctx.config.costs.opcodeGas (fun _ paid ↦ paid.gasLeft) ctx entry

private theorem runMachine_denied {m : Type → Type} [Monad m]
    (site : OverflowSite) (price : Nat) (select : Frame → GasMeter → Nat)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (short : entry.gasMeter.gasLeft < price) :
    ((runMachine site price select ctx entry).run world).run =
      pure (.ok (.halt entry .outOfGas, world)) := by
  have denied := (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩
  simp only [runMachine, denied]
  rfl

private theorem runMachine_conversion_fault {m : Type → Type} [Monad m]
    (site : OverflowSite) (price : Nat) (select : Frame → GasMeter → Nat)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (payable : price ≤ entry.gasMeter.gasLeft)
    (oversized : 2^256 ≤ select entry { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price }) :
    ((runMachine site price select ctx entry).run world).run = pure (.error (.u256Overflow site)) := by
  simp only [runMachine, chargeGas_of_le _ _ payable, (U256.ofNat?_eq_none_iff _).mpr oversized]
  rfl

private theorem machine_fitting_word (value : Nat) (fits : value < 2^256) :
    U256.ofNat? value = some (U256.ofNat value) ∧ (U256.ofNat value).toNat = value := by
  have exactWord := U256.toNat_ofNat_of_lt fits
  exact ⟨(U256.ofNat?_eq_some_iff value _).mpr ⟨fits, exactWord⟩, exactWord⟩

private theorem runMachine_full {m : Type → Type} [Monad m]
    (site : OverflowSite) (price : Nat) (select : Frame → GasMeter → Nat)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (payable : price ≤ entry.gasMeter.gasLeft)
    (fits : select entry { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price } < 2^256)
    (full : entry.stack.size = 1024) :
    ((runMachine site price select ctx entry).run world).run =
      pure (.ok (.halt { entry with gasMeter.gasLeft := entry.gasMeter.gasLeft - price }
        .stackOverflow, world)) := by
  have rejected := (Stack.push_eq_error_iff entry.stack
    (U256.ofNat (select entry { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price }))
    .stackOverflow).mpr ⟨full, rfl⟩
  simp only [runMachine, chargeGas_of_le _ _ payable, (machine_fitting_word _ fits).1,
    pushMachine_eq_reference, pushMachineReference, rejected]
  rfl

private theorem runMachine_success {m : Type → Type} [Monad m]
    (site : OverflowSite) (price : Nat) (select : Frame → GasMeter → Nat)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (payable : price ≤ entry.gasMeter.gasLeft)
    (fits : select entry { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price } < 2^256)
    (space : entry.stack.size < 1024) :
    let paid := { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price }
    let value := select entry paid
    ∃ stack : Stack, stack.toList = U256.ofNat value :: entry.stack.toList ∧
      (U256.ofNat value).toNat = value ∧
      ((runMachine site price select ctx entry).run world).run =
        pure (.ok (.continue { entry with stack, pc := entry.pc + 1, gasMeter := paid }, world)) := by
  let paid := { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price }
  let value := select entry paid
  cases pushed : entry.stack.push (U256.ofNat value) with
  | error error => exact False.elim (machine_push_fits _ _ error (Nat.ne_of_lt space) pushed)
  | ok stack =>
    refine ⟨stack, ((Stack.push_eq_ok_iff _ _ _).mp pushed).2, (machine_fitting_word _ fits).2, ?_⟩
    change entry.stack.push (U256.ofNat (select entry
      { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price })) = .ok stack at pushed
    simp only [runMachine, chargeGas_of_le _ _ payable, (machine_fitting_word _ fits).1,
      pushMachine_eq_reference, pushMachineReference, pushed]
    rfl

private theorem runMachine_continue_phi (site : OverflowSite) (price : Nat)
    (select : Frame → GasMeter → Nat) (ctx : FrameCtx) (entry next : Frame)
    (world nextWorld : VmWorld Id)
    (ran : ((runMachine site price select ctx entry).run world).run = .ok (.continue next, nextWorld)) :
    next.gasMeter.phi + price = entry.gasMeter.phi := by
  cases charged : chargeGas entry.gasMeter price with
  | error error =>
    simp only [runMachine, charged] at ran
    change Except.ok (StepResult.halt (ctx := ctx) entry error, world) = _ at ran
    have impossible := (Prod.mk.inj (Except.ok.inj ran)).1
    cases impossible
  | ok paid =>
    cases converted : U256.ofNat? (select entry paid) with
    | none =>
      simp only [runMachine, charged, converted] at ran
      contradiction
    | some word =>
      simp only [runMachine, charged, converted, pushMachine_eq_reference, pushMachineReference] at ran
      cases pushed : entry.stack.push word with
      | error error =>
        rw [pushed] at ran
        change Except.ok (StepResult.halt (ctx := ctx) { entry with gasMeter := paid } error, world) = _ at ran
        have impossible := (Prod.mk.inj (Except.ok.inj ran)).1
        cases impossible
      | ok stack =>
        rw [pushed] at ran
        have nextFrame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
        subst next
        exact chargeGas_phi _ _ paid charged

private theorem runMachine_continue_progress (site : OverflowSite) (price : Nat)
    (select : Frame → GasMeter → Nat) (ctx : FrameCtx) (entry next : Frame)
    (world nextWorld : VmWorld Id)
    (ran : ((runMachine site price select ctx entry).run world).run = .ok (.continue next, nextWorld))
    (positive : 1 ≤ price) : next.gasMeter.phi + 1 ≤ entry.gasMeter.phi := by
  have accounting := runMachine_continue_phi site price select ctx entry next world nextWorld ran
  omega

end STFSpec.Vm.Instructions
