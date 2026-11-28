/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.IncorporateChild
import STFSpec.Vm.Core.Limits
import STFSpec.Vm.Instructions.ChildOutcome
import STFSpec.Vm.Instructions.CreateRequest

/-!
# CREATE and CREATE2 resume

Library `EthVmInstructions`. Incorporate the settled child, resolve the account
charge and put the result on the suspended parent's stack.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§2.5/3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def pushWithRoom (stack : Stack) (value : U256) (room : stack.size < STACK_DEPTH_LIMIT) :
    Stack :=
  match h : stack.push value with
  | .ok result => result
  | .error error =>
    False.elim (Nat.ne_of_lt room ((Stack.push_eq_error_iff stack value error).mp h).1)

private theorem pushWithRoom_toList (stack : Stack) (value : U256)
    (room : stack.size < STACK_DEPTH_LIMIT) :
    (pushWithRoom stack value room).toList = value :: stack.toList := by
  unfold pushWithRoom
  split
  · next result h => exact ((Stack.push_eq_ok_iff stack result value).mp h).2
  · next error h =>
    exact False.elim (Nat.ne_of_lt room ((Stack.push_eq_error_iff stack value error).mp h).1)

/-- Resume CREATE or CREATE2 after child settlement.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:171–185,238–239,303–304`. -/
def resumeAfterCreate (cfg : VmConfig) (parent : Frame) (req : CreateRequest)
    (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT) : Frame :=
  let failed := c.error.isSome
  let incorporated := incorporateChild parent c.frame failed c.settled
  let meter := if failed && req.newAccountCharged then
    creditStateGasRefund incorporated.gasMeter
      (cfg.stateCosts.bytesPerNewAccount * cfg.stateCosts.costPerStateByte)
  else incorporated.gasMeter
  let result := if failed then U256.ofNat 0 else req.contractAddress.toU256
  { incorporated with
    gasMeter := meter
    returnData := if failed then c.output else Bytes.empty
    stack := pushWithRoom parent.stack result hs
    pc := parent.pc + 1 }

private theorem resumeAfterCreate_pc_stack_returnData (cfg : VmConfig) (parent : Frame)
    (req : CreateRequest) (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT) :
    let resumed := resumeAfterCreate cfg parent req c hs
    let result := if c.error.isSome then U256.ofNat 0 else req.contractAddress.toU256
    resumed.pc = parent.pc + 1 ∧
      resumed.stack.toList = result :: parent.stack.toList ∧
      resumed.returnData = (if c.error.isSome then c.output else Bytes.empty) := by
  exact ⟨rfl, pushWithRoom_toList _ _ hs, rfl⟩

private theorem resumeAfterCreate_phi (cfg : VmConfig) (parent : Frame) (req : CreateRequest)
    (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT) :
    (resumeAfterCreate cfg parent req c hs).gasMeter.phi =
      parent.gasMeter.phi + c.frame.gasMeter.phi := by
  unfold resumeAfterCreate
  dsimp only
  split
  · rw [creditStateGasRefund_phi]
    exact incorporateChild_phi parent c.frame c.error.isSome c.settled
  · exact incorporateChild_phi parent c.frame c.error.isSome c.settled

private theorem resumeAfterCreate_eq_of_price_eq (a b : VmConfig) (parent : Frame)
    (req : CreateRequest) (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT)
    (price : a.stateCosts.bytesPerNewAccount * a.stateCosts.costPerStateByte =
      b.stateCosts.bytesPerNewAccount * b.stateCosts.costPerStateByte) :
    resumeAfterCreate a parent req c hs = resumeAfterCreate b parent req c hs := by
  unfold resumeAfterCreate
  dsimp only
  rw [price]

end STFSpec.Vm.Instructions
