/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Core.Memory
import STFSpec.Vm.Instructions.Handler

/-!
# CALLDATALOAD

Library `EthVmInstructions`. Pop and charge before reading the padded
32-byte window of the frame's input. See EthVmInstructions §§2/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

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

private def pushWord (tail : Stack) (word : U256) (room : tail.size < 1024) : Stack :=
  match pushed : tail.push word with
  | .ok stack => stack
  | .error error => False.elim (push_error_with_room tail word room error pushed)

private theorem pushWord_actual (tail : Stack) (word : U256) (room : tail.size < 1024) :
    tail.push word = .ok (pushWord tail word room) := by
  unfold pushWord
  split
  · rename_i stack pushed
    exact pushed
  · rename_i error failed
    exact False.elim (push_error_with_room tail word room error failed)

private def width : U256 := U256.ofNat 32

private def window (data : Bytes) (offset : U256) : Bytes :=
  bufferRead data offset width

private theorem window_size (data : Bytes) (offset : U256) :
    (window data offset).size = 32 :=
  (bufferRead_size data offset width).trans rfl

private def word (data : Bytes) (offset : U256) : U256 :=
  U256.ofNat (Uint.ofBeBytes (window data offset))

private theorem numeric (data : Bytes) (offset : U256) :
    (word data offset).toNat = Uint.ofBeBytes (window data offset) := by
  apply U256.toNat_ofNat_of_lt
  simpa only [window_size] using Uint.ofBeBytes_lt (window data offset)

private theorem checked (data : Bytes) (offset : U256) :
    U256.ofBeBytes? (window data offset) = some (word data offset) := by
  apply (U256.ofBeBytes?_eq_some_iff _ _).2
  exact ⟨Nat.le_of_eq (window_size data offset), numeric data offset⟩

private theorem padded_model (data : Bytes) (offset : U256) :
    (word data offset).toNat =
      ((data.toList.drop offset.toNat).take 32 ++
        List.replicate (32 - min 32 (data.size - offset.toNat)) 0).foldl
          (fun acc digit ↦ 256 * acc + UInt8.toNat digit) 0 := by
  rw [numeric, Uint.ofBeBytes_eq_fold, window, bufferRead_toList]
  rfl

private def paidResult (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (meter : GasMeter) (value : U256) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, returnData, addresses, slots⟩ =>
    .continue ⟨pc + 1, pushWord stack value room, memory, meter, logs, deleted,
      returnData, addresses, slots⟩

private theorem paidResult_eq (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (meter : GasMeter) (value : U256) :
    paidResult ctx f room meter value =
      .continue { f with
        pc := f.pc + 1
        stack := pushWord f.stack value room
        gasMeter := meter } := by
  cases f
  rfl

private def afterPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (offset : U256) (room : f.stack.size < 1024) : VmM m (StepResult ctx) :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeCallDataLoad with
  | .error error => pure (.halt f error)
  | .ok meter => pure (paidResult ctx f room meter (word ctx.callData offset))

/-- Pop the full offset, charge, then push the padded big-endian input word.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:159–183` at the pin. -/
def calldataload {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (offset, residual) => afterPop ctx residual offset (poppedFrame_room f residual offset popped)

private theorem underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (missing : f.stack.pop = .error .stackUnderflow) :
    ((calldataload ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  have popped : popFrame f = .error (f, .stackUnderflow) := by
    simp [popFrame_eq, popFrameReference, missing]
  unfold calldataload
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i value residual observed
    rw [popped] at observed
    contradiction

private theorem ofPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (offset : U256) (tail : Stack) (popped : f.stack.pop = .ok (offset, tail)) :
    (calldataload ctx f : VmM m (StepResult ctx)) =
      afterPop ctx { f with stack := tail } offset (room_after_pop f.stack tail offset popped) := by
  have framePop : popFrame f = .ok (offset, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold calldataload
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private theorem denied {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (offset : U256) (tail : Stack) (popped : f.stack.pop = .ok (offset, tail))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeCallDataLoad) :
    ((calldataload ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have failed := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeCallDataLoad .outOfGas).mpr
    ⟨short, rfl⟩
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, failed]
  rfl

private theorem paid {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (offset : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (offset, tail))
    (payment : chargeGas f.gasMeter ctx.config.costs.opcodeCallDataLoad = .ok meter) :
    ∃ stack, tail.push (word ctx.callData offset) = .ok stack ∧
      stack.toList = word ctx.callData offset :: tail.toList ∧
      ((calldataload ctx f).run w).run =
        pure (.ok (.continue { f with pc := f.pc + 1, stack := stack, gasMeter := meter }, w)) := by
  let value := word ctx.callData offset
  let room := room_after_pop f.stack tail offset popped
  have actual := pushWord_actual tail value room
  refine ⟨pushWord tail value room, actual, ((Stack.push_eq_ok_iff tail _ value).mp actual).2, ?_⟩
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, payment, paidResult_eq]
  rfl

private theorem continuationPhi (ctx : FrameCtx) (f next : Frame) (w nextWorld : VmWorld Id)
    (offset : U256) (tail : Stack) (popped : f.stack.pop = .ok (offset, tail))
    (ran : ((calldataload ctx f).run w).run = .ok (.continue next, nextWorld)) :
    next.gasMeter.phi + ctx.config.costs.opcodeCallDataLoad = f.gasMeter.phi := by
  cases payment : chargeGas f.gasMeter ctx.config.costs.opcodeCallDataLoad with
  | error error =>
    rw [ofPop _ _ _ _ popped] at ran
    simp only [afterPop, payment] at ran
    change Except.ok (StepResult.halt _ error, w) = _ at ran
    cases (Prod.mk.inj (Except.ok.inj ran)).1
  | ok meter =>
    obtain ⟨stack, _, _, result⟩ := paid ctx f w offset tail meter popped payment
    rw [result] at ran
    have same := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
    rw [← same]
    exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeCallDataLoad meter payment

private theorem continuationProgress (ctx : FrameCtx) (f next : Frame) (w nextWorld : VmWorld Id)
    (offset : U256) (tail : Stack) (popped : f.stack.pop = .ok (offset, tail))
    (ran : ((calldataload ctx f).run w).run = .ok (.continue next, nextWorld))
    (positive : 1 ≤ ctx.config.costs.opcodeCallDataLoad) :
    next.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := continuationPhi ctx f next w nextWorld offset tail popped ran
  omega

end STFSpec.Vm.Instructions
