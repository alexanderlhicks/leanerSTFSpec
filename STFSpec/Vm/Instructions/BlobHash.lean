/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Instructions.Handler

/-!
# BLOBHASH

Library `EthVmInstructions`. After charging, read the transaction's versioned
hash at the popped index. An index outside the array yields zero.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def blobWord (hashes : Array VersionedHash) (index : U256) : U256 :=
  match hashes[index.toNat]? with
  | none => U256.zero
  | some hash => U256.ofBeBytes32 hash.toBytes32

private theorem blobWord_bytes (hashes : Array VersionedHash) (index : U256)
    (fits : index.toNat < hashes.size) :
    (blobWord hashes index).toBeBytes32 = (hashes[index.toNat]'fits).toBytes32 := by
  unfold blobWord
  rw [getElem?_pos hashes _ fits]
  exact U256.toBeBytes32_ofBeBytes32 _

private theorem blobWord_outside (hashes : Array VersionedHash) (index : U256)
    (outside : hashes.size ≤ index.toNat) : blobWord hashes index = U256.zero := by
  unfold blobWord
  rw [getElem?_neg hashes _ (Nat.not_lt.mpr outside)]

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

private def pushBlobWord (tail : Stack) (word : U256) (room : tail.size < 1024) : Stack :=
  match pushed : tail.push word with
  | .ok stack => stack
  | .error error => False.elim (push_error_with_room tail word room error pushed)

private theorem pushBlobWord_actual (tail : Stack) (word : U256) (room : tail.size < 1024) :
    tail.push word = .ok (pushBlobWord tail word room) := by
  unfold pushBlobWord
  split
  · rename_i stack pushed
    exact pushed
  · rename_i error failed
    exact False.elim (push_error_with_room tail word room error failed)

private def paidResult (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (meter : GasMeter) (word : U256) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, returnData, addresses, slots⟩ =>
    .continue ⟨pc + 1, pushBlobWord stack word room, memory, meter, logs, deleted,
      returnData, addresses, slots⟩

private theorem paidResult_eq (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (meter : GasMeter) (word : U256) :
    paidResult ctx f room meter word =
      .continue { f with pc := f.pc + 1, stack := pushBlobWord f.stack word room, gasMeter := meter } := by
  cases f
  rfl

private def blobHashAfterPop (ctx : FrameCtx) (f : Frame) (index : U256)
    (room : f.stack.size < 1024) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeBlobHash with
  | .error error => .halt f error
  | .ok meter => paidResult ctx f room meter (blobWord ctx.txEnv.blobVersionedHashes index)

/-- Pop the full index, charge the BLOBHASH tariff, then push the selected hash word or zero.
EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:562–586` at the pin. -/
def blobHash {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (index, residual) =>
    pure (blobHashAfterPop ctx residual index (poppedFrame_room f residual index popped))

private theorem blobHash_of_error {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (error : ExceptionalHalt) (missing : f.stack.pop = .error error) :
    (blobHash ctx f : VmM m (StepResult ctx)) = pure (.halt f error) := by
  have popped : popFrame f = .error (f, error) := by simp [popFrame_eq, popFrameReference, missing]
  unfold blobHash
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i word residual observed
    rw [popped] at observed
    contradiction

private theorem blobHash_of_pop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail)) :
    (blobHash ctx f : VmM m (StepResult ctx)) =
      pure (blobHashAfterPop ctx { f with stack := tail } word (room_after_pop f.stack tail word popped)) := by
  have framePop : popFrame f = .ok (word, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold blobHash
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private theorem underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (missing : f.stack.pop = .error .stackUnderflow) :
    ((blobHash ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  rw [blobHash_of_error _ _ _ missing]
  rfl

private theorem deniedPayment {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (index : U256) (tail : Stack) (popped : f.stack.pop = .ok (index, tail))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeBlobHash) :
    ((blobHash ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeBlobHash .outOfGas).mpr
    ⟨short, rfl⟩
  rw [blobHash_of_pop _ _ _ _ popped]
  simp only [blobHashAfterPop, denied]
  rfl

private theorem paidSuccess {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (index : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (index, tail))
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeBlobHash = .ok meter) :
    let word := blobWord ctx.txEnv.blobVersionedHashes index
    ∃ stack, tail.push word = .ok stack ∧ stack.toList = word :: tail.toList ∧
      ((blobHash ctx f).run w).run =
        pure (.ok (.continue { f with pc := f.pc + 1, stack, gasMeter := meter }, w)) ∧
      meter.phi + ctx.config.costs.opcodeBlobHash = f.gasMeter.phi := by
  intro word
  let room := room_after_pop f.stack tail index popped
  have pushed := pushBlobWord_actual tail word room
  refine ⟨pushBlobWord tail word room, pushed, ((Stack.push_eq_ok_iff tail _ word).mp pushed).2,
    ?_, chargeGas_phi f.gasMeter _ meter paid⟩
  rw [blobHash_of_pop _ _ _ _ popped]
  simp only [blobHashAfterPop, paid, paidResult_eq]
  rfl

private theorem continuationPotential (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (index : U256) (tail : Stack) (popped : f.stack.pop = .ok (index, tail))
    (ran : ((blobHash ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeBlobHash = f.gasMeter.phi := by
  cases charge : chargeGas f.gasMeter ctx.config.costs.opcodeBlobHash with
  | error error =>
    rw [blobHash_of_pop _ _ _ _ popped] at ran
    simp only [blobHashAfterPop, charge] at ran
    change Except.ok (StepResult.halt _ error, w) = _ at ran
    cases (Prod.mk.inj (Except.ok.inj ran)).1
  | ok meter =>
    obtain ⟨_, _, _, result, potential⟩ := paidSuccess ctx f w index tail meter popped charge
    rw [result] at ran
    have frame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
    rw [← frame]
    exact potential

private theorem continuationProgress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (index : U256) (tail : Stack) (popped : f.stack.pop = .ok (index, tail))
    (ran : ((blobHash ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeBlobHash) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := continuationPotential ctx f f' w w' index tail popped ran
  omega

end STFSpec.Vm.Instructions
