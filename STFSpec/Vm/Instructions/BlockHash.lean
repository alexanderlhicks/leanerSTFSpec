/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.AncestorAccess
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# BLOCKHASH

Library `EthVmInstructions`. Pop and charge before selecting a block
hash. Record a supplied ancestor through the State action before pushing.
See `STFSpec/informal/modules/EthVmInstructions.md` §§2/5/7.
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

private def ancestor (hashes : Array Hash32) (current requested : Nat) :
    Except Nat (Option (Nat × Hash32)) :=
  if admitted : requested < current ∧ current ≤ requested + 256 then
    let offset := current - requested
    if present : offset ≤ hashes.size then
      .ok (some (offset, hashes[hashes.size - offset]'(by
        have _positive := admitted.1
        omega)))
    else .error offset
  else .ok none

private theorem outsideDefaults (hashes : Array Hash32) (current requested : Nat)
    (outside : current ≤ requested ∨ requested + 256 < current) :
    ancestor hashes current requested = .ok none := by
  unfold ancestor
  have denied : ¬ (requested < current ∧ current ≤ requested + 256) := by omega
  rw [dite_eq_right denied]

private theorem missingExactOffset (hashes : Array Hash32) (current requested : Nat)
    (valid : requested < current ∧ current ≤ requested + 256)
    (tooShort : hashes.size < current - requested) :
    ancestor hashes current requested = .error (current - requested) := by
  unfold ancestor
  rw [dite_eq_left valid, dite_eq_right (Nat.not_le.mpr tooShort)]

private theorem exactFound (hashes : Array Hash32) (current requested : Nat)
    (valid : requested < current ∧ current ≤ requested + 256)
    (present : current - requested ≤ hashes.size) :
    ancestor hashes current requested =
      .ok (some (current - requested, hashes[hashes.size - (current - requested)]'(by
        have _positive := valid.1
        omega))) := by
  unfold ancestor
  rw [dite_eq_left valid, dite_eq_left present]

private theorem offsetRange (current requested : Nat)
    (valid : requested < current ∧ current ≤ requested + 256) :
    1 ≤ current - requested ∧ current - requested ≤ 256 := by omega

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
    (word : U256) (room : f.stack.size < 1024) : VmM m (StepResult ctx) :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeBlockHash with
  | .error error => pure (.halt f error)
  | .ok meter =>
    match ancestor ctx.blockEnv.blockHashes ctx.blockEnv.number word.toNat with
    | .error offset => fun _ ↦ ExceptT.mk (pure (.error (.ancestorHashUnavailable offset)))
    | .ok none => pure (paidResult ctx f room meter U256.zero)
    | .ok (some (offset, hash)) => do
      liftState (trackAncestorAccess offset)
      pure (paidResult ctx f room meter (U256.ofBeBytes32 hash.toBytes32))

/-- Pop the requested block number, charge, then select and record a supplied ancestor.
EELS `src/ethereum/forks/amsterdam/vm/instructions/block.py:22–68` at the pin. -/
def blockHash {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (word, residual) => afterPop ctx residual word (poppedFrame_room f residual word popped)

private theorem underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (missing : f.stack.pop = .error .stackUnderflow) :
    ((blockHash ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  have popped : popFrame f = .error (f, .stackUnderflow) := by
    simp [popFrame_eq, popFrameReference, missing]
  unfold blockHash
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i word residual observed
    rw [popped] at observed
    contradiction

private theorem ofPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail)) :
    (blockHash ctx f : VmM m (StepResult ctx)) =
      afterPop ctx { f with stack := tail } word (room_after_pop f.stack tail word popped) := by
  have framePop : popFrame f = .ok (word, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold blockHash
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private theorem denied {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeBlockHash) :
    ((blockHash ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have failed := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeBlockHash .outOfGas).mpr
    ⟨short, rfl⟩
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, failed]
  rfl

private theorem paidOutside {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (word : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeBlockHash = .ok meter)
    (outside : ctx.blockEnv.number ≤ word.toNat ∨ word.toNat + 256 < ctx.blockEnv.number) :
    ∃ stack, tail.push U256.zero = .ok stack ∧ stack.toList = U256.zero :: tail.toList ∧
      ((blockHash ctx f).run w).run =
        pure (.ok (.continue { f with pc := f.pc + 1, stack := stack, gasMeter := meter }, w)) := by
  let room := room_after_pop f.stack tail word popped
  have actual := pushWord_actual tail U256.zero room
  refine ⟨pushWord tail U256.zero room, actual, ((Stack.push_eq_ok_iff tail _ U256.zero).mp actual).2, ?_⟩
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, paid, outsideDefaults _ _ _ outside, paidResult_eq]
  rfl

private theorem paidMissing {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (word : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeBlockHash = .ok meter)
    (valid : word.toNat < ctx.blockEnv.number ∧ ctx.blockEnv.number ≤ word.toNat + 256)
    (short : ctx.blockEnv.blockHashes.size < ctx.blockEnv.number - word.toNat) :
    ((blockHash ctx f).run w).run =
      pure (.error (.ancestorHashUnavailable (ctx.blockEnv.number - word.toNat))) := by
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, paid, missingExactOffset _ _ _ valid short]
  rfl

private theorem paidFound {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (word : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter ctx.config.costs.opcodeBlockHash = .ok meter)
    (valid : word.toNat < ctx.blockEnv.number ∧ ctx.blockEnv.number ≤ word.toNat + 256)
    (present : ctx.blockEnv.number - word.toNat ≤ ctx.blockEnv.blockHashes.size) :
    let offset := ctx.blockEnv.number - word.toNat
    let hash := ctx.blockEnv.blockHashes[ctx.blockEnv.blockHashes.size - offset]'(by
      have positive := (offsetRange _ _ valid).1
      omega)
    let value := U256.ofBeBytes32 hash.toBytes32
    ∃ stack, tail.push value = .ok stack ∧ stack.toList = value :: tail.toList ∧
      ((blockHash ctx f).run w).run =
        (((do
          liftState (trackAncestorAccess offset)
          pure (.continue { f with pc := f.pc + 1, stack := stack, gasMeter := meter }))
          : VmM m (StepResult ctx)).run w).run := by
  dsimp only
  let value := U256.ofBeBytes32
    (ctx.blockEnv.blockHashes[ctx.blockEnv.blockHashes.size - (ctx.blockEnv.number - word.toNat)]'(by
      have positive := (offsetRange _ _ valid).1
      omega)).toBytes32
  let room := room_after_pop f.stack tail word popped
  have actual := pushWord_actual tail value room
  refine ⟨pushWord tail value room, actual, ((Stack.push_eq_ok_iff tail _ value).mp actual).2, ?_⟩
  rw [ofPop _ _ _ _ popped]
  simp only [afterPop, paid, exactFound _ _ _ valid present, paidResult_eq]
  rfl

private theorem continuationPhi (ctx : FrameCtx) (f next : Frame) (w nextWorld : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (ran : ((blockHash ctx f).run w).run = .ok (.continue next, nextWorld)) :
    next.gasMeter.phi + ctx.config.costs.opcodeBlockHash = f.gasMeter.phi := by
  rw [ofPop _ _ _ _ popped] at ran
  cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeBlockHash with
  | error error =>
    simp only [afterPop, paid] at ran
    change Except.ok (StepResult.halt _ error, w) = _ at ran
    cases (Prod.mk.inj (Except.ok.inj ran)).1
  | ok meter =>
    have spent := chargeGas_phi f.gasMeter ctx.config.costs.opcodeBlockHash meter paid
    cases selected : ancestor ctx.blockEnv.blockHashes ctx.blockEnv.number word.toNat with
    | error offset =>
      simp only [afterPop, paid, selected] at ran
      change Except.error (VmFault.ancestorHashUnavailable offset) = _ at ran
      contradiction
    | ok result =>
      cases result with
      | none =>
        simp only [afterPop, paid, selected, paidResult_eq] at ran
        change Except.ok (StepResult.continue _, w) = _ at ran
        have same := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
        rw [← same]
        exact spent
      | some pair =>
        rcases pair with ⟨offset, hash⟩
        simp only [afterPop, paid, selected, paidResult_eq, StateT.run_bind, ExceptT.run_bind,
          liftState_run] at ran
        cases state : ((trackAncestorAccess offset).run w.tx).run with
        | error error =>
          rw [state] at ran
          change Except.error (VmFault.state error) = _ at ran
          contradiction
        | ok pair =>
          rcases pair with ⟨_, tx⟩
          rw [state] at ran
          change Except.ok (StepResult.continue _, { w with tx := tx }) = _ at ran
          have same := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
          rw [← same]
          exact spent

private theorem continuationProgress (ctx : FrameCtx) (f next : Frame) (w nextWorld : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (ran : ((blockHash ctx f).run w).run = .ok (.continue next, nextWorld))
    (positive : 1 ≤ ctx.config.costs.opcodeBlockHash) :
    next.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := continuationPhi ctx f next w nextWorld word tail popped ran
  omega

end STFSpec.Vm.Instructions
