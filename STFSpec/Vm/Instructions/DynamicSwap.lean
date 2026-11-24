/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Vm.Core.StackDecoders

/-!
# Immediate stack swaps

Library `EthVmInstructions`. SWAPN and EXCHANGE charge before reading and decoding
one padded byte. They exchange two existing stack entries.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def swapReference (i j : Nat) (ctx : FrameCtx) (paid : Frame) :
    StepResult ctx :=
  match paid.stack.swap? i j with
  | none => .halt paid .stackUnderflow
  | some stack => .continue { paid with pc := paid.pc + 2, stack }

private theorem swap_none_contradicts_bound (stack : Stack) (i j : Nat)
    (fits : max i j < stack.size) (failed : stack.swap? i j = none) : False := by
  have bad := (Stack.swap?_eq_none_iff stack i j).mp failed
  rw [Nat.max_lt] at fits
  omega

private def swapLinear (i j : Nat) (ctx : FrameCtx) (paid : Frame) : StepResult ctx :=
  if fits : max i j < paid.stack.size then
    match switched : paid.stack.swap? i j with
    | none => False.elim (swap_none_contradicts_bound paid.stack i j fits switched)
    | some stack => .continue { paid with pc := paid.pc + 2, stack }
  else
    .halt paid .stackUnderflow

private theorem swapLinear_eq (i j : Nat) (ctx : FrameCtx) (paid : Frame) :
    swapLinear i j ctx paid = swapReference i j ctx paid := by
  unfold swapLinear swapReference
  by_cases fits : max i j < paid.stack.size
  · simp only [dite_eq_left fits]
    split
    · rename_i none
      exact False.elim (swap_none_contradicts_bound paid.stack i j fits none)
    · rename_i stack observed
      simp only [observed]
  · have bad : paid.stack.size ≤ i ∨ paid.stack.size ≤ j := by
      rw [Nat.max_lt] at fits
      omega
    simp only [dite_eq_right fits, (Stack.swap?_eq_none_iff paid.stack i j).mpr bad]

private def readImmediate (code : Bytes) (pc : Nat) : UInt8 :=
  if available : pc + 1 < code.size then code[pc + 1]'available else 0

private theorem readImmediate_eq_getD (code : Bytes) (pc : Nat) :
    readImmediate code pc = (code[pc + 1]?).getD 0 := by
  by_cases available : pc + 1 < code.size
  · simp [readImmediate, getElem?_pos, available]
  · simp [readImmediate, getElem?_neg, available]

private theorem readImmediate_eq (code : Bytes) (pc : Nat) :
    readImmediate code pc =
      (code.extractPadded (pc + 1) 1)[0]'(by rw [Bytes.size_extractPadded]; decide) := by
  rw [Bytes.getElem_extractPadded code (pc + 1) 1 0 (by decide)]
  simp only [Nat.add_zero, readImmediate]

private theorem admitted_read (code : Bytes) (pc : Nat)
    (offsetBound : pc + 1 < 2 ^ 256) :
    (bufferRead code (U256.ofNat (pc + 1)) (U256.ofNat 1)).toList =
      [readImmediate code pc] := by
  have oneFits : (1 : Nat) < 2 ^ 256 := by decide
  rw [bufferRead_eq_extractPadded, U256.toNat_ofNat_of_lt offsetBound,
    U256.toNat_ofNat_of_lt oneFits]
  apply List.ext_getElem
  · simp only [Bytes.length_toList, Bytes.size_extractPadded, List.length_cons, List.length_nil]
  · intro i hi _
    have zero : i = 0 := by
      simpa only [Bytes.length_toList, Bytes.size_extractPadded, Nat.lt_one_iff] using hi
    subst i
    rw [Bytes.getElem_toList _ 0 (by rw [Bytes.size_extractPadded]; decide)]
    exact (readImmediate_eq code pc).symm

private def swapnModel (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeSwapn with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodeSingle (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok depth => swapReference 0 depth ctx paid

private def exchangeModel (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeExchange with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodePair (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok (i, j) => swapReference i j ctx paid

private def swapnLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeSwapn with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodeSingle (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok depth => swapLinear 0 depth ctx paid

private def exchangeLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeExchange with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodePair (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok (i, j) => swapLinear i j ctx paid

private theorem swapnLinear_eq (ctx : FrameCtx) (f : Frame) :
    swapnLinear ctx f = swapnModel ctx f := by
  unfold swapnLinear swapnModel
  cases chargeGas f.gasMeter ctx.config.costs.opcodeSwapn with
  | error => rfl
  | ok =>
    cases decodeSingle (readImmediate ctx.code f.pc) with
    | error => rfl
    | ok => apply swapLinear_eq

private theorem exchangeLinear_eq (ctx : FrameCtx) (f : Frame) :
    exchangeLinear ctx f = exchangeModel ctx f := by
  unfold exchangeLinear exchangeModel
  cases chargeGas f.gasMeter ctx.config.costs.opcodeExchange with
  | error => rfl
  | ok =>
    cases decodePair (readImmediate ctx.code f.pc) with
    | error => rfl
    | ok pair =>
      rcases pair with ⟨i, j⟩
      apply swapLinear_eq

private def debit (p : Nat) (f : Frame) : Frame :=
  { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - p } }

private theorem swap_reference_underflow (i j : Nat) (ctx : FrameCtx) (paid : Frame)
    (short : paid.stack.size ≤ i ∨ paid.stack.size ≤ j) :
    swapReference i j ctx paid = .halt paid .stackUnderflow := by
  simp only [swapReference, (Stack.swap?_eq_none_iff _ _ _).mpr short]

private theorem swap_reference_success (i j : Nat) (ctx : FrameCtx) (paid : Frame)
    (left : i < paid.stack.size) (right : j < paid.stack.size) :
    ∃ (stack : Stack) (a b : U256),
      paid.stack.swap? i j = some stack ∧
      paid.stack.toList[i]? = some a ∧ paid.stack.toList[j]? = some b ∧
      stack.toList = (paid.stack.toList.set i b).set j a ∧
      swapReference i j ctx paid = .continue { paid with pc := paid.pc + 2, stack } := by
  cases result : paid.stack.swap? i j with
  | none => exact False.elim (swap_none_contradicts_bound paid.stack i j (by omega) result)
  | some stack =>
    obtain ⟨a, b, ha, hb, model⟩ := (Stack.swap?_eq_some_iff paid.stack stack i j).mp result
    refine ⟨stack, a, b, rfl, ha, hb, model, ?_⟩
    simp only [swapReference, result]

private theorem swap_reference_continued_meter (i j : Nat) (ctx : FrameCtx) (paid next : Frame)
    (continued : swapReference i j ctx paid = .continue next) :
    next.gasMeter = paid.gasMeter := by
  unfold swapReference at continued
  split at continued
  · contradiction
  · simp only [StepResult.continue.injEq] at continued
    subst next
    rfl

/-- Charge, decode one padded byte at the Q91 Nat offset, and swap the top word
with the word at the decoded index.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:245–278`. -/
def swapn {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (swapnLinear ctx f)

/-- Gas shortage retains the entry frame and world before reading the immediate. -/
theorem swapn_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeSwapn) :
    ((swapn ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  have failure := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeSwapn .outOfGas).mpr
    ⟨short, rfl⟩
  change pure (Except.ok (swapnLinear ctx f, w)) = _
  rw [swapnLinear_eq]
  simp only [swapnModel, failure]

/-- An invalid paid immediate halts before checking stack depth. -/
theorem swapn_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((swapn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn } }
        .invalidParameter, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  change pure (Except.ok (swapnLinear ctx f, w)) = _
  rw [swapnLinear_eq]
  simp only [swapnModel, chargeGas_of_le _ _ enough, decoded]

/-- A valid paid immediate with insufficient depth retains the paid frame. -/
theorem swapn_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (short : f.stack.size ≤ depth) :
    ((swapn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn } }
        .stackUnderflow, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  change pure (Except.ok (swapnLinear ctx f, w)) = _
  rw [swapnLinear_eq]
  simp only [swapnModel, chargeGas_of_le _ _ enough, decoded]
  change pure (Except.ok (swapReference 0 depth ctx (debit ctx.config.costs.opcodeSwapn f), w)) = _
  rw [swap_reference_underflow 0 depth ctx (debit ctx.config.costs.opcodeSwapn f) (Or.inr short)]
  rfl

/-- The actual Core swap and the two entry words determine the paid successor. -/
theorem swapn_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (within : depth < f.stack.size) :
    ∃ (stack : Stack) (a b : U256), f.stack.swap? 0 depth = some stack ∧
      f.stack.toList[0]? = some a ∧ f.stack.toList[depth]? = some b ∧
      stack.toList = (f.stack.toList.set 0 b).set depth a ∧
      ((swapn ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn }
          pc := f.pc + 2, stack }, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  have leftWithin : 0 < f.stack.size := by omega
  obtain ⟨stack, a, b, swapped, cellA, cellB, model, result⟩ :=
    swap_reference_success 0 depth ctx (debit ctx.config.costs.opcodeSwapn f) leftWithin within
  refine ⟨stack, a, b, swapped, cellA, cellB, model, ?_⟩
  change pure (Except.ok (swapnLinear ctx f, w)) = _
  rw [swapnLinear_eq]
  simp only [swapnModel, chargeGas_of_le _ _ enough, decoded]
  change pure (Except.ok (swapReference 0 depth ctx (debit ctx.config.costs.opcodeSwapn f), w)) = _
  rw [result]
  rfl

/-- A continuing Id run loses exactly the selected SWAPN price. -/
theorem swapn_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((swapn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSwapn = f.gasMeter.phi := by
  change Except.ok (swapnLinear ctx f, w) = .ok (.continue f', w') at ran
  have step := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [swapnLinear_eq] at step
  cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeSwapn with
  | error e =>
    simp only [swapnModel, paid] at step
    contradiction
  | ok meter =>
    cases decoded : decodeSingle (readImmediate ctx.code f.pc) with
    | error e =>
      simp only [swapnModel, paid, decoded] at step
      contradiction
    | ok decodedValue =>
      simp only [swapnModel, paid, decoded] at step
      rw [swap_reference_continued_meter _ _ _ _ _ step]
      exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeSwapn meter paid

/-- A positive SWAPN price gives strict progress on continuation. -/
theorem swapn_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((swapn ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeSwapn) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := swapn_continue_phi ctx f f' w w' ran
  omega

/-- Charge, decode one padded byte at the Q91 Nat offset, and swap the two decoded indices.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:281–314`. -/
def exchange {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (exchangeLinear ctx f)

/-- Gas shortage retains the entry frame and world before reading the immediate. -/
theorem exchange_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeExchange) :
    ((exchange ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  have failure := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeExchange .outOfGas).mpr
    ⟨short, rfl⟩
  change pure (Except.ok (exchangeLinear ctx f, w)) = _
  rw [exchangeLinear_eq]
  simp only [exchangeModel, failure]

/-- An invalid paid immediate halts before checking stack depth. -/
theorem exchange_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((exchange ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange } }
        .invalidParameter, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  change pure (Except.ok (exchangeLinear ctx f, w)) = _
  rw [exchangeLinear_eq]
  simp only [exchangeModel, chargeGas_of_le _ _ enough, decoded]

/-- A valid paid immediate with insufficient depth retains the paid frame. -/
theorem exchange_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .ok (i, j))
    (short : f.stack.size ≤ j) :
    ((exchange ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange } }
        .stackUnderflow, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  change pure (Except.ok (exchangeLinear ctx f, w)) = _
  rw [exchangeLinear_eq]
  simp only [exchangeModel, chargeGas_of_le _ _ enough, decoded]
  change pure (Except.ok (swapReference i j ctx (debit ctx.config.costs.opcodeExchange f), w)) = _
  rw [swap_reference_underflow i j ctx (debit ctx.config.costs.opcodeExchange f) (Or.inr short)]
  rfl

/-- The actual Core swap and the two entry words determine the paid successor. -/
theorem exchange_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .ok (i, j))
    (within : j < f.stack.size) :
    ∃ (stack : Stack) (a b : U256), f.stack.swap? i j = some stack ∧
      f.stack.toList[i]? = some a ∧ f.stack.toList[j]? = some b ∧
      stack.toList = (f.stack.toList.set i b).set j a ∧
      ((exchange ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange }
          pc := f.pc + 2, stack }, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  have bounds := decodePair_bounds _ _ _ decoded
  have leftWithin : i < f.stack.size := by omega
  obtain ⟨stack, a, b, swapped, cellA, cellB, model, result⟩ :=
    swap_reference_success i j ctx (debit ctx.config.costs.opcodeExchange f) leftWithin within
  refine ⟨stack, a, b, swapped, cellA, cellB, model, ?_⟩
  change pure (Except.ok (exchangeLinear ctx f, w)) = _
  rw [exchangeLinear_eq]
  simp only [exchangeModel, chargeGas_of_le _ _ enough, decoded]
  change pure (Except.ok (swapReference i j ctx (debit ctx.config.costs.opcodeExchange f), w)) = _
  rw [result]
  rfl

/-- A continuing Id run loses exactly the selected EXCHANGE price. -/
theorem exchange_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((exchange ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeExchange = f.gasMeter.phi := by
  change Except.ok (exchangeLinear ctx f, w) = .ok (.continue f', w') at ran
  have step := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [exchangeLinear_eq] at step
  cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeExchange with
  | error e =>
    simp only [exchangeModel, paid] at step
    contradiction
  | ok meter =>
    cases decoded : decodePair (readImmediate ctx.code f.pc) with
    | error e =>
      simp only [exchangeModel, paid, decoded] at step
      contradiction
    | ok decodedValue =>
      rcases decodedValue with ⟨i, j⟩
      simp only [exchangeModel, paid, decoded] at step
      rw [swap_reference_continued_meter _ _ _ _ _ step]
      exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeExchange meter paid

/-- A positive EXCHANGE price gives strict progress on continuation. -/
theorem exchange_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((exchange ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeExchange) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := exchange_continue_phi ctx f f' w w' ran
  omega

end STFSpec.Vm.Instructions
