/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Vm.Core.StackDecoders

/-!
# Fixed and immediate stack duplication

Library `EthVmInstructions`. DUP charges before reading the stack.
DUPN charges before reading and decoding the padded immediate.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def pushCopied (advance index : Nat) (ctx : FrameCtx) (paid : Frame) : StepResult ctx :=
  match paid.stack.peek? index with
  | none => .halt paid .stackUnderflow
  | some word =>
    match paid.stack.push word with
    | .error error => .halt paid error
    | .ok stack => .continue { paid with pc := paid.pc + advance, stack }

private theorem peek_none_of_short (stack : Stack) (index : Nat)
    (short : stack.size ≤ index) : stack.peek? index = none := by
  rw [Stack.peek?_eq_getElem?, List.getElem?_eq_none]
  simpa only [← Stack.size_eq_length_toList] using short

private theorem peek_none_contradicts_bound (stack : Stack) (index : Nat)
    (fits : index < stack.size) (empty : stack.peek? index = none) : False := by
  have within : index < stack.toList.length := by
    rwa [← Stack.size_eq_length_toList]
  rw [Stack.peek?_eq_getElem?, List.getElem?_eq_getElem within] at empty
  contradiction

private theorem not_full_push (stack : Stack) (word : U256) (error : ExceptionalHalt)
    (space : stack.size ≠ 1024) (failed : stack.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff stack word error).mp failed).1

private def pushCopiedLinear (advance index : Nat) (ctx : FrameCtx) (paid : Frame) : StepResult ctx :=
  if fits : index < paid.stack.size then
    if full : paid.stack.size = 1024 then
      .halt paid .stackOverflow
    else
      match read : paid.stack.peek? index with
      | none => False.elim (peek_none_contradicts_bound paid.stack index fits read)
      | some word =>
        match pushed : paid.stack.push word with
        | .error error => False.elim (not_full_push paid.stack word error full pushed)
        | .ok stack => .continue { paid with pc := paid.pc + advance, stack }
  else
    .halt paid .stackUnderflow

private theorem pushCopiedLinear_eq (advance index : Nat) (ctx : FrameCtx) (paid : Frame) :
    pushCopiedLinear advance index ctx paid = pushCopied advance index ctx paid := by
  unfold pushCopiedLinear pushCopied
  by_cases fits : index < paid.stack.size
  · simp only [dite_eq_left fits]
    by_cases full : paid.stack.size = 1024
    · simp only [dite_eq_left full]
      cases read : paid.stack.peek? index with
      | none => exact False.elim (peek_none_contradicts_bound paid.stack index fits read)
      | some word =>
        have rejected := (Stack.push_eq_error_iff paid.stack word .stackOverflow).mpr ⟨full, rfl⟩
        simp only [rejected]
    · simp only [dite_eq_right full]
      split
      · rename_i absent
        exact False.elim (peek_none_contradicts_bound paid.stack index fits absent)
      · rename_i word read
        split
        · rename_i error failed
          exact False.elim (not_full_push paid.stack word error full failed)
        · rename_i stack pushed
          simp only [read, pushed]
  · simp only [dite_eq_right fits, peek_none_of_short paid.stack index (Nat.not_lt.mp fits)]

private def dupModel (ordinal : Fin 16) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeDup with
  | .error error => .halt f error
  | .ok paid => pushCopied 1 ordinal.val ctx { f with gasMeter := paid }

private def dupLinear (ordinal : Fin 16) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeDup with
  | .error error => .halt f error
  | .ok paid => pushCopiedLinear 1 ordinal.val ctx { f with gasMeter := paid }

private theorem dupLinear_eq (ordinal : Fin 16) (ctx : FrameCtx) (f : Frame) :
    dupLinear ordinal ctx f = dupModel ordinal ctx f := by
  unfold dupLinear dupModel
  cases chargeGas f.gasMeter ctx.config.costs.opcodeDup with
  | error => rfl
  | ok => apply pushCopiedLinear_eq

/-- Charge and copy a word at the supplied fixed top-relative index.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:82–107`. -/
def dupN (ordinal : Fin 16) {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (dupLinear ordinal ctx f)

/-- Gas shortage retains the complete entry frame and world. -/
theorem dupN_run_oog (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeDup) :
    ((dupN ordinal ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeDup
    .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (dupLinear ordinal ctx f, w)) = _
  rw [dupLinear_eq]
  simp only [dupModel, denied]

/-- Insufficient depth halts with the paid frame. -/
theorem dupN_run_underflow (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft)
    (short : f.stack.size ≤ ordinal.val) :
    ((dupN ordinal ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup } }
        .stackUnderflow, w)) := by
  have missing := peek_none_of_short f.stack ordinal.val short
  change pure (Except.ok (dupLinear ordinal ctx f, w)) = _
  rw [dupLinear_eq]
  simp only [dupModel, chargeGas_of_le _ _ enough, pushCopied, missing]

/-- An affordable fixed duplication on a full stack retains the paid frame. -/
theorem dupN_run_overflow (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((dupN ordinal ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup } }
        .stackOverflow, w)) := by
  have bound := ordinal.isLt
  have fits : ordinal.val < f.stack.size := by omega
  change pure (Except.ok (dupLinear ordinal ctx f, w)) = _
  rw [dupLinear_eq]
  simp only [dupModel, chargeGas_of_le _ _ enough, pushCopied]
  cases inspected : f.stack.peek? ordinal.val with
  | none => exact False.elim (peek_none_contradicts_bound f.stack _ fits inspected)
  | some word =>
    have rejected := (Stack.push_eq_error_iff f.stack word .stackOverflow).mpr ⟨full, rfl⟩
    simp only [rejected]

/-- The copied word and successful push determine the next frame. -/
theorem dupN_run_success (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft)
    (fits : ordinal.val < f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? ordinal.val = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupN ordinal ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup }
          pc := f.pc + 1, stack }, w)) := by
  cases inspected : f.stack.peek? ordinal.val with
  | none => exact False.elim (peek_none_contradicts_bound f.stack _ fits inspected)
  | some word =>
    cases pushed : f.stack.push word with
    | error error => exact False.elim (not_full_push f.stack word error (Nat.ne_of_lt space) pushed)
    | ok stack =>
      have model := ((Stack.push_eq_ok_iff f.stack stack word).mp pushed).2
      refine ⟨word, stack, rfl, pushed, model, ?_⟩
      change pure (Except.ok (dupLinear ordinal ctx f, w)) = _
      rw [dupLinear_eq]
      simp only [dupModel, chargeGas_of_le _ _ enough, pushCopied, inspected, pushed]

/-- A continuing Id run loses exactly the selected fixed DUP price. -/
theorem dupN_continue_phi (ordinal : Fin 16) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupN ordinal ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDup = f.gasMeter.phi := by
  change Except.ok (dupLinear ordinal ctx f, w) = .ok (.continue f', w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [dupLinear_eq] at result
  cases charged : chargeGas f.gasMeter ctx.config.costs.opcodeDup with
  | error e =>
    simp only [dupModel, charged] at result
    contradiction
  | ok meter =>
    cases entry : f.stack.peek? ordinal.val with
    | none =>
      simp only [dupModel, charged, pushCopied, entry] at result
      contradiction
    | some word =>
      cases pushed : f.stack.push word with
      | error e =>
        simp only [dupModel, charged, pushCopied, entry, pushed] at result
        contradiction
      | ok stack =>
        simp only [dupModel, charged, pushCopied, entry, pushed, StepResult.continue.injEq] at result
        subst f'
        exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeDup meter charged

/-- A positive fixed DUP price gives strict progress on continuation. -/
theorem dupN_continue_progress (ordinal : Fin 16)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupN ordinal ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeDup) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := dupN_continue_phi ordinal ctx f f' w w' ran
  omega

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

private def dupnModel (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeDupn with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodeSingle (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok depth => pushCopied 2 (depth - 1) ctx paid

private def dupnLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeDupn with
  | .error error => .halt f error
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    match decodeSingle (readImmediate ctx.code f.pc) with
    | .error error => .halt paid error
    | .ok depth => pushCopiedLinear 2 (depth - 1) ctx paid

private theorem dupnLinear_eq (ctx : FrameCtx) (f : Frame) :
    dupnLinear ctx f = dupnModel ctx f := by
  unfold dupnLinear dupnModel
  cases chargeGas f.gasMeter ctx.config.costs.opcodeDupn with
  | error => rfl
  | ok =>
    cases decodeSingle (readImmediate ctx.code f.pc) with
    | error => rfl
    | ok => apply pushCopiedLinear_eq

/-- Charge, decode one padded byte at the Q91 Nat offset, and duplicate the selected word.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:213–242`. -/
def dupn {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (dupnLinear ctx f)

/-- Gas shortage halts before reading the immediate. -/
theorem dupn_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeDupn) :
    ((dupn ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeDupn
    .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (dupnLinear ctx f, w)) = _
  rw [dupnLinear_eq]
  simp only [dupnModel, denied]

/-- An invalid paid immediate halts before checking operand depth. -/
theorem dupn_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .invalidParameter, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  change pure (Except.ok (dupnLinear ctx f, w)) = _
  rw [dupnLinear_eq]
  simp only [dupnModel, chargeGas_of_le _ _ enough, decoded]

/-- A valid paid immediate with insufficient depth retains the paid frame. -/
theorem dupn_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (short : f.stack.size < depth) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .stackUnderflow, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  have missing := peek_none_of_short f.stack (depth - 1) (by omega)
  change pure (Except.ok (dupnLinear ctx f, w)) = _
  rw [dupnLinear_eq]
  simp only [dupnModel, chargeGas_of_le _ _ enough, decoded, pushCopied, missing]

/-- A valid paid immediate on a full stack retains the paid frame. -/
theorem dupn_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (full : f.stack.size = 1024) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .stackOverflow, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  have bound := decodeSingle_bounds _ _ decoded
  have fits : depth - 1 < f.stack.size := by omega
  change pure (Except.ok (dupnLinear ctx f, w)) = _
  rw [dupnLinear_eq]
  simp only [dupnModel, chargeGas_of_le _ _ enough, decoded, pushCopied]
  cases inspected : f.stack.peek? (depth - 1) with
  | none => exact False.elim (peek_none_contradicts_bound f.stack _ fits inspected)
  | some word =>
    have rejected := (Stack.push_eq_error_iff f.stack word .stackOverflow).mpr ⟨full, rfl⟩
    simp only [rejected]

/-- A successful paid duplication copies the selected word and advances the PC by two. -/
theorem dupn_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (fits : depth ≤ f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? (depth - 1) = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupn ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn }
          pc := f.pc + 2, stack }, w)) := by
  rw [← readImmediate_eq_getD] at decoded
  have bound := decodeSingle_bounds _ _ decoded
  have indexFits : depth - 1 < f.stack.size := by omega
  cases inspected : f.stack.peek? (depth - 1) with
  | none => exact False.elim (peek_none_contradicts_bound f.stack _ indexFits inspected)
  | some word =>
    cases pushed : f.stack.push word with
    | error error => exact False.elim (not_full_push f.stack word error (Nat.ne_of_lt space) pushed)
    | ok stack =>
      have model := ((Stack.push_eq_ok_iff f.stack stack word).mp pushed).2
      refine ⟨word, stack, rfl, pushed, model, ?_⟩
      change pure (Except.ok (dupnLinear ctx f, w)) = _
      rw [dupnLinear_eq]
      simp only [dupnModel, chargeGas_of_le _ _ enough, decoded, pushCopied, inspected, pushed]

/-- A continuing Id run loses exactly the selected DUPN price. -/
theorem dupn_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDupn = f.gasMeter.phi := by
  change Except.ok (dupnLinear ctx f, w) = .ok (.continue f', w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [dupnLinear_eq] at result
  cases charged : chargeGas f.gasMeter ctx.config.costs.opcodeDupn with
  | error e =>
    simp only [dupnModel, charged] at result
    contradiction
  | ok meter =>
    cases decode : decodeSingle (readImmediate ctx.code f.pc) with
    | error e =>
      simp only [dupnModel, charged, decode] at result
      contradiction
    | ok depth =>
      cases entry : f.stack.peek? (depth - 1) with
      | none =>
        simp only [dupnModel, charged, decode, pushCopied, entry] at result
        contradiction
      | some word =>
        cases pushed : f.stack.push word with
        | error e =>
          simp only [dupnModel, charged, decode, pushCopied, entry, pushed] at result
          contradiction
        | ok stack =>
          simp only [dupnModel, charged, decode, pushCopied, entry, pushed,
            StepResult.continue.injEq] at result
          subst f'
          exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeDupn meter charged

/-- A positive DUPN price gives strict progress on continuation. -/
theorem dupn_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupn ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeDupn) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := dupn_continue_phi ctx f f' w w' ran
  omega

end STFSpec.Vm.Instructions
