/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.AccountDefault
import STFSpec.State.Code
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# EXTCODECOPY

Library `EthVmInstructions`. Charge and expand the destination window
before reading the account and its raw code through State.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private def popWordReference (stack : Stack) : Except Stack (U256 × Stack) :=
  match stack.pop with
  | .error _ => .error stack
  | .ok result => .ok result

private theorem no_nonempty_pop_error (stack : Stack) (nonempty : stack.size ≠ 0)
    (error : ExceptionalHalt) (failed : stack.pop = .error error) : False := by
  have empty := ((Stack.pop_eq_error_iff stack error).mp failed).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

private def popWord (stack : Stack) : Except Stack (U256 × Stack) :=
  if empty : stack.size = 0 then .error stack
  else
    match popped : stack.pop with
    | .error error => False.elim (no_nonempty_pop_error stack empty error popped)
    | .ok result => .ok result

private theorem popWord_eq_reference (stack : Stack) :
    popWord stack = popWordReference stack := by
  unfold popWord popWordReference
  split
  · rename_i empty
    rw [Stack.size_eq_length_toList] at empty
    rw [(Stack.pop_eq_error_iff stack .stackUnderflow).mpr
      ⟨List.length_eq_zero_iff.mp empty, rfl⟩]
  · rename_i nonempty
    split
    · rename_i error failed
      exact False.elim (no_nonempty_pop_error stack nonempty error failed)
    · rename_i result popped
      rw [popped]

private structure CopyOperands where
  address : Address
  memoryStart : U256
  codeStart : U256
  size : U256

private def popOperands (stack : Stack) : Except Stack (CopyOperands × Stack) := do
  let (word, stack) ← popWord stack
  let address := Address.ofU256Masked word
  let (memoryStart, stack) ← popWord stack
  let (codeStart, stack) ← popWord stack
  let (size, stack) ← popWord stack
  pure (⟨address, memoryStart, codeStart, size⟩, stack)

private def warmAndPrice (cfg : VmConfig) (warm : AddrSet) (address : Address) : AddrSet × Nat :=
  if address ∈ warm then (warm, cfg.costs.warmAccess) else
    (warm.insert address, cfg.costs.coldAccountAccess)

private def copyPrice (cfg : VmConfig) (accessPrice : Nat) (size : U256) (memoryPrice : Nat) : Nat :=
  accessPrice + cfg.costs.warmAccess + cfg.costs.opcodeCopyPerWord * (ceil32 size.toNat / 32) +
    memoryPrice

private theorem expanded_window (cfg : VmConfig) (memory : Memory) (dest size : U256) :
    let e := calculateGasExtendMemory cfg memory [(dest, size)]
    let expanded := memory.expand e.expandBy (calculateGasExtendMemory_aligned cfg memory [(dest, size)])
    size.toNat = 0 ∨ dest.toNat + size.toNat ≤ expanded.size := by
  dsimp only
  let e := calculateGasExtendMemory cfg memory [(dest, size)]
  have expandedSize : (memory.expand e.expandBy
      (calculateGasExtendMemory_aligned cfg memory [(dest, size)])).size = memory.size + e.expandBy := by
    rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append, List.length_replicate,
      Memory.length_toBytes]
  rw [expandedSize]
  exact calculateGasExtendMemory_covers cfg memory [(dest, size)] dest size (by simp)

private theorem write_window (memory : Memory) (dest source size : U256) (code : ByteArray)
    (covered : size.toNat = 0 ∨ dest.toNat + size.toNat ≤ memory.size) :
    let value := bufferRead (Bytes.ofByteArray code) source size
    value.size = 0 ∨ dest.toNat + value.size ≤ memory.size := by
  simpa only [bufferRead_size] using covered

private def readCode {m : Type → Type} [Monad m] (address : Address) : VmM m ByteArray := do
  let account ← liftState (getAccount address)
  liftState (getCode account.codeHash)

private def finishReference {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (operands : CopyOperands) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.memoryStart.toNat + operands.size.toNat ≤ (frame.memory.expand extent aligned).size) :
    VmM m (StepResult ctx) :=
  let memory := frame.memory.expand extent aligned
  do
    let code ← readCode operands.address
    let value := bufferRead (Bytes.ofByteArray code) operands.codeStart operands.size
    let written := memory.write operands.memoryStart.toNat value
      (write_window memory operands.memoryStart operands.codeStart operands.size code covered)
    pure (.continue { frame with pc := frame.pc + 1, memory := written })

-- The native Id specialization receives the expanded destination before either State lookup.
@[noinline] private def copyFromState {m : Type → Type} [Monad m] (ctx : FrameCtx)
    (frame : Frame) (operands : CopyOperands)
    (covered : operands.size.toNat = 0 ∨ operands.memoryStart.toNat + operands.size.toNat ≤ frame.memory.size) :
    VmM m (StepResult ctx) :=
  match frame with
  | ⟨pc, stack, memory, meter, logs, deleted, ret, warm, slots⟩ => do
    let code ← readCode operands.address
    let value := bufferRead (Bytes.ofByteArray code) operands.codeStart operands.size
    let written := memory.write operands.memoryStart.toNat value
      (write_window memory operands.memoryStart operands.codeStart operands.size code covered)
    pure (.continue ⟨pc + 1, stack, written, meter, logs, deleted, ret, warm, slots⟩)

private def finishCopy {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (operands : CopyOperands) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.memoryStart.toNat + operands.size.toNat ≤ (frame.memory.expand extent aligned).size) :
    VmM m (StepResult ctx) :=
  match frame with
  | ⟨pc, stack, initial, meter, logs, deleted, ret, warm, slots⟩ =>
    let memory := initial.expand extent aligned
    copyFromState ctx ⟨pc, stack, memory, meter, logs, deleted, ret, warm, slots⟩ operands covered

private theorem finishCopy_eq_reference {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (operands : CopyOperands) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.memoryStart.toNat + operands.size.toNat ≤ (frame.memory.expand extent aligned).size) :
    finishCopy (m := m) ctx frame operands extent aligned covered =
      finishReference ctx frame operands extent aligned covered := by
  cases frame
  rfl

private def copyAfterPops {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (operands : CopyOperands) : VmM m (StepResult ctx) :=
  let windows := [(operands.memoryStart, operands.size)]
  let quote := calculateGasExtendMemory ctx.config frame.memory windows
  let (warm, accessPrice) := warmAndPrice ctx.config frame.accessedAddresses operands.address
  let price := copyPrice ctx.config accessPrice operands.size quote.cost
  let accessed := { frame with accessedAddresses := warm }
  match chargeGas frame.gasMeter price with
  | .error error => pure (.halt accessed error)
  | .ok paid =>
    finishCopy ctx { accessed with gasMeter := paid } operands quote.expandBy
      (calculateGasExtendMemory_aligned ctx.config frame.memory windows)
      (expanded_window ctx.config frame.memory operands.memoryStart operands.size)

private def extcodecopyReference {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  match popOperands frame.stack with
  | .error stack => pure (.halt { frame with stack } .stackUnderflow)
  | .ok (operands, stack) => copyAfterPops ctx { frame with stack } operands

/-- Copy the padded raw code window after charging and expanding memory.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:364–405`. -/
def extcodecopy {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  match frame with
  | ⟨pc, stack, memory, meter, logs, deleted, ret, warm, slots⟩ =>
    match popOperands stack with
    | .error residual => pure (.halt ⟨pc, residual, memory, meter, logs, deleted, ret, warm, slots⟩ .stackUnderflow)
    | .ok (operands, residual) =>
      copyAfterPops ctx ⟨pc, residual, memory, meter, logs, deleted, ret, warm, slots⟩ operands

private theorem extcodecopy_eq_reference {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame) :
    extcodecopy (m := m) ctx frame = extcodecopyReference ctx frame := by
  cases frame
  rfl

private theorem first_underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (world : VmWorld m) (first : frame.stack.pop = .error .stackUnderflow) :
    ((extcodecopy ctx frame).run world).run = pure (.ok (.halt frame .stackUnderflow, world)) := by
  simp only [extcodecopy_eq_reference, extcodecopyReference, popOperands, popWord_eq_reference,
    popWordReference, first, Bind.bind, Except.bind]
  rfl

private theorem second_underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (world : VmWorld m) (word : U256) (firstTail : Stack)
    (first : frame.stack.pop = .ok (word, firstTail))
    (second : firstTail.pop = .error .stackUnderflow) :
    ((extcodecopy ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := firstTail } .stackUnderflow, world)) := by
  simp only [extcodecopy_eq_reference, extcodecopyReference, popOperands, popWord_eq_reference,
    popWordReference, first, second, Bind.bind, Except.bind]
  rfl

private theorem third_underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (world : VmWorld m) (word dest : U256) (firstTail secondTail : Stack)
    (first : frame.stack.pop = .ok (word, firstTail))
    (second : firstTail.pop = .ok (dest, secondTail))
    (third : secondTail.pop = .error .stackUnderflow) :
    ((extcodecopy ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := secondTail } .stackUnderflow, world)) := by
  simp only [extcodecopy_eq_reference, extcodecopyReference, popOperands, popWord_eq_reference,
    popWordReference, first, second, third, Bind.bind, Except.bind]
  rfl

private theorem fourth_underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (world : VmWorld m) (word dest source : U256) (firstTail secondTail thirdTail : Stack)
    (first : frame.stack.pop = .ok (word, firstTail))
    (second : firstTail.pop = .ok (dest, secondTail))
    (third : secondTail.pop = .ok (source, thirdTail))
    (fourth : thirdTail.pop = .error .stackUnderflow) :
    ((extcodecopy ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := thirdTail } .stackUnderflow, world)) := by
  simp only [extcodecopy_eq_reference, extcodecopyReference, popOperands, popWord_eq_reference,
    popWordReference, first, second, third, fourth, Bind.bind, Except.bind]
  rfl

private theorem operands_of_pops (stack firstTail secondTail thirdTail residual : Stack)
    (word dest source size : U256)
    (first : stack.pop = .ok (word, firstTail))
    (second : firstTail.pop = .ok (dest, secondTail))
    (third : secondTail.pop = .ok (source, thirdTail))
    (fourth : thirdTail.pop = .ok (size, residual)) :
    popOperands stack = .ok (⟨Address.ofU256Masked word, dest, source, size⟩, residual) := by
  simp only [popOperands, popWord_eq_reference, popWordReference, first, second, third, fourth,
    Bind.bind, Except.bind]
  rfl

private theorem warm_selection (ctx : FrameCtx) (warm : AddrSet) (address : Address)
    (present : address ∈ warm) :
    warmAndPrice ctx.config warm address = (warm, ctx.config.costs.warmAccess) := by
  simp only [warmAndPrice, ite_eq_left present]

private theorem cold_selection (ctx : FrameCtx) (warm : AddrSet) (address : Address)
    (absent : address ∉ warm) :
    warmAndPrice ctx.config warm address = (warm.insert address, ctx.config.costs.coldAccountAccess) := by
  simp only [warmAndPrice, ite_eq_right absent]

private theorem extcodecopy_denied {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (world : VmWorld m) (operands : CopyOperands) (stack : Stack)
    (parsed : popOperands frame.stack = .ok (operands, stack)) :
    let paths := [(operands.memoryStart, operands.size)]
    let e := calculateGasExtendMemory ctx.config frame.memory paths
    let (warm, accessPrice) := warmAndPrice ctx.config frame.accessedAddresses operands.address
    frame.gasMeter.gasLeft < copyPrice ctx.config accessPrice operands.size e.cost →
    ((extcodecopy ctx frame).run world).run =
      pure (.ok (.halt { frame with stack, accessedAddresses := warm } .outOfGas, world)) := by
  dsimp only
  generalize selected : warmAndPrice ctx.config frame.accessedAddresses operands.address = access
  obtain ⟨warm, accessPrice⟩ := access
  intro short
  have denied := (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩
  simp only [extcodecopy_eq_reference, extcodecopyReference, parsed, copyAfterPops, selected, denied]
  rfl

private theorem extcodecopy_paid {m : Type → Type} [Monad m] (ctx : FrameCtx) (frame : Frame)
    (operands : CopyOperands) (stack : Stack) (paid : GasMeter)
    (parsed : popOperands frame.stack = .ok (operands, stack)) :
    let paths := [(operands.memoryStart, operands.size)]
    let e := calculateGasExtendMemory ctx.config frame.memory paths
    let (warm, accessPrice) := warmAndPrice ctx.config frame.accessedAddresses operands.address
    chargeGas frame.gasMeter (copyPrice ctx.config accessPrice operands.size e.cost) = .ok paid →
    extcodecopy (m := m) ctx frame = finishReference ctx
      { frame with stack, accessedAddresses := warm, gasMeter := paid } operands e.expandBy
      (calculateGasExtendMemory_aligned ctx.config frame.memory paths)
      (expanded_window ctx.config frame.memory operands.memoryStart operands.size) := by
  dsimp only
  generalize selected : warmAndPrice ctx.config frame.accessedAddresses operands.address = access
  obtain ⟨warm, accessPrice⟩ := access
  intro charged
  simp only [extcodecopy_eq_reference, extcodecopyReference, parsed, copyAfterPops, selected, charged,
    finishCopy_eq_reference]
  rw [selected]

private theorem paid_id (ctx : FrameCtx) (frame : Frame) (world : VmWorld Id)
    (operands : CopyOperands) (stack : Stack) (paid : GasMeter)
    (parsed : popOperands frame.stack = .ok (operands, stack)) :
    let paths := [(operands.memoryStart, operands.size)]
    let e := calculateGasExtendMemory ctx.config frame.memory paths
    let (warm, accessPrice) := warmAndPrice ctx.config frame.accessedAddresses operands.address
    let memory := frame.memory.expand e.expandBy
      (calculateGasExtendMemory_aligned ctx.config frame.memory paths)
    let covered := expanded_window ctx.config frame.memory operands.memoryStart operands.size
    chargeGas frame.gasMeter (copyPrice ctx.config accessPrice operands.size e.cost) = .ok paid →
    ((extcodecopy ctx frame).run world).run =
      match ((getAccount operands.address).run world.tx).run with
      | .error error => .error (.state error)
      | .ok (account, afterAccount) =>
        match ((getCode account.codeHash).run afterAccount).run with
        | .error error => .error (.state error)
        | .ok (code, afterCode) =>
          let value := bufferRead (Bytes.ofByteArray code) operands.codeStart operands.size
          let written := memory.write operands.memoryStart.toNat value
            (write_window memory operands.memoryStart operands.codeStart operands.size code covered)
          .ok (.continue { frame with
            pc := frame.pc + 1, stack, memory := written, gasMeter := paid, accessedAddresses := warm },
            { world with tx := afterCode }) := by
  dsimp only
  have run := extcodecopy_paid (m := Id) ctx frame operands stack paid parsed
  generalize selected : warmAndPrice ctx.config frame.accessedAddresses operands.address = access at run ⊢
  obtain ⟨warm, accessPrice⟩ := access
  intro charged
  rw [run charged]
  simp only [finishReference, readCode, StateT.run_bind, ExceptT.run_bind, liftState_run]
  cases accountResult : ((getAccount operands.address).run world.tx).run with
  | error _ => rfl
  | ok result =>
    obtain ⟨account, afterAccount⟩ := result
    cases fetched : ((getCode account.codeHash).run afterAccount).run <;>
      simp [Bind.bind, Pure.pure, fetched] <;> rfl

private theorem bytes_after_write (cfg : VmConfig) (memory : Memory) (operands : CopyOperands)
    (code : ByteArray) :
    let paths := [(operands.memoryStart, operands.size)]
    let e := calculateGasExtendMemory cfg memory paths
    let expanded := memory.expand e.expandBy (calculateGasExtendMemory_aligned cfg memory paths)
    let covered := expanded_window cfg memory operands.memoryStart operands.size
    let value := bufferRead (Bytes.ofByteArray code) operands.codeStart operands.size
    let bytes := memory.toBytes ++ List.replicate e.expandBy 0
    (expanded.write operands.memoryStart.toNat value
        (write_window expanded operands.memoryStart operands.codeStart operands.size code covered)).toBytes =
      bytes.take operands.memoryStart.toNat ++ value.toList ++
        bytes.drop (operands.memoryStart.toNat + operands.size.toNat) := by
  dsimp only
  rw [Memory.toBytes_write, Memory.toBytes_expand, bufferRead_size]

private theorem paid_observations (address seen : Address) (account : Account) (code : ByteArray)
    (before afterAccount afterCode : TxState Id) (key : Hash32)
    (readAccount : ((getAccount address).run before).run = .ok (account, afterAccount))
    (readCode : ((getCode account.codeHash).run afterAccount).run = .ok (code, afterCode)) :
    (seen ∈ afterCode.obs.accountReads ↔ seen = address ∨ seen ∈ before.obs.accountReads) ∧
    (key ∈ afterCode.obs.codeReads ↔ key ∈ before.obs.codeReads ∨
      (key = account.codeHash ∧ account.codeHash ≠ before.block.consts.emptyCodeHash ∧
        before.rev.codeWrites[account.codeHash]? = none ∧ before.block.codeWrites[account.codeHash]? = none)) := by
  obtain ⟨_, _, accounts, _, _⟩ := getCode_frames _ _ code _ readCode
  obtain ⟨block, rev, _, codes, _⟩ := getAccount_frames _ _ account _ readAccount
  constructor
  · rw [accounts]
    exact getAccount_mem _ _ _ account _ readAccount
  · rw [getCode_mem _ _ _ code _ readCode, codes, block, rev]

private abbrev selectedPrice (ctx : FrameCtx) (frame : Frame) (operands : CopyOperands) : Nat :=
  copyPrice ctx.config (warmAndPrice ctx.config frame.accessedAddresses operands.address).2 operands.size
    (calculateGasExtendMemory ctx.config frame.memory [(operands.memoryStart, operands.size)]).cost

private theorem continuationPhi (ctx : FrameCtx) (frame next : Frame) (world world' : VmWorld Id)
    (ran : ((extcodecopy ctx frame).run world).run = .ok (.continue next, world')) :
    ∃ (operands : CopyOperands) (stack : Stack), popOperands frame.stack = .ok (operands, stack) ∧
      next.gasMeter.phi + selectedPrice ctx frame operands = frame.gasMeter.phi := by
  cases parsed : popOperands frame.stack with
  | error stack =>
    simp only [extcodecopy_eq_reference, extcodecopyReference, parsed] at ran
    cases (Prod.mk.inj (Except.ok.inj ran)).1
  | ok result =>
    obtain ⟨operands, stack⟩ := result
    cases charged : chargeGas frame.gasMeter (selectedPrice ctx frame operands) with
    | error error =>
      simp only [extcodecopy_eq_reference, extcodecopyReference, parsed, copyAfterPops, charged] at ran
      cases (Prod.mk.inj (Except.ok.inj ran)).1
    | ok paid =>
      have action := paid_id ctx frame world operands stack paid parsed
      unfold selectedPrice at charged ⊢
      dsimp only at action charged ⊢
      generalize chosen : warmAndPrice ctx.config frame.accessedAddresses operands.address = rates at action charged ⊢
      obtain ⟨warm, accessPrice⟩ := rates
      rw [action charged] at ran
      cases accountRead : ((getAccount operands.address).run world.tx).run with
      | error error =>
        rw [accountRead] at ran
        contradiction
      | ok accountStep =>
        obtain ⟨account, afterAccount⟩ := accountStep
        rw [accountRead] at ran
        cases codeRead : ((getCode account.codeHash).run afterAccount).run with
        | error error =>
          simp only [codeRead] at ran
          contradiction
        | ok codeStep =>
          obtain ⟨code, afterCode⟩ := codeStep
          simp only [codeRead] at ran
          have same := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
          subst next
          refine ⟨operands, stack, rfl, ?_⟩
          rw [chosen]
          exact chargeGas_phi _ _ paid charged

private theorem continuationProgress (ctx : FrameCtx) (frame next : Frame) (world world' : VmWorld Id)
    (ran : ((extcodecopy ctx frame).run world).run = .ok (.continue next, world'))
    (positive : ∀ (operands : CopyOperands) (stack : Stack),
      popOperands frame.stack = .ok (operands, stack) → 0 < selectedPrice ctx frame operands) :
    next.gasMeter.phi + 1 ≤ frame.gasMeter.phi := by
  obtain ⟨operands, stack, parsed, spent⟩ := continuationPhi ctx frame next world world' ran
  have nonzero := positive operands stack parsed
  omega

end STFSpec.Vm.Instructions
