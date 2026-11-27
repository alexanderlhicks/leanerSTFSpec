/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Instructions.Handler

/-!
# LOG0 through LOG4

Library `EthVmInstructions`. Pop the memory window and topics, pay and expand,
then check that the context permits a log.
See `STFSpec/informal/modules/EthVmInstructions.md`.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def topicOfWord (word : U256) : Hash32 := Hash32.ofBytes32 word.toBeBytes32

private def popLogWordReference (stack : Stack) : Except Stack (U256 × Stack) :=
  match stack.pop with
  | .error _ => .error stack
  | .ok wordAndRest => .ok wordAndRest

private theorem no_nonempty_pop_error (stack : Stack) (nonempty : stack.size ≠ 0)
    (error : ExceptionalHalt) (failed : stack.pop = .error error) : False := by
  have model := ((Stack.pop_eq_error_iff stack error).mp failed).1
  apply nonempty
  rw [Stack.size_eq_length_toList, model]
  rfl

private def popLogWord (stack : Stack) : Except Stack (U256 × Stack) :=
  if empty : stack.size = 0 then
    .error stack
  else
    match popped : stack.pop with
    | .error error => False.elim (no_nonempty_pop_error stack empty error popped)
    | .ok wordAndRest => .ok wordAndRest

private theorem popLogWord_eq_reference (stack : Stack) :
    popLogWord stack = popLogWordReference stack := by
  unfold popLogWord popLogWordReference
  by_cases empty : stack.size = 0
  · have failed := (Stack.pop_eq_error_iff stack .stackUnderflow).mpr
      ⟨List.length_eq_zero_iff.mp (by rwa [← Stack.size_eq_length_toList]), rfl⟩
    simp only [dite_eq_left empty, failed]
  · simp only [dite_eq_right empty]
    split
    · rename_i error failed
      exact False.elim (no_nonempty_pop_error stack empty error failed)
    · rename_i wordAndRest popped
      rw [popped]

private def popTopics : Nat → Stack → Except Stack (List Hash32 × Stack)
  | 0, stack => .ok ([], stack)
  | count + 1, stack =>
    match popLogWord stack with
    | .error residual => .error residual
    | .ok (word, rest) =>
      let topic := topicOfWord word
      match popTopics count rest with
      | .error residual => .error residual
      | .ok (topics, residual) => .ok (topic :: topics, residual)

private structure LogOperands where
  offset : U256
  size : U256
  topics : List Hash32

private def popOperands (count : Nat) (stack : Stack) : Except Stack (LogOperands × Stack) :=
  match popLogWord stack with
  | .error residual => .error residual
  | .ok (offset, rest) =>
    match popLogWord rest with
    | .error residual => .error residual
    | .ok (size, rest) =>
      match popTopics count rest with
      | .error residual => .error residual
      | .ok (topics, residual) => .ok (⟨offset, size, topics⟩, residual)

private def logPrice (cfg : VmConfig) (count : Nat) (size : U256) (memoryCost : Nat) : Nat :=
  cfg.costs.opcodeLogBase + cfg.costs.opcodeLogDataPerByte * size.toNat +
    cfg.costs.opcodeLogTopic * count + memoryCost

private theorem expanded_window (cfg : VmConfig) (memory : Memory) (offset size : U256) :
    let quote := calculateGasExtendMemory cfg memory [(offset, size)]
    let expanded := memory.expand quote.expandBy
      (calculateGasExtendMemory_aligned cfg memory [(offset, size)])
    size.toNat = 0 ∨ offset.toNat + size.toNat ≤ expanded.size := by
  dsimp only
  let quote := calculateGasExtendMemory cfg memory [(offset, size)]
  have sizeAfter : (memory.expand quote.expandBy
      (calculateGasExtendMemory_aligned cfg memory [(offset, size)])).size =
      memory.size + quote.expandBy := by
    rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append,
      List.length_replicate, Memory.length_toBytes]
  rw [sizeAfter]
  exact calculateGasExtendMemory_covers cfg memory [(offset, size)] offset size (by simp)

private def finishLogReference (ctx : FrameCtx) (entry : Frame) (operands : LogOperands)
    (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.offset.toNat + operands.size.toNat ≤ (entry.memory.expand extent aligned).size) :
    StepResult ctx :=
  let memory := entry.memory.expand extent aligned
  let expanded := { entry with gasMeter := paid, memory }
  if ctx.isStatic then
    .halt expanded .writeInStaticContext
  else
    let data := memory.readBytes operands.offset.toNat operands.size.toNat covered
    let log : Log := ⟨ctx.currentTarget, operands.topics.toArray, data⟩
    .continue { expanded with pc := entry.pc + 1, logs := entry.logs.append (.leaf [log]) }

private def finishLog (ctx : FrameCtx) (entry : Frame) (operands : LogOperands)
    (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.offset.toNat + operands.size.toNat ≤ (entry.memory.expand extent aligned).size) :
    StepResult ctx :=
  match entry with
  | ⟨pc, stack, initial, _, logs, deleted, ret, addresses, slots⟩ =>
    let memory := initial.expand extent aligned
    if ctx.isStatic then
      .halt ⟨pc, stack, memory, paid, logs, deleted, ret, addresses, slots⟩ .writeInStaticContext
    else
      let data := memory.readBytes operands.offset.toNat operands.size.toNat covered
      let log : Log := ⟨ctx.currentTarget, operands.topics.toArray, data⟩
      .continue ⟨pc + 1, stack, memory, paid, logs.append (.leaf [log]),
        deleted, ret, addresses, slots⟩

private theorem finishLog_eq_reference (ctx : FrameCtx) (entry : Frame) (operands : LogOperands)
    (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : operands.size.toNat = 0 ∨
      operands.offset.toNat + operands.size.toNat ≤ (entry.memory.expand extent aligned).size) :
    finishLog ctx entry operands paid extent aligned covered =
      finishLogReference ctx entry operands paid extent aligned covered := by
  cases entry
  rfl

private def runLog (count : Nat) (ctx : FrameCtx) (entry : Frame) : StepResult ctx :=
  match popOperands count entry.stack with
  | .error stack => .halt { entry with stack } .stackUnderflow
  | .ok (operands, stack) =>
    let popped := { entry with stack }
    let quote := calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]
    match chargeGas entry.gasMeter (logPrice ctx.config count operands.size quote.cost) with
    | .error error => .halt popped error
    | .ok paid =>
      finishLog ctx popped operands paid quote.expandBy
        (calculateGasExtendMemory_aligned ctx.config entry.memory [(operands.offset, operands.size)])
        (expanded_window ctx.config entry.memory operands.offset operands.size)

/-- Append one log with `n` topics after paying and expanding memory.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/log.py:28–86`. -/
def logN {m : Type → Type} [Monad m] (n : Fin 5) : Handler m :=
  fun ctx entry ↦ pure (runLog n.val ctx entry)

private theorem popTopics_model (count : Nat) (stack : Stack) :
    match popTopics count stack with
    | .error residual => stack.toList.length < count ∧ residual.toList = []
    | .ok (topics, residual) => ∃ words : List U256, words.length = count ∧
        stack.toList = words ++ residual.toList ∧ topics = words.map topicOfWord := by
  induction count generalizing stack with
  | zero =>
    exact ⟨[], rfl, rfl, rfl⟩
  | succ n ih =>
    cases first : stack.pop with
    | error e =>
      have empty := ((Stack.pop_eq_error_iff stack e).mp first).1
      simp only [popTopics, popLogWord_eq_reference, popLogWordReference, first, empty, List.length_nil]
      exact ⟨Nat.zero_lt_succ _, True.intro⟩
    | ok split =>
      obtain ⟨word, rest⟩ := split
      have whole := (Stack.pop_eq_ok_iff stack rest word).mp first
      have suffix := ih rest
      cases next : popTopics n rest with
      | error residual =>
        rw [next] at suffix
        simp only [popTopics, popLogWord_eq_reference, popLogWordReference, first, next, whole, List.length_cons]
        exact ⟨Nat.succ_lt_succ suffix.1, suffix.2⟩
      | ok split =>
        obtain ⟨topics, residual⟩ := split
        rw [next] at suffix
        obtain ⟨words, width, consumed, ordered⟩ := suffix
        simp only [popTopics, popLogWord_eq_reference, popLogWordReference, first, next, whole]
        exact ⟨word :: words, congrArg Nat.succ width,
          congrArg (List.cons word) consumed, congrArg (List.cons (topicOfWord word)) ordered⟩

private theorem popOperands_model (count : Nat) (stack : Stack) :
    match popOperands count stack with
    | .error residual => stack.toList.length < 2 + count ∧ residual.toList = []
    | .ok (operands, residual) => ∃ words : List U256, words.length = count ∧
        stack.toList = operands.offset :: operands.size :: (words ++ residual.toList) ∧
        operands.topics.map Hash32.toBytes32 = words.map U256.toBeBytes32 := by
  simp only [popOperands, popLogWord_eq_reference, popLogWordReference]
  cases offset : stack.pop with
  | error e =>
    have empty := ((Stack.pop_eq_error_iff stack e).mp offset).1
    simpa only [empty, List.length_nil] using
      And.intro (show 0 < 2 + count by omega) (show ([] : List U256) = [] by rfl)
  | ok split =>
    obtain ⟨start, rest⟩ := split
    have withOffset := (Stack.pop_eq_ok_iff stack rest start).mp offset
    cases width : rest.pop with
    | error e =>
      have empty := ((Stack.pop_eq_error_iff rest e).mp width).1
      simp only [width, withOffset, empty, List.length_cons, List.length_nil]
      exact ⟨by omega, True.intro⟩
    | ok split =>
      obtain ⟨size, suffix⟩ := split
      have withSize := (Stack.pop_eq_ok_iff rest suffix size).mp width
      have model := popTopics_model count suffix
      cases topics : popTopics count suffix with
      | error residual =>
        rw [topics] at model
        simp only [width, topics, withOffset, withSize, List.length_cons]
        exact ⟨by have short := model.1; omega, model.2⟩
      | ok split =>
        obtain ⟨logs, residual⟩ := split
        rw [topics] at model
        obtain ⟨words, length, consumed, ordered⟩ := model
        simp only [width, topics]
        refine ⟨words, length, ?_, ?_⟩
        · rw [withOffset, withSize, consumed]
        · rw [ordered, List.map_map]
          apply List.map_congr_left
          intro word _
          exact Hash32.toBytes32_ofBytes32 word.toBeBytes32

private theorem logN_underflow {m : Type → Type} [Monad m] (n : Fin 5)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (short : entry.stack.toList.length < 2 + n.val) :
    ∃ residual : Stack, residual.toList = [] ∧
      ((logN n ctx entry).run world).run =
        pure (.ok (.halt { entry with stack := residual } .stackUnderflow, world)) := by
  have model := popOperands_model n.val entry.stack
  cases parsed : popOperands n.val entry.stack with
  | error residual =>
    rw [parsed] at model
    exact ⟨residual, model.2, by simp only [logN, runLog, parsed]; rfl⟩
  | ok split =>
    obtain ⟨operands, residual⟩ := split
    rw [parsed] at model
    obtain ⟨words, length, consumed, _⟩ := model
    simp only [consumed, List.length_cons, List.length_append, length] at short
    omega

private theorem logN_denied {m : Type → Type} [Monad m] (n : Fin 5)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (operands : LogOperands) (stack : Stack)
    (parsed : popOperands n.val entry.stack = .ok (operands, stack))
    (short : entry.gasMeter.gasLeft <
      logPrice ctx.config n.val operands.size
        (calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]).cost) :
    ((logN n ctx entry).run world).run =
      pure (.ok (.halt { entry with stack } .outOfGas, world)) := by
  have denied := (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩
  simp only [logN, runLog, parsed, denied]
  rfl

private theorem logN_paid_static {m : Type → Type} [Monad m] (n : Fin 5)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (operands : LogOperands) (stack : Stack)
    (parsed : popOperands n.val entry.stack = .ok (operands, stack))
    (static : ctx.isStatic = true) :
    let windows := [(operands.offset, operands.size)]
    let quote := calculateGasExtendMemory ctx.config entry.memory windows
    let price := logPrice ctx.config n.val operands.size quote.cost
    let expanded := entry.memory.expand quote.expandBy
      (calculateGasExtendMemory_aligned ctx.config entry.memory windows)
    price ≤ entry.gasMeter.gasLeft →
      ((logN n ctx entry).run world).run = pure (.ok (.halt
        { entry with stack, memory := expanded, gasMeter.gasLeft := entry.gasMeter.gasLeft - price }
        .writeInStaticContext, world)) := by
  dsimp only
  intro payable
  simp only [logN, runLog, parsed, chargeGas_of_le _ _ payable, finishLog_eq_reference, finishLogReference, static, ite_true]
  rfl

private theorem logN_paid_success {m : Type → Type} [Monad m] (n : Fin 5)
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (operands : LogOperands) (stack : Stack)
    (parsed : popOperands n.val entry.stack = .ok (operands, stack))
    (normal : ctx.isStatic = false) :
    let windows := [(operands.offset, operands.size)]
    let quote := calculateGasExtendMemory ctx.config entry.memory windows
    let price := logPrice ctx.config n.val operands.size quote.cost
    let expanded := entry.memory.expand quote.expandBy
      (calculateGasExtendMemory_aligned ctx.config entry.memory windows)
    price ≤ entry.gasMeter.gasLeft →
      ∃ log : Log, log.address = ctx.currentTarget ∧ log.topics.toList = operands.topics ∧
        log.data.toList = List.take operands.size.toNat
          (List.drop operands.offset.toNat (entry.memory.toBytes ++ List.replicate quote.expandBy 0)) ∧
        (entry.logs.append (.leaf [log])).toList = entry.logs.toList ++ [log] ∧
        ((logN n ctx entry).run world).run = pure (.ok (.continue
          { entry with
            stack
            memory := expanded
            gasMeter := { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price }
            pc := entry.pc + 1
            logs := entry.logs.append (.leaf [log]) }, world)) := by
  dsimp only
  intro payable
  let quote := calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]
  let memory := entry.memory.expand quote.expandBy
    (calculateGasExtendMemory_aligned ctx.config entry.memory [(operands.offset, operands.size)])
  let data := memory.readBytes operands.offset.toNat operands.size.toNat
    (expanded_window ctx.config entry.memory operands.offset operands.size)
  refine ⟨⟨ctx.currentTarget, operands.topics.toArray, data⟩, rfl, by simp, ?_, ?_, ?_⟩
  · exact (Memory.readBytes_toList memory operands.offset.toNat operands.size.toNat
      (expanded_window ctx.config entry.memory operands.offset operands.size)).trans
      (by rw [Memory.toBytes_expand])
  · simp only [LogRope.toList_append, LogRope.toList_leaf]
  · simp only [logN, runLog, parsed, chargeGas_of_le _ _ payable, finishLog_eq_reference, finishLogReference, normal,
      Bool.false_eq_true, ite_false]
    rfl

private theorem logN_continue_phi (n : Fin 5) (ctx : FrameCtx) (entry next : Frame)
    (world world' : VmWorld Id)
    (ran : ((logN n ctx entry).run world).run = .ok (.continue next, world')) :
    ∃ operands : LogOperands, ∃ stack : Stack,
      popOperands n.val entry.stack = .ok (operands, stack) ∧
      next.gasMeter.phi +
        logPrice ctx.config n.val operands.size
          (calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]).cost =
        entry.gasMeter.phi := by
  change Except.ok (runLog n.val ctx entry, world) = _ at ran
  have step := (Prod.mk.inj (Except.ok.inj ran)).1
  cases parsed : popOperands n.val entry.stack with
  | error residual =>
    simp only [runLog, parsed] at step
    contradiction
  | ok split =>
    obtain ⟨operands, stack⟩ := split
    cases charged : chargeGas entry.gasMeter
        (logPrice ctx.config n.val operands.size
          (calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]).cost) with
    | error e =>
      simp only [runLog, parsed, charged] at step
      contradiction
    | ok paid =>
      simp only [runLog, parsed, charged] at step
      rw [finishLog_eq_reference] at step
      by_cases static : ctx.isStatic = true
      · simp only [finishLogReference, static, ite_true] at step
        contradiction
      · simp only [finishLogReference, static] at step
        have frame := StepResult.continue.inj step
        subst next
        exact ⟨operands, stack, rfl, chargeGas_phi _ _ paid charged⟩

private theorem logN_positive (n : Fin 5) (ctx : FrameCtx) (entry next : Frame)
    (world world' : VmWorld Id)
    (ran : ((logN n ctx entry).run world).run = .ok (.continue next, world'))
    (positive : ∀ operands : LogOperands, ∀ stack : Stack,
      popOperands n.val entry.stack = .ok (operands, stack) →
      1 ≤ logPrice ctx.config n.val operands.size
        (calculateGasExtendMemory ctx.config entry.memory [(operands.offset, operands.size)]).cost) :
    next.gasMeter.phi + 1 ≤ entry.gasMeter.phi := by
  obtain ⟨operands, stack, parsed, equation⟩ := logN_continue_phi n ctx entry next world world' ran
  have grows := positive operands stack parsed
  omega

end STFSpec.Vm.Instructions
