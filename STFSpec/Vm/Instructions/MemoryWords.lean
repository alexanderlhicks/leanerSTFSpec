/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Vm.Instructions.Handler
import STFSpec.Vm.Core.MemoryGas

/-!
# Fixed-width memory instructions

Library `EthVmInstructions`. MLOAD, MSTORE and MSTORE8 pop their operands
before charging for the window. Payment precedes the Memory operations.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private abbrev windowPrice (cfg : VmConfig) (m : Memory) (off width : U256) : ExtendMemory :=
  calculateGasExtendMemory cfg m [(off, width)]

private theorem expanded_size (m : Memory) (n : Nat) (aligned : n % 32 = 0) :
    (m.expand n aligned).size = m.size + n := by
  rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append,
    Memory.length_toBytes, List.length_replicate]

private theorem expanded_covers (cfg : VmConfig) (m : Memory) (off width : U256)
    (aligned : (windowPrice cfg m off width).expandBy % 32 = 0) :
    width.toNat = 0 ∨
      off.toNat + width.toNat ≤ (m.expand (windowPrice cfg m off width).expandBy aligned).size := by
  rw [expanded_size]
  exact calculateGasExtendMemory_covers cfg m [(off, width)] off width (by simp)

private theorem expanded_covers_word (cfg : VmConfig) (m : Memory) (off : U256)
    (aligned : (windowPrice cfg m off (U256.ofNat 32)).expandBy % 32 = 0) :
    off.toNat + 32 ≤ (m.expand (windowPrice cfg m off (U256.ofNat 32)).expandBy aligned).size := by
  have within := expanded_covers cfg m off (U256.ofNat 32) aligned
  change 32 = 0 ∨ _ at within
  exact within.resolve_left (by decide)

private theorem read_word_size (m : Memory) (off : U256)
    (within : off.toNat + 32 ≤ m.size) :
    (m.readBytes off.toNat 32 (Or.inr within)).size = 32 := by
  rw [← Bytes.length_toList, Memory.readBytes_toList,
    List.length_take, List.length_drop, Memory.length_toBytes]
  omega

private theorem decoded_word (data : Bytes) (length : data.size = 32) :
    (U256.ofNat (Uint.ofBeBytes data)).toNat = Uint.ofBeBytes data := by
  have bound := Uint.ofBeBytes_lt data
  rw [length] at bound
  rw [U256.toNat_ofNat, Nat.mod_eq_of_lt bound]

private theorem space_after_pop (s tail : Stack) (off : U256) (popped : s.pop = .ok (off, tail)) :
    tail.size < 1024 := by
  have length := congrArg List.length ((Stack.pop_eq_ok_iff s tail off).mp popped)
  rw [List.length_cons, ← Stack.size_eq_length_toList, ← Stack.size_eq_length_toList] at length
  have bound := s.size_le
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
    have frame := (Prod.mk.inj same).2
    rw [← frame]
    exact space_after_pop f.stack tail value observed

private theorem push_failure_impossible (tail : Stack) (word : U256) (room : tail.size < 1024)
    (error : ExceptionalHalt) (failed : tail.push word = .error error) : False :=
  (Nat.ne_of_lt room) ((Stack.push_eq_error_iff tail word error).mp failed).1

private def pushLoaded (tail : Stack) (word : U256) (room : tail.size < 1024) : Stack :=
  match pushed : tail.push word with
  | .error error => False.elim (push_failure_impossible tail word room error pushed)
  | .ok stack => stack

private theorem pushLoaded_actual (tail : Stack) (word : U256) (room : tail.size < 1024) :
    tail.push word = .ok (pushLoaded tail word room) := by
  unfold pushLoaded
  split
  · rename_i error failed
    exact False.elim (push_failure_impossible tail word room error failed)
  · rename_i stack pushed
    exact pushed

private def advanceWithMemory (ctx : FrameCtx) (f : Frame) (meter : GasMeter)
    (update : (stack : Stack) → stack = f.stack →
      (memory : Memory) → memory = f.memory → Stack × Memory) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, ret, addresses, slots⟩ =>
    let (nextStack, nextMemory) := update stack rfl memory rfl
    .continue ⟨pc + 1, nextStack, nextMemory, meter, logs, deleted, ret, addresses, slots⟩

private theorem advanceWithMemory_eq (ctx : FrameCtx) (f : Frame) (meter : GasMeter)
    (update : (stack : Stack) → stack = f.stack →
      (memory : Memory) → memory = f.memory → Stack × Memory) :
    advanceWithMemory ctx f meter update =
      let next := update f.stack rfl f.memory rfl
      .continue { f with pc := f.pc + 1, stack := next.1, memory := next.2, gasMeter := meter } := by
  cases f
  rfl

private def loadUpdate (off : U256) (tail : Stack) (room : tail.size < 1024)
    (extent : Nat) (aligned : extent % 32 = 0)
    (memory : Memory) (fits : off.toNat + 32 ≤ memory.size + extent) : Stack × Memory :=
  let expanded := memory.expand extent aligned
  let bytes := expanded.readBytes off.toNat 32 (Or.inr (by
    rw [expanded_size]
    exact fits))
  (pushLoaded tail (U256.ofNat (Uint.ofBeBytes bytes)) room, expanded)

private def storeUpdate (off : U256) (tail : Stack)
    (extent : Nat) (aligned : extent % 32 = 0) (data : Bytes) (memory : Memory)
    (fits : data.size = 0 ∨ off.toNat + data.size ≤ memory.size + extent) : Stack × Memory :=
  let expanded := memory.expand extent aligned
  let written := expanded.write off.toNat data (by
    rw [expanded_size]
    exact fits)
  (tail, written)

private def mloadAfterPop (ctx : FrameCtx) (f : Frame) (off : U256)
    (room : f.stack.size < 1024) : StepResult ctx :=
  let width := U256.ofNat 32
  let extent := windowPrice ctx.config f.memory off width
  match chargeGas f.gasMeter (ctx.config.costs.opcodeMloadBase + extent.cost) with
  | .error error => .halt f error
  | .ok meter =>
    have fits : off.toNat + 32 ≤ f.memory.size + extent.expandBy :=
      (calculateGasExtendMemory_covers ctx.config f.memory [(off, width)] off width
        (by simp)).resolve_left (by decide)
    advanceWithMemory ctx f meter fun stack sameStack memory sameMemory ↦
      loadUpdate off stack (sameStack.symm ▸ room) extent.expandBy
        (calculateGasExtendMemory_aligned ctx.config f.memory [(off, width)])
        memory (sameMemory.symm ▸ fits)

private def mloadResult (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match popped : popFrame f with
  | .error (residual, error) => .halt residual error
  | .ok (off, residual) => mloadAfterPop ctx residual off (poppedFrame_room f residual off popped)

private theorem mload_result_of_error (ctx : FrameCtx) (f : Frame) (error : ExceptionalHalt)
    (missing : f.stack.pop = .error error) : mloadResult ctx f = .halt f error := by
  have popped : popFrame f = .error (f, error) := by simp [popFrame_eq, popFrameReference, missing]
  unfold mloadResult
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i off tail observed
    rw [popped] at observed
    contradiction

private theorem mload_result_of_pop (ctx : FrameCtx) (f : Frame) (off : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (off, tail)) :
    mloadResult ctx f =
      mloadAfterPop ctx { f with stack := tail } off (space_after_pop f.stack tail off popped) := by
  have framePop : popFrame f = .ok (off, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold mloadResult
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actualOff residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private def storeAfterPops (encode : U256 → Bytes) (width : U256)
    (encodedSize : ∀ word, (encode word).size = width.toNat)
    (price : Nat) (ctx : FrameCtx) (f : Frame) (off word : U256) : StepResult ctx :=
  let extent := windowPrice ctx.config f.memory off width
  match chargeGas f.gasMeter (price + extent.cost) with
  | .error error => .halt f error
  | .ok meter =>
    let data := encode word
    have fits : data.size = 0 ∨ off.toNat + data.size ≤ f.memory.size + extent.expandBy := by
      rw [encodedSize word]
      exact calculateGasExtendMemory_covers ctx.config f.memory [(off, width)] off width (by simp)
    advanceWithMemory ctx f meter fun stack _ memory sameMemory ↦
      storeUpdate off stack extent.expandBy
        (calculateGasExtendMemory_aligned ctx.config f.memory [(off, width)])
        data memory (sameMemory.symm ▸ fits)

private def storeResult (encode : U256 → Bytes) (width : U256)
    (encodedSize : ∀ word, (encode word).size = width.toNat)
    (price : Nat) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match popFrame f with
  | .error (residual, error) => .halt residual error
  | .ok (off, first) =>
    match popFrame first with
    | .error (residual, error) => .halt residual error
    | .ok (word, residual) => storeAfterPops encode width encodedSize price ctx residual off word

private def encodeWord (word : U256) : Bytes := word.toBeBytes32.toBytes

private theorem encode_word_size (word : U256) : (encodeWord word).size = (U256.ofNat 32).toNat :=
  FixedBytes.size_toBytes word.toBeBytes32

private def encodeLowByte (word : U256) : Bytes := Bytes.ofList [UInt8.ofNat word.toNat]

private theorem encode_low_byte_size (word : U256) :
    (encodeLowByte word).size = (U256.ofNat 1).toNat := by
  rw [encodeLowByte, Bytes.size_ofList]
  rfl

/-- Charge for the expanded word window, then load its big-endian word.
EELS `src/ethereum/forks/amsterdam/vm/instructions/memory.py:89–116`. -/
def mload {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (mloadResult ctx f)

/-- Charge for the expanded word window, then store all 32 big-endian bytes.
EELS `src/ethereum/forks/amsterdam/vm/instructions/memory.py:26–54`. -/
def mstore {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f)

/-- Charge for the expanded byte window, then store the word's low byte.
EELS `src/ethereum/forks/amsterdam/vm/instructions/memory.py:57–86`. -/
def mstore8 {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f)

private theorem advance_meter (ctx : FrameCtx) (f next : Frame) (meter : GasMeter)
    (update : (stack : Stack) → stack = f.stack →
      (memory : Memory) → memory = f.memory → Stack × Memory)
    (continued : advanceWithMemory ctx f meter update = .continue next) :
    next.gasMeter = meter := by
  rw [advanceWithMemory_eq] at continued
  simp only [StepResult.continue.injEq] at continued
  subst next
  rfl

/-- The initial missing offset halts with the entry frame. -/
theorem mload_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (missing : f.stack.pop = .error .stackUnderflow) :
    ((mload ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (mloadResult ctx f, w)) = _
  rw [mload_result_of_error ctx f _ missing]

/-- Gas denial keeps the offset pop and the entry memory and meter. -/
theorem mload_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (off, tail))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) :
    ((mload ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter _ .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (mloadResult ctx f, w)) = _
  rw [mload_result_of_pop ctx f off tail popped]
  simp only [mloadAfterPop, denied]

/-- The admitted 32-byte read and the actual push determine the complete paid result. -/
theorem mload_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (off, tail))
    (enough : ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost ≤
        f.gasMeter.gasLeft) :
    let e := calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]
    let price := ctx.config.costs.opcodeMloadBase + e.cost
    ∃ (nextMemory : Memory) (bytes : Bytes) (word : U256) (nextStack : Stack),
      nextMemory.toBytes = f.memory.toBytes ++ List.replicate e.expandBy 0 ∧
      bytes.toList = (nextMemory.toBytes.drop off.toNat).take 32 ∧
      bytes.size = 32 ∧ word.toNat = Uint.ofBeBytes bytes ∧
      tail.push word = .ok nextStack ∧ nextStack.toList = word :: tail.toList ∧
      ((mload ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack := nextStack
        memory := nextMemory
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) := by
  let e := windowPrice ctx.config f.memory off (U256.ofNat 32)
  let aligned := calculateGasExtendMemory_aligned ctx.config f.memory [(off, U256.ofNat 32)]
  let expanded := f.memory.expand e.expandBy aligned
  have within : off.toNat + 32 ≤ expanded.size :=
    expanded_covers_word ctx.config f.memory off aligned
  let bytes := expanded.readBytes off.toNat 32 (Or.inr within)
  let word := U256.ofNat (Uint.ofBeBytes bytes)
  let room := space_after_pop f.stack tail off popped
  let nextStack := pushLoaded tail word room
  have outputSize : bytes.size = 32 := read_word_size expanded off within
  have pushed : tail.push word = .ok nextStack := pushLoaded_actual tail word room
  refine ⟨expanded, bytes, word, nextStack,
    Memory.toBytes_expand _ _ _, Memory.readBytes_toList _ _ _ _, outputSize,
    decoded_word bytes outputSize, pushed,
    ((Stack.push_eq_ok_iff tail nextStack word).mp pushed).2, ?_⟩
  change pure (Except.ok (mloadResult ctx f, w)) = _
  rw [mload_result_of_pop ctx f off tail popped]
  simp only [mloadAfterPop, chargeGas_of_le _ _ enough]
  rw [advanceWithMemory_eq]
  rfl

/-- A continuing Id load spends its exact selected base and window price. -/
theorem mload_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mload ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + (ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) =
      f.gasMeter.phi := by
  change Except.ok (mloadResult ctx f, w) = .ok (.continue f', w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [mload_result_of_pop ctx f off tail popped] at result
  cases paid : chargeGas f.gasMeter
      (ctx.config.costs.opcodeMloadBase + (windowPrice ctx.config f.memory off (U256.ofNat 32)).cost) with
  | error e =>
    simp only [mloadAfterPop, paid] at result
    contradiction
  | ok meter =>
    simp only [mloadAfterPop, paid] at result
    rw [advance_meter _ _ _ _ _ result]
    exact chargeGas_phi _ _ _ paid

/-- A positive selected load charge gives strict local progress on continuation. -/
theorem mload_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mload ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := mload_continue_phi ctx f f' w w' off tail popped ran
  omega

private theorem store_success_model (encode : U256 → Bytes) (width : U256)
    (encodedSize : ∀ word, (encode word).size = width.toNat)
    (base : Nat) (ctx : FrameCtx) (f : Frame) (off word : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (word, s₂))
    (enough : base + (windowPrice ctx.config f.memory off width).cost ≤ f.gasMeter.gasLeft) :
    let e := windowPrice ctx.config f.memory off width
    let price := base + e.cost
    let bytes := f.memory.toBytes ++ List.replicate e.expandBy 0
    ∃ nextMemory : Memory,
      nextMemory.toBytes = bytes.take off.toNat ++ (encode word).toList ++
        bytes.drop (off.toNat + (encode word).size) ∧
      storeResult encode width encodedSize base ctx f = .continue { f with
        pc := f.pc + 1
        stack := s₂
        memory := nextMemory
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } } := by
  let e := windowPrice ctx.config f.memory off width
  let aligned := calculateGasExtendMemory_aligned ctx.config f.memory [(off, width)]
  let expanded := f.memory.expand e.expandBy aligned
  have fits : (encode word).size = 0 ∨ off.toNat + (encode word).size ≤ expanded.size := by
    rw [encodedSize]
    exact expanded_covers ctx.config f.memory off width aligned
  refine ⟨expanded.write off.toNat (encode word) fits, ?_, ?_⟩
  · rw [Memory.toBytes_write]
    dsimp only [expanded]
    rw [Memory.toBytes_expand]
  · simp only [storeResult, popFrame_eq, popFrameReference, first, second, storeAfterPops,
      chargeGas_of_le _ _ enough]
    rw [advanceWithMemory_eq]
    rfl

private theorem store_continue_phi (encode : U256 → Bytes) (width : U256)
    (encodedSize : ∀ word, (encode word).size = width.toNat)
    (base : Nat) (ctx : FrameCtx) (f f' : Frame) (off : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (off, tail))
    (continued : storeResult encode width encodedSize base ctx f = .continue f') :
    f'.gasMeter.phi + (base + (windowPrice ctx.config f.memory off width).cost) = f.gasMeter.phi := by
  cases operand : tail.pop with
  | error e =>
    simp only [storeResult, popFrame_eq, popFrameReference, popped, operand] at continued
    contradiction
  | ok result =>
    rcases result with ⟨word, rest⟩
    cases paid : chargeGas f.gasMeter (base + (windowPrice ctx.config f.memory off width).cost) with
    | error e =>
      simp only [storeResult, popFrame_eq, popFrameReference, popped, operand, storeAfterPops,
        paid] at continued
      contradiction
    | ok meter =>
      simp only [storeResult, popFrame_eq, popFrameReference, popped, operand, storeAfterPops,
        paid] at continued
      rw [advance_meter _ _ _ _ _ continued]
      exact chargeGas_phi _ _ _ paid

/-- An absent offset stops the word store before payment. -/
theorem mstore_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (missing : f.stack.pop = .error .stackUnderflow) :
    ((mstore ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, missing]

/-- An absent value stops the word store with the first residual stack. -/
theorem mstore_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (missing : s₁.pop = .error .stackUnderflow) :
    ((mstore ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  change pure (Except.ok (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, first, missing]

/-- Gas denial retains both pops and the entry memory and meter. -/
theorem mstore_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (word, s₂))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) :
    ((mstore ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter _ .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, first, second, storeAfterPops, denied]

/-- The paid word store overwrites its window in the expanded memory. -/
theorem mstore_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (word, s₂))
    (enough : ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost ≤
        f.gasMeter.gasLeft) :
    let e := calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]
    let price := ctx.config.costs.opcodeMstoreBase + e.cost
    let bytes := f.memory.toBytes ++ List.replicate e.expandBy 0
    ∃ nextMemory : Memory,
      nextMemory.toBytes = bytes.take off.toNat ++ word.toBeBytes32.toBytes.toList ++
        bytes.drop (off.toNat + 32) ∧
      ((mstore ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack := s₂
        memory := nextMemory
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) := by
  obtain ⟨nextMemory, model, result⟩ := store_success_model encodeWord (U256.ofNat 32)
    encode_word_size ctx.config.costs.opcodeMstoreBase ctx f off word s₁ s₂ first second enough
  refine ⟨nextMemory, ?_, ?_⟩
  · simpa only [encodeWord, FixedBytes.size_toBytes] using model
  · change pure (Except.ok (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f, w)) = _
    rw [result]

/-- A continuing Id word store spends its exact selected base and window price. -/
theorem mstore_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + (ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) =
      f.gasMeter.phi := by
  change Except.ok (storeResult encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f, w) = .ok (.continue f', w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  exact store_continue_phi encodeWord (U256.ofNat 32) encode_word_size
    ctx.config.costs.opcodeMstoreBase ctx f f' off tail popped result

/-- A positive selected word store charge gives strict local progress on continuation. -/
theorem mstore_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := mstore_continue_phi ctx f f' w w' off tail popped ran
  omega

/-- An absent offset stops the byte store before payment. -/
theorem mstore8_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (missing : f.stack.pop = .error .stackUnderflow) :
    ((mstore8 ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, missing]

/-- An absent value stops the byte store with the first residual stack. -/
theorem mstore8_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (missing : s₁.pop = .error .stackUnderflow) :
    ((mstore8 ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  change pure (Except.ok (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, first, missing]

/-- Gas denial retains both pops and the entry memory and meter. -/
theorem mstore8_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (word, s₂))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost) :
    ((mstore8 ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter _ .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f, w)) = _
  simp only [storeResult, popFrame_eq, popFrameReference, first, second, storeAfterPops, denied]

/-- The paid byte store overwrites its window in the expanded memory. -/
theorem mstore8_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (word, s₂))
    (enough : ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost ≤
        f.gasMeter.gasLeft) :
    let e := calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]
    let price := ctx.config.costs.opcodeMstore8Base + e.cost
    let bytes := f.memory.toBytes ++ List.replicate e.expandBy 0
    ∃ nextMemory : Memory,
      nextMemory.toBytes = bytes.take off.toNat ++ [UInt8.ofNat word.toNat] ++
        bytes.drop (off.toNat + 1) ∧
      ((mstore8 ctx f).run w).run = pure (Except.ok (.continue { f with
        pc := f.pc + 1
        stack := s₂
        memory := nextMemory
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) := by
  obtain ⟨nextMemory, model, result⟩ := store_success_model encodeLowByte (U256.ofNat 1)
    encode_low_byte_size ctx.config.costs.opcodeMstore8Base ctx f off word s₁ s₂ first second enough
  refine ⟨nextMemory, ?_, ?_⟩
  · simpa only [encodeLowByte, Bytes.toList_ofList, Bytes.size_ofList, List.length_cons,
      List.length_nil] using model
  · change pure (Except.ok (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f, w)) = _
    rw [result]

/-- A continuing Id byte store spends its exact selected base and window price. -/
theorem mstore8_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore8 ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + (ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost) =
      f.gasMeter.phi := by
  change Except.ok (storeResult encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f, w) = .ok (.continue f', w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  exact store_continue_phi encodeLowByte (U256.ofNat 1) encode_low_byte_size
    ctx.config.costs.opcodeMstore8Base ctx f f' off tail popped result

/-- A positive selected byte store charge gives strict local progress on continuation. -/
theorem mstore8_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore8 ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := mstore8_continue_phi ctx f f' w w' off tail popped ran
  omega

end STFSpec.Vm.Instructions
