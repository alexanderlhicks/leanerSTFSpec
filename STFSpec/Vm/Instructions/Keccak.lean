/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Hash.KeccakQuery
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Instructions.Handler

/-!
# KECCAK

Library `EthVmInstructions`. The standalone handler pays for the requested
memory window, then passes its exact bytes to the supplied Keccak oracle.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Hash STFSpec.Vm.Core

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

private def popKeccakOperands (stack : Stack) : Except Stack (U256 × U256 × Stack) :=
  match popWord stack with
  | .error residual => .error residual
  | .ok (offset, tail) =>
    match popWord tail with
    | .error residual => .error residual
    | .ok (size, residual) => .ok (offset, size, residual)

private theorem push_room (stack residual : Stack) (offset size : U256)
    (parsed : popKeccakOperands stack = .ok (offset, size, residual)) :
    residual.size < 1024 := by
  unfold popKeccakOperands at parsed
  rw [popWord_eq_reference] at parsed
  cases first : stack.pop with
  | error _ => simp [popWordReference, first] at parsed
  | ok one =>
    obtain ⟨start, tail⟩ := one
    simp only [popWordReference, first, popWord_eq_reference] at parsed
    cases second : tail.pop with
    | error _ => simp [second] at parsed
    | ok two =>
      obtain ⟨count, rest⟩ := two
      simp only [second, Except.ok.injEq, Prod.mk.injEq] at parsed
      obtain ⟨_, _, rfl⟩ := parsed
      have length := congrArg List.length ((Stack.pop_eq_ok_iff tail rest count).mp second)
      rw [List.length_cons, ← Stack.size_eq_length_toList, ← Stack.size_eq_length_toList] at length
      have bound := tail.size_le
      omega

private def pushDigest (stack : Stack) (word : U256) (room : stack.size < 1024) : Stack :=
  match pushed : stack.push word with
  | .error _ => False.elim ((Nat.ne_of_lt room) ((Stack.push_eq_error_iff _ _ _).mp pushed).1)
  | .ok next => next

private theorem pushDigest_actual (stack : Stack) (word : U256) (room : stack.size < 1024) :
    stack.push word = .ok (pushDigest stack word room) := by
  unfold pushDigest
  split
  · rename_i error failed
    exact False.elim ((Nat.ne_of_lt room) ((Stack.push_eq_error_iff _ _ _).mp failed).1)
  · assumption

private def keccakPrice (cfg : VmConfig) (size : U256) (memoryCost : Nat) : Nat :=
  cfg.costs.opcodeKeccak256Base + cfg.costs.opcodeKeccak256PerWord * (ceil32 size.toNat / 32) +
    memoryCost

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

private def keccakPaidReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (offset size : U256)
    (room : entry.stack.size < 1024) (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : size.toNat = 0 ∨ offset.toNat + size.toNat ≤ (entry.memory.expand extent aligned).size) :
    VmM m (StepResult ctx) :=
  let memory := entry.memory.expand extent aligned
  let data := memory.readBytes offset.toNat size.toNat covered
  fun world ↦ ExceptT.mk do
    let answer ← KeccakQuery.keccak (m := m) data.toByteArray
    let stack := pushDigest entry.stack (U256.ofBeBytes32 answer.toBytes32) room
    pure (.ok (.continue { entry with pc := entry.pc + 1, stack, memory, gasMeter := paid }, world))

private def keccakPaid {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (offset size : U256)
    (room : entry.stack.size < 1024) (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : size.toNat = 0 ∨ offset.toNat + size.toNat ≤ (entry.memory.expand extent aligned).size) :
    VmM m (StepResult ctx) :=
  match entry with
  | ⟨pc, residual, initial, _, logs, deleted, ret, addresses, slots⟩ =>
    let memory := initial.expand extent aligned
    let data := memory.readBytes offset.toNat size.toNat covered
    fun world ↦ ExceptT.mk do
      let answer ← KeccakQuery.keccak (m := m) data.toByteArray
      let stack := pushDigest residual (U256.ofBeBytes32 answer.toBytes32) room
      pure (.ok (.continue ⟨pc + 1, stack, memory, paid, logs, deleted, ret, addresses, slots⟩, world))

private theorem keccakPaid_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (offset size : U256)
    (room : entry.stack.size < 1024) (paid : GasMeter) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : size.toNat = 0 ∨ offset.toNat + size.toNat ≤ (entry.memory.expand extent aligned).size) :
    keccakPaid (m := m) ctx entry offset size room paid extent aligned covered =
      keccakPaidReference ctx entry offset size room paid extent aligned covered := by
  cases entry
  rfl

private def keccakReference {m : Type → Type} [Monad m] [KeccakQuery m] : Handler m :=
  fun ctx entry ↦
    match parsed : popKeccakOperands entry.stack with
    | .error stack => pure (.halt { entry with stack } .stackUnderflow)
    | .ok (offset, size, stack) =>
      let quote := calculateGasExtendMemory ctx.config entry.memory [(offset, size)]
      match chargeGas entry.gasMeter (keccakPrice ctx.config size quote.cost) with
      | .error error => pure (.halt { entry with stack } error)
      | .ok paid =>
        keccakPaid ctx { entry with stack } offset size (push_room entry.stack stack offset size parsed)
          paid quote.expandBy (calculateGasExtendMemory_aligned ctx.config entry.memory [(offset, size)])
          (expanded_window ctx.config entry.memory offset size)

/-- Pay for the selected memory window, query Keccak once and push its complete digest.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/keccak.py:26–62`. -/
def keccak {m : Type → Type} [Monad m] [KeccakQuery m] : Handler m :=
  fun ctx entry ↦
    match entry with
    | ⟨pc, stack, memory, meter, logs, deleted, ret, addresses, slots⟩ =>
      match parsed : popKeccakOperands stack with
      | .error residual =>
        pure (.halt ⟨pc, residual, memory, meter, logs, deleted, ret, addresses, slots⟩ .stackUnderflow)
      | .ok (offset, size, residual) =>
        let quote := calculateGasExtendMemory ctx.config memory [(offset, size)]
        let popped : Frame := ⟨pc, residual, memory, meter, logs, deleted, ret, addresses, slots⟩
        match chargeGas meter (keccakPrice ctx.config size quote.cost) with
        | .error error => pure (.halt popped error)
        | .ok paid =>
          keccakPaid ctx popped offset size (push_room stack residual offset size parsed)
            paid quote.expandBy (calculateGasExtendMemory_aligned ctx.config memory [(offset, size)])
            (expanded_window ctx.config memory offset size)

private theorem keccak_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) :
    keccak (m := m) ctx entry = keccakReference ctx entry := by
  cases entry
  rfl

private theorem keccak_of_underflow {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (stack : Stack)
    (parsed : popKeccakOperands entry.stack = .error stack) :
    keccak (m := m) ctx entry = pure (.halt { entry with stack } .stackUnderflow) := by
  rw [keccak_eq_reference]
  unfold keccakReference
  split
  · rename_i observed failed
    rw [parsed] at failed
    cases failed
    rfl
  · rename_i _ _ _ _ succeeded
    rw [parsed] at succeeded
    contradiction

private theorem keccak_of_operands {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (offset size : U256) (stack : Stack)
    (parsed : popKeccakOperands entry.stack = .ok (offset, size, stack)) :
    keccak (m := m) ctx entry =
      let quote := calculateGasExtendMemory ctx.config entry.memory [(offset, size)]
      match chargeGas entry.gasMeter (keccakPrice ctx.config size quote.cost) with
      | .error error => pure (.halt { entry with stack } error)
      | .ok paid =>
        keccakPaid ctx { entry with stack } offset size (push_room entry.stack stack offset size parsed)
          paid quote.expandBy (calculateGasExtendMemory_aligned ctx.config entry.memory [(offset, size)])
          (expanded_window ctx.config entry.memory offset size) := by
  rw [keccak_eq_reference]
  unfold keccakReference
  split
  · rename_i failed
    rw [parsed] at failed
    contradiction
  · rename_i succeeded
    rw [parsed] at succeeded
    simp only [Except.ok.injEq, Prod.mk.injEq] at succeeded
    obtain ⟨rfl, rfl, rfl⟩ := succeeded
    rfl

private theorem keccak_first_underflow {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (empty : entry.stack.pop = .error .stackUnderflow) :
    ((keccak ctx entry).run world).run = pure (.ok (.halt entry .stackUnderflow, world)) := by
  have parsed : popKeccakOperands entry.stack = .error entry.stack := by
    simp only [popKeccakOperands, popWord_eq_reference, popWordReference, empty]
  rw [keccak_of_underflow ctx entry _ parsed]
  rfl

private theorem keccak_second_underflow {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (offset : U256) (tail : Stack)
    (first : entry.stack.pop = .ok (offset, tail))
    (second : tail.pop = .error .stackUnderflow) :
    ((keccak ctx entry).run world).run =
      pure (.ok (.halt { entry with stack := tail } .stackUnderflow, world)) := by
  have parsed : popKeccakOperands entry.stack = .error tail := by
    simp only [popKeccakOperands, popWord_eq_reference, popWordReference, first, second]
  rw [keccak_of_underflow ctx entry _ parsed]
  rfl

private theorem keccak_denied {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (offset size : U256) (stack : Stack)
    (parsed : popKeccakOperands entry.stack = .ok (offset, size, stack))
    (short : entry.gasMeter.gasLeft <
      keccakPrice ctx.config size (calculateGasExtendMemory ctx.config entry.memory [(offset, size)]).cost) :
    ((keccak ctx entry).run world).run =
      pure (.ok (.halt { entry with stack } .outOfGas, world)) := by
  have denied := (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩
  simp only [keccak_of_operands _ _ _ _ _ parsed, denied]
  rfl

private theorem keccak_paid {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (entry : Frame) (world : VmWorld m) (offset size : U256) (stack : Stack)
    (parsed : popKeccakOperands entry.stack = .ok (offset, size, stack)) :
    let windows := [(offset, size)]
    let quote := calculateGasExtendMemory ctx.config entry.memory windows
    let price := keccakPrice ctx.config size quote.cost
    let memory := entry.memory.expand quote.expandBy
      (calculateGasExtendMemory_aligned ctx.config entry.memory windows)
    let data := memory.readBytes offset.toNat size.toNat (expanded_window ctx.config entry.memory offset size)
    price ≤ entry.gasMeter.gasLeft →
    ((keccak ctx entry).run world).run =
      (do
        let answer ← KeccakQuery.keccak (m := m) data.toByteArray
        let next := pushDigest stack (U256.ofBeBytes32 answer.toBytes32)
          (push_room entry.stack stack offset size parsed)
        pure (.ok (.continue { entry with
          pc := entry.pc + 1, stack := next, memory
          gasMeter := { entry.gasMeter with gasLeft := entry.gasMeter.gasLeft - price } }, world))) := by
  dsimp only
  intro payable
  simp only [keccak_of_operands _ _ _ _ _ parsed, chargeGas_of_le _ _ payable, keccakPaid_eq_reference,
    keccakPaidReference]
  rfl

private theorem keccak_preimage (ctx : FrameCtx) (memory : Memory) (offset size : U256) :
    let windows := [(offset, size)]
    let quote := calculateGasExtendMemory ctx.config memory windows
    let expanded := memory.expand quote.expandBy (calculateGasExtendMemory_aligned ctx.config memory windows)
    let data := expanded.readBytes offset.toNat size.toNat (expanded_window ctx.config memory offset size)
    data.toList = ((memory.toBytes ++ List.replicate quote.expandBy 0).drop offset.toNat).take size.toNat := by
  dsimp only
  rw [Memory.readBytes_toList, Memory.toBytes_expand]

private theorem digest_bytes (answer : Hash32) :
    (U256.ofBeBytes32 answer.toBytes32).toBeBytes32 = answer.toBytes32 :=
  U256.toBeBytes32_ofBeBytes32 _

private theorem keccak_continue_phi (ctx : FrameCtx) (entry next : Frame) (world world' : VmWorld Id)
    (ran : ((keccak ctx entry).run world).run = .ok (.continue next, world')) :
    ∃ offset size : U256, ∃ stack : Stack,
      popKeccakOperands entry.stack = .ok (offset, size, stack) ∧
      next.gasMeter.phi +
        keccakPrice ctx.config size (calculateGasExtendMemory ctx.config entry.memory [(offset, size)]).cost =
        entry.gasMeter.phi := by
  cases parsed : popKeccakOperands entry.stack with
  | error residual =>
    rw [keccak_of_underflow ctx entry _ parsed] at ran
    cases (Prod.mk.inj (Except.ok.inj ran)).1
  | ok operands =>
    obtain ⟨offset, size, stack⟩ := operands
    cases charged : chargeGas entry.gasMeter
        (keccakPrice ctx.config size (calculateGasExtendMemory ctx.config entry.memory [(offset, size)]).cost) with
    | error error =>
      simp only [keccak_of_operands _ _ _ _ _ parsed, charged] at ran
      cases (Prod.mk.inj (Except.ok.inj ran)).1
    | ok paid =>
      simp only [keccak_of_operands _ _ _ _ _ parsed, charged, keccakPaid_eq_reference, keccakPaidReference] at ran
      have frame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
      subst next
      exact ⟨offset, size, stack, rfl, chargeGas_phi _ _ paid charged⟩

private theorem keccak_positive (ctx : FrameCtx) (entry next : Frame) (world world' : VmWorld Id)
    (ran : ((keccak ctx entry).run world).run = .ok (.continue next, world'))
    (positive : ∀ offset size : U256, ∀ stack : Stack,
      popKeccakOperands entry.stack = .ok (offset, size, stack) →
        0 < keccakPrice ctx.config size
          (calculateGasExtendMemory ctx.config entry.memory [(offset, size)]).cost) :
    next.gasMeter.phi + 1 ≤ entry.gasMeter.phi := by
  obtain ⟨offset, size, stack, parsed, equation⟩ := keccak_continue_phi ctx entry next world world' ran
  have nonzero := positive offset size stack parsed
  omega

end STFSpec.Vm.Instructions
