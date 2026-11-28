/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.Address
import STFSpec.State.AccountDeployable
import STFSpec.State.AccountEmptiness
import STFSpec.State.AccountScalars
import STFSpec.Vm.Core.CallGas
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.ChildFrame
import STFSpec.Vm.Instructions.CreateResume
import STFSpec.Vm.Instructions.Handler

/-!
# CREATE and CREATE2

Library `EthVmInstructions`. Run the parent-side instruction through a local
exit or a child creation request.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§2.5/3/4/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.State STFSpec.Vm.Core

private def pushZeroWithRoom (stack : Stack) (room : stack.size < STACK_DEPTH_LIMIT) : Stack :=
  match result : stack.push U256.zero with
  | .ok after => after
  | .error error =>
    False.elim (Nat.ne_of_lt room ((Stack.push_eq_error_iff stack U256.zero error).mp result).1)

private def failCreate (parent : Frame) (room : parent.stack.size < STACK_DEPTH_LIMIT) : Frame :=
  { parent with stack := pushZeroWithRoom parent.stack room, pc := parent.pc + 1 }

private def followCreate {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (parent : Frame) (destination : Address) (endowment : U256)
    (initCode : Bytes) (room : parent.stack.size < STACK_DEPTH_LIMIT)
    (deeper : ctx.depth < STACK_DEPTH_LIMIT) :
    VmM m (StepResult ctx) := do
  let warmed := { parent with accessedAddresses := parent.accessedAddresses.insert destination }
  let alive ← liftState (isAccountAlive destination)
  let charged := !alive
  let price := ctx.config.stateCosts.bytesPerNewAccount * ctx.config.stateCosts.costPerStateByte
  let chargedMeter := if charged then chargeStateGas parent.gasMeter price
    else .ok parent.gasMeter
  match chargedMeter with
  | .error error => pure (.halt warmed error)
  | .ok meter =>
    let (grant, suspended) := withholdCreateGas meter
    let deployable ← liftState (accountDeployable destination)
    if !deployable then
      liftState (incrementNonce ctx.currentTarget)
      pure (.continue (failCreate { warmed with gasMeter := suspended } room))
    else
      let (reservoir, drained) := drainStateGasReservoir suspended
      liftState (incrementNonce ctx.currentTarget)
      let req : CreateRequest :=
        { gas := grant
          stateGasReservoir := reservoir
          endowment
          caller := ctx.currentTarget
          contractAddress := destination
          initCode
          newAccountCharged := charged }
      pure (.create { warmed with gasMeter := drained } req deeper room)

private def genericCreate {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (destination : Address) (endowment : U256)
    (initCode : Bytes) (room : frame.stack.size < STACK_DEPTH_LIMIT) :
    VmM m (StepResult ctx) := do
  let reset := { frame with returnData := Bytes.empty }
  let sender ← liftState (getAccount ctx.currentTarget)
  if sender.balance.toNat < endowment.toNat ∨ sender.nonce = 2^64 - 1 then
    pure (.continue (failCreate reset room))
  else if deeper : ctx.depth < STACK_DEPTH_LIMIT then
    followCreate ctx reset destination endowment initCode room deeper
  else pure (.continue (failCreate reset room))

private theorem stack_room_after_pop (before after : Stack) (word : U256)
    (popped : before.pop = .ok (word, after)) : after.size < STACK_DEPTH_LIMIT := by
  have bound := before.size_le
  rw [Stack.size_eq_length_toList, (Stack.pop_eq_ok_iff before after word).mp popped] at bound
  rw [Stack.size_eq_length_toList]
  simp only [List.length_cons] at bound
  change after.toList.length < 1024
  omega

private abbrev PoppedFrame := U256 × {after : Frame // after.stack.size < STACK_DEPTH_LIMIT}

private def popFrameReference (frame : Frame) : Except (Frame × ExceptionalHalt) PoppedFrame :=
  match popped : frame.stack.pop with
  | .error error => .error (frame, error)
  | .ok (value, stack) => .ok (value, ⟨{ frame with stack },
      stack_room_after_pop frame.stack stack value popped⟩)

private theorem pop_error_of_nonempty (stack : Stack) (error : ExceptionalHalt)
    (nonempty : 0 < stack.size) (failed : stack.pop = .error error) : False := by
  have observed := (Stack.pop_eq_error_iff stack error).mp failed
  simp [Stack.size_eq_length_toList, observed.1] at nonempty

private def popFrame (frame : Frame) : Except (Frame × ExceptionalHalt) PoppedFrame :=
  if nonempty : 0 < frame.stack.size then
    match popped : frame.stack.pop with
    | .error error => False.elim (pop_error_of_nonempty frame.stack error nonempty popped)
    | .ok (value, stack) => .ok (value, ⟨{ frame with stack },
        stack_room_after_pop frame.stack stack value popped⟩)
  else
    popFrameReference frame

private theorem popFrame_eq (frame : Frame) : popFrame frame = popFrameReference frame := by
  unfold popFrame
  split
  · unfold popFrameReference
    split
    · rename_i error failed
      exact False.elim (pop_error_of_nonempty frame.stack error ‹0 < frame.stack.size› failed)
    · rfl
  · rfl

private structure CreationInput where
  endowment : U256
  offset : U256
  size : U256
  salt : Option Bytes32

-- Keep the residual frame out of the data passed to address derivation so
-- expansion can consume its memory.
private structure CreationOperands where
  input : CreationInput
  frame : Frame
  room : frame.stack.size < STACK_DEPTH_LIMIT

private def creationOperands (salted : Bool) (frame : Frame) :
    Except (Frame × ExceptionalHalt) CreationOperands := do
  let (endowment, first) ← popFrame frame
  let (offset, second) ← popFrame first.val
  let (size, third) ← popFrame second.val
  if salted then
    let (salt, fourth) ← popFrame third.val
    pure ⟨⟨endowment, offset, size, some salt.toBeBytes32⟩, fourth.val, fourth.property⟩
  else
    pure ⟨⟨endowment, offset, size, none⟩, third.val, third.property⟩

private theorem expanded_window_fits (cfg : VmConfig) (memory : Memory) (offset size : U256) :
    let ws := [(offset, size)]
    let expansion := calculateGasExtendMemory cfg memory ws
    let expanded :=
      memory.expand expansion.expandBy (calculateGasExtendMemory_aligned cfg memory ws)
    size.toNat = 0 ∨ offset.toNat + size.toNat ≤ expanded.size := by
  dsimp only
  rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append,
    Memory.length_toBytes, List.length_replicate]
  exact calculateGasExtendMemory_covers cfg memory [(offset, size)] offset size (by simp)

private def createExecutionPrice (salted : Bool) (cfg : VmConfig)
    (extensionCost size : Nat) : Nat :=
  let hashGas := cfg.costs.opcodeKeccak256PerWord * (ceil32 size / 32)
  let initGas := initCodeCost cfg size
  if salted then cfg.costs.createAccess + hashGas + extensionCost + initGas
  else cfg.costs.createAccess + extensionCost + initGas

private def createInMemory {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (expanded : Frame) (input : CreationInput)
    (room : expanded.stack.size < STACK_DEPTH_LIMIT)
    (fits : input.size.toNat = 0 ∨
      input.offset.toNat + input.size.toNat ≤ expanded.memory.size) :
    VmM m (StepResult ctx) := do
  match input.salt with
  | none =>
    let sender ← liftState (getAccount ctx.currentTarget)
    let destination ← computeContractAddressQ ctx.currentTarget sender.nonce
    let initCode := expanded.memory.readBytes input.offset.toNat input.size.toNat fits
    genericCreate ctx expanded destination input.endowment initCode room
  | some salt =>
    let initCode := expanded.memory.readBytes input.offset.toNat input.size.toNat fits
    let destination ← computeCreate2ContractAddressQ ctx.currentTarget salt initCode.toByteArray
    genericCreate ctx expanded destination input.endowment initCode room

private def createAfterOperands {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (operands : CreationOperands) :
    VmM m (StepResult ctx) :=
  let cfg := ctx.config
  let f := operands.frame
  let size := operands.input.size.toNat
  let window := [(operands.input.offset, operands.input.size)]
  let expansion := calculateGasExtendMemory cfg f.memory window
  let cost := createExecutionPrice salted cfg expansion.cost size
  match chargeGas f.gasMeter cost with
  | .error error => pure (.halt f error)
  | .ok meter =>
    let paid := { f with gasMeter := meter }
    if cfg.limits.maxInitCodeSize < size then pure (.halt paid .outOfGas)
    else
      let memory := f.memory.expand expansion.expandBy
        (calculateGasExtendMemory_aligned cfg f.memory window)
      createInMemory ctx { paid with memory } operands.input operands.room
        (expanded_window_fits cfg f.memory operands.input.offset operands.input.size)

private def createHandler {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) : Handler m :=
  fun ctx frame ↦
    if ctx.isStatic then pure (.halt frame .writeInStaticContext)
    else
      match creationOperands salted frame with
      | .error (after, error) => pure (.halt after error)
      | .ok operands => createAfterOperands salted ctx operands

/-- Price the instruction and derive its destination from the sender's current nonce.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:59–171,188–239` at the pin. -/
def create {m : Type → Type} [Monad m] [KeccakQuery m] : Handler m :=
  createHandler false

/-- Price the instruction and derive its destination from the salt and init code.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:59–171,242–304` at the pin. -/
def create2 {m : Type → Type} [Monad m] [KeccakQuery m] : Handler m :=
  createHandler true

/-! ### Ordered local laws -/

private theorem popFrame_error (frame : Frame) (error : ExceptionalHalt)
    (failed : frame.stack.pop = .error error) :
    popFrame frame = .error (frame, error) := by
  rw [popFrame_eq]
  unfold popFrameReference
  split
  · next actual h => rw [h] at failed; cases failed; rfl
  · next _ _ h => rw [h] at failed; contradiction

private theorem popFrame_ok (frame : Frame) (value : U256) (stack : Stack)
    (popped : frame.stack.pop = .ok (value, stack)) :
    popFrame frame = .ok (value, ⟨{ frame with stack },
      stack_room_after_pop frame.stack stack value popped⟩) := by
  rw [popFrame_eq]
  unfold popFrameReference
  split
  · next _ h => rw [h] at popped; contradiction
  · next _ _ h => rw [h] at popped; cases popped; rfl

private theorem creationOperands_first_underflow (salted : Bool) (frame : Frame)
    (first : frame.stack.pop = .error .stackUnderflow) :
    creationOperands salted frame = .error (frame, .stackUnderflow) := by
  simp only [creationOperands, popFrame_error _ _ first, Bind.bind, Except.bind]

private theorem creationOperands_second_underflow (salted : Bool) (frame : Frame)
    (endowment : U256) (stack : Stack) (first : frame.stack.pop = .ok (endowment, stack))
    (second : stack.pop = .error .stackUnderflow) :
    creationOperands salted frame = .error ({ frame with stack }, .stackUnderflow) := by
  simp only [creationOperands, popFrame_ok _ _ _ first,
    popFrame_error { frame with stack } _ second, Bind.bind, Except.bind]

private theorem creationOperands_third_underflow (salted : Bool) (frame : Frame)
    (endowment offset : U256) (firstStack secondStack : Stack)
    (first : frame.stack.pop = .ok (endowment, firstStack))
    (second : firstStack.pop = .ok (offset, secondStack))
    (third : secondStack.pop = .error .stackUnderflow) :
    creationOperands salted frame =
      .error ({ frame with stack := secondStack }, .stackUnderflow) := by
  simp only [creationOperands, popFrame_ok _ _ _ first,
    popFrame_ok { frame with stack := firstStack } _ _ second,
    popFrame_error { frame with stack := secondStack } _ third, Bind.bind, Except.bind]

private theorem creationOperands_salt_underflow (frame : Frame)
    (endowment offset size : U256) (firstStack secondStack thirdStack : Stack)
    (first : frame.stack.pop = .ok (endowment, firstStack))
    (second : firstStack.pop = .ok (offset, secondStack))
    (third : secondStack.pop = .ok (size, thirdStack))
    (salt : thirdStack.pop = .error .stackUnderflow) :
    creationOperands true frame =
      .error ({ frame with stack := thirdStack }, .stackUnderflow) := by
  simp only [creationOperands, popFrame_ok _ _ _ first,
    popFrame_ok { frame with stack := firstStack } _ _ second,
    popFrame_ok { frame with stack := secondStack } _ _ third,
    popFrame_error { frame with stack := thirdStack } _ salt, Bind.bind, Except.bind, ite_true]

private theorem createHandler_static {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (frame : Frame) (static : ctx.isStatic = true) :
    createHandler (m := m) salted ctx frame = pure (.halt frame .writeInStaticContext) := by
  simp only [createHandler, static, ite_true]

private theorem createHandler_pop_error {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (frame residual : Frame) (error : ExceptionalHalt)
    (dynamic : ctx.isStatic = false)
    (operands : creationOperands salted frame = .error (residual, error)) :
    createHandler (m := m) salted ctx frame = pure (.halt residual error) := by
  simp only [createHandler, dynamic, Bool.false_eq_true, ite_false, operands]

private theorem createAfterOperands_oog {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (operands : CreationOperands) (error : ExceptionalHalt)
    (denied : chargeGas operands.frame.gasMeter (createExecutionPrice salted ctx.config
      (calculateGasExtendMemory ctx.config operands.frame.memory [(operands.input.offset,
        operands.input.size)]).cost operands.input.size.toNat) = .error error) :
    createAfterOperands (m := m) salted ctx operands = pure (.halt operands.frame error) := by
  simp only [createAfterOperands, denied]

private theorem createAfterOperands_oversize {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (operands : CreationOperands) (meter : GasMeter)
    (paid : chargeGas operands.frame.gasMeter (createExecutionPrice salted ctx.config
      (calculateGasExtendMemory ctx.config operands.frame.memory [(operands.input.offset,
        operands.input.size)]).cost operands.input.size.toNat) = .ok meter)
    (oversize : ctx.config.limits.maxInitCodeSize < operands.input.size.toNat) :
    createAfterOperands (m := m) salted ctx operands =
      pure (.halt { operands.frame with gasMeter := meter } .outOfGas) := by
  simp only [createAfterOperands, paid, oversize, ite_true]

private theorem createAfterOperands_admitted {m : Type → Type} [Monad m] [KeccakQuery m]
    (salted : Bool) (ctx : FrameCtx) (operands : CreationOperands) (meter : GasMeter)
    (paid : chargeGas operands.frame.gasMeter (createExecutionPrice salted ctx.config
      (calculateGasExtendMemory ctx.config operands.frame.memory [(operands.input.offset,
        operands.input.size)]).cost operands.input.size.toNat) = .ok meter)
    (admitted : operands.input.size.toNat ≤ ctx.config.limits.maxInitCodeSize) :
    let memory := operands.frame.memory
    let window := [(operands.input.offset, operands.input.size)]
    let expansion := calculateGasExtendMemory ctx.config memory window
    let expanded := memory.expand expansion.expandBy
      (calculateGasExtendMemory_aligned ctx.config memory window)
    createAfterOperands (m := m) salted ctx operands =
      createInMemory ctx { operands.frame with gasMeter := meter, memory := expanded }
        operands.input operands.room
        (expanded_window_fits ctx.config memory operands.input.offset operands.input.size) := by
  simp only [createAfterOperands, paid, Nat.not_lt.mpr admitted, ite_false]

private theorem failCreate_pc_stack (parent : Frame)
    (room : parent.stack.size < STACK_DEPTH_LIMIT) :
    (failCreate parent room).pc = parent.pc + 1 ∧
      (failCreate parent room).stack.toList = U256.zero :: parent.stack.toList := by
  refine ⟨rfl, ?_⟩
  unfold failCreate pushZeroWithRoom
  split
  · next result h => exact ((Stack.push_eq_ok_iff parent.stack result U256.zero).mp h).2
  · next error h =>
    exact False.elim (Nat.ne_of_lt room ((Stack.push_eq_error_iff _ _ error).mp h).1)

private theorem createInMemory_nonce_address {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (frame : Frame) (input : CreationInput)
    (room : frame.stack.size < STACK_DEPTH_LIMIT)
    (fits : input.size.toNat = 0 ∨
      input.offset.toNat + input.size.toNat ≤ frame.memory.size)
    (unsalted : input.salt = none) :
    createInMemory (m := m) ctx frame input room fits = (do
      let sender ← liftState (getAccount ctx.currentTarget)
      let destination ← computeContractAddressQ ctx.currentTarget sender.nonce
      let initCode := frame.memory.readBytes input.offset.toNat input.size.toNat fits
      genericCreate ctx frame destination input.endowment initCode room) := by
  simp only [createInMemory, unsalted]

private theorem createInMemory_salt_address {m : Type → Type} [Monad m] [KeccakQuery m]
    (ctx : FrameCtx) (frame : Frame) (input : CreationInput) (salt : Bytes32)
    (room : frame.stack.size < STACK_DEPTH_LIMIT)
    (fits : input.size.toNat = 0 ∨
      input.offset.toNat + input.size.toNat ≤ frame.memory.size)
    (salted : input.salt = some salt) :
    createInMemory (m := m) ctx frame input room fits = (do
      let initCode := frame.memory.readBytes input.offset.toNat input.size.toNat fits
      let destination ← computeCreate2ContractAddressQ ctx.currentTarget salt initCode.toByteArray
      genericCreate ctx frame destination input.endowment initCode room) := by
  simp only [createInMemory, salted]

private theorem runVm_bind {m : Type → Type} [Monad m] {α β : Type}
    (action : VmM m α) (next : α → VmM m β) (world : VmWorld m) :
    (((action >>= next).run world).run) =
      ((action.run world).run >>= fun result ↦
        match result with
        | .error fault => pure (.error fault)
        | .ok (value, after) => ((next value).run after).run) := by
  simp only [StateT.run, Bind.bind, StateT.bind, ExceptT.bind, ExceptT.run, ExceptT.mk]
  congr 1
  funext result
  cases result with
  | error => rfl
  | ok pair => cases pair; rfl

private theorem followCreate_run {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (parent : Frame) (destination : Address) (endowment : U256)
    (initCode : Bytes) (room : parent.stack.size < STACK_DEPTH_LIMIT)
    (deeper : ctx.depth < STACK_DEPTH_LIMIT) (world : VmWorld m) :
    ((followCreate ctx parent destination endowment initCode room deeper).run world).run =
      ((liftState (isAccountAlive destination)).run world).run >>= fun
      | .error fault => pure (.error fault)
      | .ok (alive, afterAlive) =>
        let warmed :=
          { parent with accessedAddresses := parent.accessedAddresses.insert destination }
        let price :=
          ctx.config.stateCosts.bytesPerNewAccount * ctx.config.stateCosts.costPerStateByte
        match (if !alive then chargeStateGas parent.gasMeter price else .ok parent.gasMeter) with
        | .error error => pure (.ok (.halt warmed error, afterAlive))
        | .ok meter =>
          let (grant, suspended) := withholdCreateGas meter
          ((liftState (accountDeployable destination)).run afterAlive).run >>= fun
          | .error fault => pure (.error fault)
          | .ok (deployable, afterTest) =>
            if !deployable then
              ((liftState (incrementNonce ctx.currentTarget)).run afterTest).run >>= fun
              | .error fault => pure (.error fault)
              | .ok (_, afterNonce) =>
                pure (.ok (.continue (failCreate { warmed with gasMeter := suspended } room),
                  afterNonce))
            else
              let (reservoir, drained) := drainStateGasReservoir suspended
              let req : CreateRequest :=
                ⟨grant, reservoir, endowment, ctx.currentTarget, destination, initCode, !alive⟩
              ((liftState (incrementNonce ctx.currentTarget)).run afterTest).run >>= fun
              | .error fault => pure (.error fault)
              | .ok (_, afterNonce) =>
                pure (.ok (.create { warmed with gasMeter := drained } req deeper room,
                  afterNonce)) := by
  unfold followCreate
  rw [runVm_bind]
  congr 1
  funext result
  cases result with
  | error => rfl
  | ok entry =>
    obtain ⟨alive, afterAlive⟩ := entry
    dsimp only
    split
    · rfl
    · simp only [runVm_bind]
      congr 1
      funext result
      cases result with
      | error => rfl
      | ok entry =>
        obtain ⟨deployable, afterTest⟩ := entry
        dsimp only
        cases deployable
        · simp only [Bool.not_false, ite_true, runVm_bind]
          congr 1
          funext result
          cases result with
          | error => rfl
          | ok entry => cases entry; rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, runVm_bind]
          congr 1
          funext result
          cases result with
          | error => rfl
          | ok entry => cases entry; rfl

private theorem genericCreate_run {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (destination : Address) (endowment : U256)
    (initCode : Bytes) (room : frame.stack.size < STACK_DEPTH_LIMIT) (world : VmWorld m) :
    ((genericCreate ctx frame destination endowment initCode room).run world).run =
      ((liftState (getAccount ctx.currentTarget)).run world).run >>= fun result ↦
        match result with
        | .error fault => pure (.error fault)
        | .ok (sender, after) =>
          let reset := { frame with returnData := Bytes.empty }
          if sender.balance.toNat < endowment.toNat ∨ sender.nonce = 2^64 - 1 then
            pure (.ok (.continue (failCreate reset room), after))
          else if deeper : ctx.depth < STACK_DEPTH_LIMIT then
            ((followCreate ctx reset destination endowment initCode room deeper).run after).run
          else pure (.ok (.continue (failCreate reset room), after)) := by
  unfold genericCreate
  rw [runVm_bind]
  congr 1
  funext result
  cases result with
  | error => rfl
  | ok result =>
    obtain ⟨sender, after⟩ := result
    by_cases blocked : sender.balance.toNat < endowment.toNat ∨ sender.nonce = 2^64 - 1
    · simp only [blocked, ite_true]
      rfl
    · simp only [blocked, ite_false]
      split <;> rfl

/-! ### Local potential accounting -/

private def retainedPhi {ctx : FrameCtx} : StepResult ctx → Nat
  | .continue frame => frame.gasMeter.phi
  | .create parent req _ _ => parent.gasMeter.phi + req.gas
  | _ => 0

private theorem result_of_pure {α : Type} (expected actual : α) (initial final : VmWorld Id)
    (observed : ((pure expected : VmM Id α).run initial).run = .ok (actual, final)) :
    actual = expected := by
  change Except.ok (expected, initial) = .ok (actual, final) at observed
  exact (congrArg Prod.fst (Except.ok.inj observed)).symm

private theorem result_of_bind {α β : Type}
    (action : VmM Id α) (next : α → VmM Id β) (initial final : VmWorld Id) (result : β)
    (observed : (((action >>= next).run initial).run) = .ok (result, final)) :
    ∃ (value : α) (after : VmWorld Id),
      ((action.run initial).run = .ok (value, after)) ∧
      ((next value).run after).run = .ok (result, final) := by
  rw [runVm_bind] at observed
  cases first : (action.run initial).run with
  | error fault =>
    rw [first] at observed
    contradiction
  | ok pair =>
    obtain ⟨value, after⟩ := pair
    rw [first] at observed
    exact ⟨value, after, rfl, observed⟩

private theorem result_of_bind_pure {α β : Type}
    (action : VmM Id α) (expected actual : β) (initial final : VmWorld Id)
    (observed : (((action >>= fun _ ↦ pure expected).run initial).run) = .ok (actual, final)) :
    actual = expected := by
  obtain ⟨_, after, _, reached⟩ := result_of_bind action _ initial final actual observed
  exact result_of_pure expected actual after final reached

private theorem optional_charge_phi (charged : Bool) (before after : GasMeter) (price : Nat)
    (paid : (if charged then chargeStateGas before price else .ok before) = .ok after) :
    after.phi = before.phi := by
  cases charged
  · simp only [Bool.false_eq_true, ite_false, Except.ok.injEq] at paid
    rw [← paid]
  · exact chargeStateGas_phi before price after paid

private theorem followCreate_retainedPhi {ctx : FrameCtx} (entry : Frame)
    (destination : Address) (endowment : U256) (init : Bytes)
    (room : entry.stack.size < STACK_DEPTH_LIMIT) (deeper : ctx.depth < STACK_DEPTH_LIMIT)
    (initial final : VmWorld Id) (result : StepResult ctx)
    (observed : ((followCreate ctx entry destination endowment init room deeper).run initial).run =
      .ok (result, final)) : retainedPhi result ≤ entry.gasMeter.phi := by
  unfold followCreate at observed
  obtain ⟨alive, afterAlive, _, reached⟩ :=
    result_of_bind (liftState (isAccountAlive destination)) _ initial final result observed
  let price := ctx.config.stateCosts.bytesPerNewAccount * ctx.config.stateCosts.costPerStateByte
  cases paid : (if !alive then chargeStateGas entry.gasMeter price else .ok entry.gasMeter) with
  | error error =>
    have halted : ((pure (.halt (ctx := ctx)
      { entry with accessedAddresses := entry.accessedAddresses.insert destination } error) :
        VmM Id (StepResult ctx)).run afterAlive).run = .ok (result, final) := by
      simpa only [price, paid] using reached
    rw [result_of_pure _ _ _ _ halted]
    exact Nat.zero_le _
  | ok meter =>
    have unchanged := optional_charge_phi (!alive) entry.gasMeter meter price paid
    have withheld := withholdCreateGas_phi meter
    simp only [price, paid] at reached
    obtain ⟨deployable, afterDeployable, _, tested⟩ :=
      result_of_bind (liftState (accountDeployable destination)) _ afterAlive final result reached
    cases deployable
    · simp only [Bool.not_false, ite_true] at tested
      rw [result_of_bind_pure (liftState (incrementNonce ctx.currentTarget)) _ _ _ _ tested]
      change (withholdCreateGas meter).2.phi ≤ entry.gasMeter.phi
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at tested
      rw [result_of_bind_pure (liftState (incrementNonce ctx.currentTarget)) _ _ _ _ tested]
      change (drainStateGasReservoir (withholdCreateGas meter).2).2.phi +
        (withholdCreateGas meter).1 ≤ entry.gasMeter.phi
      rw [drainStateGasReservoir_phi, withheld, unchanged]
      exact Nat.le_refl _

private theorem genericCreate_retainedPhi {ctx : FrameCtx} (entry : Frame)
    (destination : Address) (endowment : U256) (init : Bytes)
    (room : entry.stack.size < STACK_DEPTH_LIMIT)
    (initial final : VmWorld Id) (result : StepResult ctx)
    (observed : ((genericCreate ctx entry destination endowment init room).run initial).run =
      .ok (result, final)) : retainedPhi result ≤ entry.gasMeter.phi := by
  unfold genericCreate at observed
  obtain ⟨sender, after, _, reached⟩ :=
    result_of_bind (liftState (getAccount ctx.currentTarget)) _ initial final result observed
  by_cases blocked : sender.balance.toNat < endowment.toNat ∨ sender.nonce = 2^64 - 1
  · simp only [blocked, ite_true] at reached
    rw [result_of_pure _ _ _ _ reached]
    exact Nat.le_refl _
  · simp only [blocked, ite_false] at reached
    by_cases deeper : ctx.depth < STACK_DEPTH_LIMIT
    · simp only [dite_eq_left deeper] at reached
      exact followCreate_retainedPhi { entry with returnData := Bytes.empty } destination endowment
        init room deeper after final result reached
    · simp only [dite_eq_right deeper] at reached
      rw [result_of_pure _ _ _ _ reached]
      exact Nat.le_refl _

private theorem createInMemory_retainedPhi {ctx : FrameCtx} (expanded : Frame)
    (input : CreationInput) (room : expanded.stack.size < STACK_DEPTH_LIMIT)
    (fits : input.size.toNat = 0 ∨
      input.offset.toNat + input.size.toNat ≤ expanded.memory.size) (initial final : VmWorld Id)
    (result : StepResult ctx)
    (observed : ((createInMemory ctx expanded input room fits).run initial).run =
      .ok (result, final)) : retainedPhi result ≤ expanded.gasMeter.phi := by
  unfold createInMemory at observed
  cases salt : input.salt with
  | none =>
    simp only [salt] at observed
    obtain ⟨sender, afterRead, _, read⟩ :=
      result_of_bind (liftState (getAccount ctx.currentTarget)) _ initial final result observed
    obtain ⟨destination, afterHash, _, reached⟩ :=
      result_of_bind (computeContractAddressQ (m := VmM Id) ctx.currentTarget sender.nonce)
        _ afterRead final result read
    exact genericCreate_retainedPhi expanded destination input.endowment _ room afterHash final
      result reached
  | some saltBytes =>
    simp only [salt] at observed
    obtain ⟨destination, afterHash, _, reached⟩ := result_of_bind
      (computeCreate2ContractAddressQ (m := VmM Id) ctx.currentTarget saltBytes _) _ initial final
      result observed
    exact genericCreate_retainedPhi expanded destination input.endowment _ room afterHash final
      result reached

private theorem popFrame_retains_meter (frame : Frame) (value : U256)
    (after : {after : Frame // after.stack.size < STACK_DEPTH_LIMIT})
    (observed : popFrame frame = .ok (value, after)) :
    after.val.gasMeter = frame.gasMeter := by
  rw [popFrame_eq] at observed
  unfold popFrameReference at observed
  split at observed
  · contradiction
  · cases observed
    rfl

private theorem creationOperands_retains_meter (salted : Bool) (frame : Frame)
    (operands : CreationOperands) (observed : creationOperands salted frame = .ok operands) :
    operands.frame.gasMeter = frame.gasMeter := by
  unfold creationOperands at observed
  cases first : popFrame frame with
  | error => simp [Bind.bind, Except.bind, first] at observed
  | ok one =>
    obtain ⟨endowment, one⟩ := one
    simp only [Bind.bind, Except.bind, first] at observed
    have firstEq := popFrame_retains_meter frame endowment one first
    cases second : popFrame one.val with
    | error => simp [second] at observed
    | ok two =>
      obtain ⟨offset, two⟩ := two
      simp only [second] at observed
      have secondEq := popFrame_retains_meter one.val offset two second
      cases third : popFrame two.val with
      | error => simp [third] at observed
      | ok three =>
        obtain ⟨size, three⟩ := three
        simp only [third] at observed
        have thirdEq := popFrame_retains_meter two.val size three third
        cases salted
        · simp only [Bool.false_eq_true, ite_false, Pure.pure, Except.pure, Except.ok.injEq]
            at observed
          subst operands
          exact thirdEq.trans (secondEq.trans firstEq)
        · simp only [ite_true] at observed
          cases fourth : popFrame three.val with
          | error => simp [fourth] at observed
          | ok four =>
            obtain ⟨salt, four⟩ := four
            simp only [fourth, Pure.pure, Except.pure, Except.ok.injEq] at observed
            subst operands
            exact (popFrame_retains_meter three.val salt four fourth).trans
              (thirdEq.trans (secondEq.trans firstEq))

private def paysAccessCost {ctx : FrameCtx} (before : Frame) : StepResult ctx → Prop
  | .continue after => after.gasMeter.phi + ctx.config.costs.createAccess ≤ before.gasMeter.phi
  | .create parent req _ _ =>
    parent.gasMeter.phi + req.gas + ctx.config.costs.createAccess ≤ before.gasMeter.phi
  | _ => True

private theorem halt_paysAccessCost {ctx : FrameCtx} (before halted : Frame)
    (error : ExceptionalHalt) (initial final : VmWorld Id) (result : StepResult ctx)
    (observed : ((pure (.halt halted error) : VmM Id (StepResult ctx)).run initial).run =
      .ok (result, final)) : paysAccessCost before result := by
  rw [result_of_pure _ _ _ _ observed]
  trivial

private theorem createAfterOperands_paysAccessCost {ctx : FrameCtx} (salted : Bool)
    (operands : CreationOperands) (initial final : VmWorld Id) (result : StepResult ctx)
    (observed : ((createAfterOperands salted ctx operands).run initial).run =
      .ok (result, final)) : paysAccessCost operands.frame result := by
  unfold createAfterOperands at observed
  let f := operands.frame
  let size := operands.input.size.toNat
  let window := [(operands.input.offset, operands.input.size)]
  let expansion := calculateGasExtendMemory ctx.config f.memory window
  let cost := createExecutionPrice salted ctx.config expansion.cost size
  cases paid : chargeGas f.gasMeter cost with
  | error error =>
    apply halt_paysAccessCost f f error initial final result
    simpa only [f, size, window, expansion, cost, paid] using observed
  | ok meter =>
    simp only [f, size, window, expansion, cost, paid] at observed
    by_cases oversize : ctx.config.limits.maxInitCodeSize < size
    · apply halt_paysAccessCost f { f with gasMeter := meter } .outOfGas initial final result
      simpa only [size, oversize, ite_true] using observed
    · simp only [size, oversize, ite_false] at observed
      have paidCost := chargeGas_phi f.gasMeter cost meter paid
      change meter.phi + cost = operands.frame.gasMeter.phi at paidCost
      have minimum : ctx.config.costs.createAccess ≤ cost := by
        unfold cost createExecutionPrice
        dsimp only
        split <;> omega
      let memory := f.memory.expand expansion.expandBy
        (calculateGasExtendMemory_aligned ctx.config f.memory window)
      let expanded := { f with gasMeter := meter, memory }
      have retained := createInMemory_retainedPhi expanded operands.input operands.room
        (expanded_window_fits ctx.config f.memory operands.input.offset operands.input.size)
        initial final result observed
      change retainedPhi result ≤ meter.phi at retained
      cases result <;> simp only [paysAccessCost, retainedPhi] at * <;> omega

private theorem createHandler_paysAccessCost (salted : Bool) (ctx : FrameCtx) (frame : Frame)
    (initial final : VmWorld Id) (result : StepResult ctx)
    (observed : ((createHandler salted ctx frame).run initial).run = .ok (result, final)) :
    paysAccessCost frame result := by
  unfold createHandler at observed
  by_cases static : ctx.isStatic = true
  · simp only [static, ite_true] at observed
    exact halt_paysAccessCost frame frame .writeInStaticContext initial final result observed
  · simp only [static] at observed
    cases popped : creationOperands salted frame with
    | error failure =>
      obtain ⟨after, error⟩ := failure
      simp only [popped] at observed
      exact halt_paysAccessCost frame after error initial final result observed
    | ok operands =>
      simp only [popped] at observed
      have progress := createAfterOperands_paysAccessCost salted operands initial final result
        observed
      have meter := creationOperands_retains_meter salted frame operands popped
      cases result with
      | «continue» => simpa only [paysAccessCost, meter] using progress
      | create => simpa only [paysAccessCost, meter] using progress
      | _ => trivial

private theorem resumeAfterCreate_meter_phi (cfg : VmConfig) (parent : Frame) (req : CreateRequest)
    (child : ChildOutcome) (room : parent.stack.size < STACK_DEPTH_LIMIT) :
    (resumeAfterCreate cfg parent req child room).gasMeter.phi =
      parent.gasMeter.phi + child.frame.gasMeter.phi := by
  unfold resumeAfterCreate
  dsimp only
  split
  · rw [creditStateGasRefund_phi]
    exact incorporateChild_phi parent child.frame child.error.isSome child.settled
  · exact incorporateChild_phi parent child.frame child.error.isSome child.settled

private theorem createHandler_resume_paysAccessCost (salted : Bool) (ctx : FrameCtx) (frame : Frame)
    (initial final : VmWorld Id) (parent : Frame) (req : CreateRequest)
    (deeper : ctx.depth < STACK_DEPTH_LIMIT) (room : parent.stack.size < STACK_DEPTH_LIMIT)
    (child : ChildOutcome)
    (observed : ((createHandler salted ctx frame).run initial).run =
      .ok (.create parent req deeper room, final))
    (returned : child.frame.gasMeter.phi ≤
      (childFrame parent req.gas req.stateGasReservoir).gasMeter.phi) :
    (resumeAfterCreate ctx.config parent req child room).gasMeter.phi +
      ctx.config.costs.createAccess ≤ frame.gasMeter.phi := by
  have paid := createHandler_paysAccessCost salted ctx frame initial final _ observed
  change
    parent.gasMeter.phi + req.gas + ctx.config.costs.createAccess ≤ frame.gasMeter.phi at paid
  change child.frame.gasMeter.phi ≤ req.gas + 0 + 0 at returned
  rw [resumeAfterCreate_meter_phi]
  omega

end STFSpec.Vm.Instructions
