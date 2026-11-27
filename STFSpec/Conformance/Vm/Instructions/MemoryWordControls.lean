/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# Fixed-width memory instruction controls

Library `EthConformance`. The guards check complete frames and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.MemoryWordControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private structure Prices where
  load : Nat
  store : Nat
  store8 : Nat
  zero : Nat
  memoryPerWord : Nat

private def context (prices : Prices) (static : Bool) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    veryLow := 97
    opcodeMloadBase := prices.load
    opcodeMstoreBase := prices.store
    opcodeMstore8Base := prices.store8
    zero := prices.zero
    memoryPerWord := prices.memoryPerWord }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0x51, 0x52, 0x53],
    validJumpDestinations (Bytes.ofList [91, 0, 91]),
    1024, by decide, true, static, false, addr 107⟩

private def world : VmWorld Id :=
  let pre : PreState Id := ⟨fun _ ↦ .ok none, fun _ _ ↦ .ok (U256.ofNat 109),
    fun _ ↦ .ok (ByteArray.mk #[0, 255, 128]), fun _ ↦ .ok (hash 113)⟩
  let block : BlockState Id :=
    ⟨pre, ⟨hash 127, hash 131, hash 137, hash 139⟩,
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (addr 149) none,
      ⟨157, ∅, ∅⟩, ∅, ⟨163, ∅, ∅⟩, ∅, ∅, ∅, ∅, ∅, ∅,
      some (2 ^ 290 + 167)⟩
  let rev : TxRevertible :=
    ⟨∅, ⟨173, ∅, ∅⟩, ∅, ⟨179, ∅, ∅⟩, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
        (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193)⟩
  let obs : TxObs :=
    ⟨(∅ : Std.HashSet Address).insert (addr 197), ∅, ∅,
      (∅ : Std.HashSet Address).insert (addr 199)⟩
  ⟨⟨block, rev, obs⟩⟩

private def expanded : Memory := Memory.empty.expand 32 (by decide)

private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def memory : Memory := expanded.write 0 (Bytes.ofList ((List.range 32).map UInt8.ofNat)) (by
  right
  rw [expanded_size]
  decide)

private def frame (pc gas : Nat) (stack : Stack) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, stack, memory, ⟨gas, 101, 2, -17, 5, 11⟩,
    .concat (.leaf [entry]) (.concat .empty (.leaf [entry])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    (∅ : AddrSet).insert (addr 1),
    ((∅ : SlotSet).insert (addr 1, FixedBytes.ofNat 256)).insert (addr 256, FixedBytes.ofNat 1)⟩

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map (fun l ↦
      (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def worldModel (w : VmWorld Id) :=
  let tx := w.tx
  let storage := ((tx.block.preState.getStorage (addr 1) (FixedBytes.ofNat 2)).toOption).map
    U256.toNat
  (tx.block.accountOrder.next, tx.block.storageAddressOrder.next,
    tx.rev.accountOrder.next, tx.rev.storageAddressOrder.next,
    tx.block.oldestAncestorOffset, tx.block.consts.emptyCodeHash.toNat,
    storage, tx.obs.createdAccounts.contains (addr 199), tx.obs.accountReads.contains (addr 197))

private def stackOf (words : List Nat) : Option Stack :=
  words.reverse.foldlM (fun stack word ↦ (stack.push (U256.ofNat word)).toOption) Stack.empty

private structure Expected where
  pc : Nat
  gas : Nat
  stack : List Nat
  memory : List UInt8
  fault : Option ExceptionalHalt

private def runCase (run : Handler Id) (prices : Prices) (static : Bool) (gas pc : Nat)
    (words : List Nat) (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some desired := stackOf expected.stack | return false
  let expectedFrame := frameModel (frame expected.pc expected.gas desired)
  let before := frame pc gas stack
  let result := ((run (context prices static) before).run world).run
  match result, expected.fault with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.continue after, retained), none =>
    return frameModel { after with memory } == expectedFrame &&
      after.memory.toBytes == expected.memory && worldModel retained == worldModel world &&
      frameModel before == frameModel (frame pc gas stack)
  | _, _ => return false

private def priced : Prices := ⟨11, 19, 29, 7, 5⟩
private def initial : List UInt8 := (List.range 32).map UInt8.ofNat
private def inert : List UInt8 := initial ++ List.replicate 32 0
private def maximum : Nat := 2 ^ 256 - 1
private def word : Nat := 2 ^ 255 + 0x1279
private def wordBytes : List UInt8 := [128] ++ List.replicate 29 0 ++ [18, 121]
private def initialWord : Nat := (List.range 32).foldl (fun value byte ↦ 256 * value + byte) 0

#guard runCase mload priced true 0 7 [] ⟨7, 0, [], initial, some .stackUnderflow⟩
#guard runCase mload priced false 17 7 [0, 53] ⟨7, 17, [53], initial, some .outOfGas⟩
#guard runCase mload priced true 18 7 (0 :: List.range 1023)
  ⟨8, 0, initialWord :: List.range 1023, initial, none⟩
#guard runCase mload priced true 22 7 [30, 53] ⟨7, 22, [53], initial, some .outOfGas⟩
#guard runCase mload priced true 23 maximum [30, 53]
  ⟨2 ^ 256, 0, [(30 * 256 + 31) * 256 ^ 30, 53], inert, none⟩
#guard runCase mload priced false 100 7 [maximum, 53]
  ⟨7, 100, [53], initial, some .outOfGas⟩

#guard runCase mstore priced false 0 7 [] ⟨7, 0, [], initial, some .stackUnderflow⟩
#guard runCase mstore priced true 0 7 [maximum] ⟨7, 0, [], initial, some .stackUnderflow⟩
#guard runCase mstore priced true 25 7 [0, word, 53] ⟨7, 25, [53], initial, some .outOfGas⟩
#guard runCase mstore priced false 26 7 [0, word, 53] ⟨8, 0, [53], wordBytes, none⟩
#guard runCase mstore priced true 30 7 [31, word, 53] ⟨7, 30, [53], initial, some .outOfGas⟩
#guard runCase mstore priced true 33 maximum [31, word, 53]
  ⟨2 ^ 256, 2, [53], initial.take 31 ++ wordBytes ++ [0], none⟩
#guard runCase mstore priced false 100 7 [maximum, word, 53]
  ⟨7, 100, [53], initial, some .outOfGas⟩

#guard runCase mstore8 priced true 0 7 [] ⟨7, 0, [], initial, some .stackUnderflow⟩
#guard runCase mstore8 priced false 0 7 [maximum] ⟨7, 0, [], initial, some .stackUnderflow⟩
#guard runCase mstore8 priced true 35 7 [31, word, 53] ⟨7, 35, [53], initial, some .outOfGas⟩
#guard runCase mstore8 priced true 36 7 [31, word, 53]
  ⟨8, 0, [53], initial.take 31 ++ [121], none⟩
#guard runCase mstore8 priced false 41 7 [32, word, 53]
  ⟨8, 0, [53], initial ++ [121] ++ List.replicate 31 0, none⟩
#guard runCase mstore8 priced true 100 7 [maximum, word, 53]
  ⟨7, 100, [53], initial, some .outOfGas⟩
#guard runCase mstore8 ⟨11, 19, 0, 0, 0⟩ true 0 7 [32, word, 53]
  ⟨8, 0, [53], initial ++ [121] ++ List.replicate 31 0, none⟩

private def handlerTypes {m : Type → Type} [Monad m] : Handler m × Handler m × Handler m :=
  (mload, mstore, mstore8)

private theorem load_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (tail : Stack) :
    let price := ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost
    let run := ((mload ctx f).run w).run
    (f.stack.pop = .error .stackUnderflow →
      run = pure (Except.ok (.halt f .stackUnderflow, w))) ∧
    (f.stack.pop = .ok (off, tail) → f.gasMeter.gasLeft < price →
      run = pure (Except.ok (.halt { f with stack := tail } .outOfGas, w))) :=
  ⟨mload_run_underflow ctx f w, mload_run_oog ctx f w off tail⟩

private theorem mstore_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack) :
    let price := ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost
    let run := ((mstore ctx f).run w).run
    (f.stack.pop = .error .stackUnderflow →
      run = pure (Except.ok (.halt f .stackUnderflow, w))) ∧
    (f.stack.pop = .ok (off, s₁) → s₁.pop = .error .stackUnderflow →
      run = pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))) ∧
    (f.stack.pop = .ok (off, s₁) → s₁.pop = .ok (word, s₂) → f.gasMeter.gasLeft < price →
      run = pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))) :=
  ⟨mstore_run_first_underflow ctx f w, mstore_run_second_underflow ctx f w off s₁,
    mstore_run_oog ctx f w off word s₁ s₂⟩

private theorem mstore8_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off word : U256) (s₁ s₂ : Stack) :
    let price := ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost
    let run := ((mstore8 ctx f).run w).run
    (f.stack.pop = .error .stackUnderflow →
      run = pure (Except.ok (.halt f .stackUnderflow, w))) ∧
    (f.stack.pop = .ok (off, s₁) → s₁.pop = .error .stackUnderflow →
      run = pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))) ∧
    (f.stack.pop = .ok (off, s₁) → s₁.pop = .ok (word, s₂) → f.gasMeter.gasLeft < price →
      run = pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))) :=
  ⟨mstore8_run_first_underflow ctx f w, mstore8_run_second_underflow ctx f w off s₁,
    mstore8_run_oog ctx f w off word s₁ s₂⟩

private theorem mload_paid {m : Type → Type} [Monad m]
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
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) :=
  mload_run_success ctx f w off tail popped enough

private theorem mload_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mload ctx f).run w).run = .ok (.continue f', w')) :
    let price := ctx.config.costs.opcodeMloadBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost
    f'.gasMeter.phi + price = f.gasMeter.phi ∧
      (1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨mload_continue_phi ctx f f' w w' off tail popped ran,
    mload_continue_progress ctx f f' w w' off tail popped ran⟩

private theorem mstore_paid {m : Type → Type} [Monad m]
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
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) :=
  mstore_run_success ctx f w off word s₁ s₂ first second enough

private theorem mstore_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore ctx f).run w).run = .ok (.continue f', w')) :
    let price := ctx.config.costs.opcodeMstoreBase +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 32)]).cost
    f'.gasMeter.phi + price = f.gasMeter.phi ∧
      (1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨mstore_continue_phi ctx f f' w w' off tail popped ran,
    mstore_continue_progress ctx f f' w w' off tail popped ran⟩

private theorem mstore8_paid {m : Type → Type} [Monad m]
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
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) :=
  mstore8_run_success ctx f w off word s₁ s₂ first second enough

private theorem mstore8_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (off : U256) (tail : Stack) (popped : f.stack.pop = .ok (off, tail))
    (ran : ((mstore8 ctx f).run w).run = .ok (.continue f', w')) :
    let price := ctx.config.costs.opcodeMstore8Base +
      (calculateGasExtendMemory ctx.config f.memory [(off, U256.ofNat 1)]).cost
    f'.gasMeter.phi + price = f.gasMeter.phi ∧
      (1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨mstore8_continue_phi ctx f f' w w' off tail popped ran,
    mstore8_continue_progress ctx f f' w w' off tail popped ran⟩

end STFSpec.Conformance.Vm.Instructions.MemoryWordControls
