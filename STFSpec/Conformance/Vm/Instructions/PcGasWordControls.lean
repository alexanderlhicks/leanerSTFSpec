/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions

/-!
# PC and GAS controls

Library `EthConformance`. Exercise the complete frame results and the distinct
nominal fault sites through the Instructions facade.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.PcGasWordControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (pcPrice gasPrice : Nat) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodePc := pcPrice, opcodeGas := gasPrice, opcodeMsize := 71,
    opcodeGasPrice := 73, opcodeBaseFee := 79 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0, 255], validJumpDestinations (Bytes.ofList [91]),
    1024, by decide, true, true, false, addr 107⟩

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

private def memory : Memory := expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
  right
  rw [expanded_size]
  decide)

private def frame (pc gas : Nat) (stack : Stack) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, stack, memory, ⟨gas, 2^279 + 67, 2^273 + 39, -17, 5, 11⟩,
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

private inductive Expected where
  | denied
  | full
  | site (value : OverflowSite)
  | paid (word : Nat)

private def check (action : Handler Id) (pcPrice gasPrice : Nat)
    (entryPc price grant depth : Nat) (expected : Expected) : Bool := Id.run do
  let words := (List.range depth).map (· + 283)
  let some stack := stackOf words | return false
  let entry := frame entryPc grant stack
  let paid := { entry with gasMeter.gasLeft := grant - price }
  let result := ((action (context pcPrice gasPrice) entry).run world).run
  match result, expected with
  | .error (.u256Overflow .pc), .site .pc
  | .error (.u256Overflow .gasLeft), .site .gasLeft => return true
  | .ok (.halt after .outOfGas, retained), .denied =>
    return frameModel after == frameModel entry && worldModel retained == worldModel world
  | .ok (.halt after .stackOverflow, retained), .full =>
    return frameModel after == frameModel paid && worldModel retained == worldModel world
  | .ok (.continue after, retained), .paid word =>
    let some pushed := stackOf (word :: words) | return false
    return frameModel after == frameModel { paid with stack := pushed, pc := entryPc + 1 } &&
      worldModel retained == worldModel world
  | _, _ => return false

private def limit : Nat := 2^256
private def widePrice : Nat := 2^278 + 53

#guard check pc 7 11 (limit + 1) 7 6 1024 .denied
#guard check pc 7 11 limit 7 7 1024 (.site .pc)
#guard check pc 7 11 limit 7 7 2 (.site .pc)
#guard check pc 7 11 (limit - 1) 7 7 1023 (.paid (limit - 1))
#guard check pc 7 11 17 7 7 1024 .full
#guard check pc 0 11 0 0 0 0 (.paid 0)
#guard check pc widePrice 11 211 widePrice (widePrice + 7) 3 (.paid 211)

#guard check gasLeft 7 (limit + 1) 11 (limit + 1) limit 1024 .denied
#guard check gasLeft 7 11 (limit + 1) 11 (limit + 11) 1024 (.site .gasLeft)
#guard check gasLeft 7 11 (limit + 1) 11 (limit + 11) 2 (.site .gasLeft)
#guard check gasLeft 7 11 (limit + 1) 11 (limit + 10) 1023 (.paid (limit - 1))
#guard check gasLeft 7 11 11 11 (limit + 10) 1024 .full
#guard check gasLeft 7 0 11 0 0 0 (.paid 0)
#guard check gasLeft 7 widePrice (limit + 1) widePrice (widePrice + 7) 3 (.paid 7)

private def pcSignature {m : Type → Type} [Monad m] : Handler m := pc
private def gasSignature {m : Type → Type} [Monad m] : Handler m := gasLeft

end STFSpec.Conformance.Vm.Instructions.PcGasWordControls
