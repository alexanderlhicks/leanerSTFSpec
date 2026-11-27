/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization

/-!
# EXTCODECOPY controls

Library `EthConformance`. Check complete frames and ordered account and code
observations through the facade. See EthVmInstructions §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.ExtCodeCopyControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def target := addr 29
private def codeHash := hash 67
private def emptyCodeHash := hash 71
private def missingNode := hash 73
private def word : Nat := 2 ^ 255 + 2 ^ 192 + 29
private def maxWord : Nat := 2 ^ 256 - 1
private def delegateMarker : List UInt8 := [0xef, 1, 0] ++ List.replicate 20 0x97
private abbrev Recording := StateT (List (Nat × Nat)) Id

private inductive CaseRoute where
  | ordinary
  | absent
  | accountFault
  | codeFault

private def accountProvider (route : CaseRoute) (address : Address) :
    Recording (Except WitnessError (Option Account)) := do
  modify (fun prior ↦ prior ++ [(1, address.toNat)])
  match route with
  | .absent => pure (.ok none)
  | .accountFault => pure (.error (.missing (.node missingNode)))
  | _ => pure (.ok (some ⟨0, U256.zero, codeHash⟩))

private def codeProvider (route : CaseRoute) (key : Hash32) :
    Recording (Except WitnessError ByteArray) := do
  modify (fun prior ↦ prior ++ [(2, key.toNat)])
  match route with
  | .codeFault => pure (.error (.missing (.code codeHash)))
  | _ => pure (.ok (Bytes.ofList delegateMarker).toByteArray)

private def world (route : CaseRoute) : VmWorld Recording :=
  let provider : PreState Recording := ⟨accountProvider route,
    fun _ _ ↦ pure (.ok U256.zero), codeProvider route, fun _ ↦ pure (.ok (hash 83))⟩
  let block := BlockState.new provider ⟨emptyCodeHash, hash 89, hash 97, hash 101⟩
  let tx := TxState.new { block with oldestAncestorOffset := some (2 ^ 265 + 103) }
  let tx : TxState Recording := { tx with
    rev.codeWrites := tx.rev.codeWrites.insert emptyCodeHash (Bytes.ofList [0x77, 0x89]).toByteArray
    obs.accountReads := tx.obs.accountReads.insert (addr 107)
    obs.codeReads := tx.obs.codeReads.insert (hash 109)
    obs.createdAccounts := tx.obs.createdAccounts.insert (addr 113) }
  ⟨tx⟩

private def context (static : Bool) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    warmAccess := 11, coldAccountAccess := 37, opcodeCopyPerWord := 17
    zero := 19, memoryPerWord := 5 }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 3, 5, #[hash 7], addr 11, 13, 17, U256.ofNat 19, FixedBytes.ofNat 23,
      U64.ofNat 31, hash 37, U64.ofNat 41⟩
  let tx : TransactionEnvironment :=
    ⟨addr 43, addr 47, true, Bytes.ofList [0, 128], U256.ofNat 53, 59, 61,
      79, 127, 131, ∅, ∅, #[], #[], some 0, some (hash 137)⟩
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    block, tx, addr 139, addr 149, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0x3c], validJumpDestinations (Bytes.ofList [0x3c]),
    1024, by decide, true, static, false, addr 151⟩

private def initial : List UInt8 := (List.range 32).map UInt8.ofNat
private def expanded : Memory := Memory.empty.expand 32 (by decide)

private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def memory : Memory := expanded.write 0 (Bytes.ofList initial) (by
  right
  rw [expanded_size]
  decide)

private def stackOf (words : List Nat) : Option Stack :=
  words.reverse.foldlM (fun stack word ↦ (stack.push (U256.ofNat word)).toOption) Stack.empty

private def frame (pc gas : Nat) (stack : Stack) (warm : Bool) : Frame :=
  let log : Log := ⟨addr 157, #[hash 163, hash 167], Bytes.ofList [0x89, 0, 0xff]⟩
  let addresses := (∅ : AddrSet).insert (addr 173)
  ⟨pc, stack, memory, ⟨gas, 179, 2, -17, 5, 11⟩, .concat (.leaf [log]) .empty,
    (∅ : AddrSet).insert (addr 181), Bytes.ofList [0, 183, 0xff],
    if warm then addresses.insert target else addresses,
    (∅ : SlotSet).insert (addr 191, FixedBytes.ofNat 193)⟩

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map (fun l ↦ (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def worldModel (w : VmWorld Recording) :=
  let tx := w.tx
  (tx.block.oldestAncestorOffset, tx.block.consts.emptyCodeHash.toNat,
    tx.rev.codeWrites.toList.map (fun (key, value) ↦ (key.toNat, value.data.toList)),
    tx.obs.accountReads.toList.map Address.toNat |>.mergeSort (· ≤ ·),
    tx.obs.codeReads.toList.map Hash32.toNat |>.mergeSort (· ≤ ·),
    tx.obs.createdAccounts.toList.map Address.toNat |>.mergeSort (· ≤ ·))

private inductive ExpectedOutcome where
  | underflow
  | denied
  | accountFault
  | codeFault
  | success

private structure Expected where
  outcome : ExpectedOutcome
  pc : Nat
  gas : Nat
  stack : List Nat
  memory : List UInt8
  warm : Bool
  trace : List (Nat × Nat)

private def control (route : CaseRoute) (static warm : Bool) (pc gas : Nat) (words : List Nat)
    (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some desiredStack := stackOf expected.stack | return false
  let before := frame pc gas stack warm
  let prior := world route
  let action := ((extcodecopy (context static) before).run prior).run
  let (result, trace) := action.run []
  let desiredFrame := frameModel (frame expected.pc expected.gas desiredStack expected.warm)
  let frameAgrees := fun after ↦
    frameModel { after with memory } == desiredFrame && after.memory.toBytes == expected.memory
  let agrees := match result, expected.outcome with
    | .ok (.halt after .stackUnderflow, retained), .underflow
    | .ok (.halt after .outOfGas, retained), .denied =>
      frameAgrees after && worldModel retained == worldModel prior
    | .error (.state (.witness (.missing (.node key)))), .accountFault => key == missingNode
    | .error (.state (.witness (.missing (.code key)))), .codeFault => key == codeHash
    | .ok (.continue after, retained), .success =>
      let tx := prior.tx
      let obs := { tx.obs with
        accountReads := tx.obs.accountReads.insert target
        codeReads := if expected.trace.length == 2 then tx.obs.codeReads.insert codeHash else tx.obs.codeReads }
      frameAgrees after && worldModel retained == worldModel ⟨{ tx with obs }⟩
    | _, _ => false
  return agrees && trace == expected.trace && frameModel before == frameModel (frame pc gas stack warm)

private def providerTrace : List (Nat × Nat) := [(1, 29), (2, 67)]
private def untouched := initial.take 27
private def copiedMarker := untouched ++ delegateMarker ++ List.replicate 14 0

#guard control .ordinary false false 7 0 [] ⟨.underflow, 7, 0, [], initial, false, []⟩
#guard control .ordinary true false 7 0 [word] ⟨.underflow, 7, 0, [], initial, false, []⟩
#guard control .ordinary false false 7 0 [word, 27] ⟨.underflow, 7, 0, [], initial, false, []⟩
#guard control .ordinary true false 7 0 [word, 27, 0] ⟨.underflow, 7, 0, [], initial, false, []⟩
#guard control .ordinary false false 7 88 [word, 27, 0, 27, 53]
  ⟨.denied, 7, 88, [53], initial, true, []⟩
#guard control .ordinary true true 7 62 [word, 27, 0, 27, 53]
  ⟨.denied, 7, 62, [53], initial, true, []⟩
#guard control .ordinary true false maxWord 89 [word, 27, 0, 27, 53]
  ⟨.success, 2 ^ 256, 0, [53], copiedMarker, true, providerTrace⟩
#guard control .ordinary false true 7 63 ([word, 27, 0, 27] ++ List.range 1020)
  ⟨.success, 8, 0, List.range 1020, copiedMarker, true, providerTrace⟩
#guard control .ordinary true false 7 89 [word, 31, maxWord, 3]
  ⟨.success, 8, 0, [], initial.take 31 ++ List.replicate 33 0, true, providerTrace⟩
#guard control .ordinary false false 7 67 [word, maxWord, maxWord, 0]
  ⟨.success, 8, 0, [], initial, true, providerTrace⟩
#guard control .absent true false 7 89 [word, 31, 0, 3]
  ⟨.success, 8, 0, [], initial.take 31 ++ List.replicate 33 0, true, [(1, 29)]⟩
#guard control .accountFault false false 7 89 [word, 27, 0, 27, 53]
  ⟨.accountFault, 7, 0, [53], [], true, [(1, 29)]⟩
#guard control .codeFault true true 7 63 [word, 27, 0, 27, 53]
  ⟨.codeFault, 7, 0, [53], [], true, providerTrace⟩
#guard control .codeFault false false 7 67 [word, maxWord, maxWord, 0]
  ⟨.codeFault, 7, 0, [], [], true, providerTrace⟩

end STFSpec.Conformance.Vm.Instructions.ExtCodeCopyControls
