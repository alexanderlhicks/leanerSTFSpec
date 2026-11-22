/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Mutable child frame clients

Library `EthConformance`. Private clients check every initialized field, the
exact grants, and the committed-spill clause at child entry.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.ChildFrameCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private theorem construction (parent : Frame) (gas reservoir : Nat) :
    childFrame parent gas reservoir =
      Frame.mk 0 Stack.empty Memory.empty (GasMeter.mk gas reservoir reservoir 0 0 0)
        LogRope.empty ∅ Bytes.empty parent.accessedAddresses parent.accessedStorageKeys := rfl

private theorem initial_committed_spill (parent : Frame) (gas reservoir : Nat) :
    ChildSettled (childFrame parent gas reservoir) false := ⟨rfl, True.intro⟩

private def warmer : Address := Address.ofNat 256
private def deleted : Address := Address.ofNat 257
private def slot : Bytes32 := FixedBytes.ofNat 258
private def expanded : Memory := Memory.empty.expand 32 (by decide)
private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def parent : Frame :=
  { pc := 17
    stack := (Stack.empty.push (U256.ofNat 19)).toOption.get (by decide)
    memory := expanded.write 2 (Bytes.ofList [23]) (by
      right
      rw [expanded_size]
      decide)
    gasMeter := GasMeter.mk 29 31 37 (-41) 43 47
    logs := .leaf [{ address := deleted, topics := #[], data := Bytes.ofList [53] }]
    accountsToDelete := (∅ : AddrSet).insert deleted
    returnData := Bytes.ofList [59]
    accessedAddresses := (∅ : AddrSet).insert warmer
    accessedStorageKeys := (∅ : SlotSet).insert (deleted, slot) }

private def zeroGrants : Frame := childFrame parent 0 0
private def largeGas : Nat := 2 ^ 300 + 61
private def largeReservoir : Nat := 2 ^ 320 + 67
private def largeGrants : Frame := childFrame parent largeGas largeReservoir

#guard zeroGrants.pc == 0
#guard zeroGrants.stack.toList.isEmpty
#guard zeroGrants.memory.toBytes.isEmpty
#guard zeroGrants.logs.toList.isEmpty
#guard zeroGrants.accountsToDelete.toList.isEmpty
#guard zeroGrants.returnData.toList.isEmpty
#guard zeroGrants.accessedAddresses.toList == [warmer]
#guard zeroGrants.accessedStorageKeys.toList == [(deleted, slot)]

private def meterFields (frame : Frame) : Nat × Nat × Nat × Int × Nat × Nat :=
  let meter := frame.gasMeter
  (meter.gasLeft, meter.stateGasLeft, meter.stateGasBaseline, meter.refundCounter,
    meter.stateGasSpilled, meter.stateGasCommittedSpill)

#guard meterFields zeroGrants == (0, 0, 0, 0, 0, 0)
#guard meterFields largeGrants == (largeGas, largeReservoir, largeReservoir, 0, 0, 0)
#guard meterFields (childFrame parent 0 largeReservoir) ==
  (0, largeReservoir, largeReservoir, 0, 0, 0)
#guard meterFields (childFrame parent largeGas 0) == (largeGas, 0, 0, 0, 0, 0)

end STFSpec.Conformance.Vm.Instructions.ChildFrameCallerProofs
