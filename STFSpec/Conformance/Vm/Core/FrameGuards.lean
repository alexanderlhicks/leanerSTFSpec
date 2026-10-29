/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete nontrivial raw frame controls

Library `EthConformance`. Public-only construction with checked stack success,
nonzero written memory, distinct persistent sets, duplicate logs, signed refund
and a program counter above the U256 range. These are raw data controls, not an
execution or whole-Evm refinement.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.FrameGuards
open STFSpec.Vm.Core STFSpec.Base

private def low : Address := Address.ofNat 1
private def high : Address := Address.ofNat 256
private def slotLow : Bytes32 := FixedBytes.ofNat 1
private def slotHigh : Bytes32 := FixedBytes.ofNat 256
private def deleted : AddrSet := (∅ : AddrSet).insert high
private def warm : AddrSet := (∅ : AddrSet).insert low
private def slots : SlotSet := ((∅ : SlotSet).insert (low, slotHigh)).insert (high, slotLow)

-- Addresses compare before slots; same-address pairs compare their complete slot.
#guard compare low high == .lt
#guard compare (low, slotHigh) (high, slotLow) == .lt
#guard compare (low, slotLow) (low, slotHigh) == .lt
#guard (∅ : AddrSet).contains low == false
#guard (∅ : SlotSet).contains (low, slotLow) == false
#guard (deleted ∪ warm).toList == [low, high]
#guard ((slots.insert (low, slotHigh)) ∪
  ((∅ : SlotSet).insert (low, slotLow))).toList ==
    [(low, slotLow), (low, slotHigh), (high, slotLow)]
#guard slots.contains (low, slotLow) == false
#guard slots.contains (high, slotHigh) == false

-- A rejected construction makes these proof obligations fail, rather than defaulting.
private def oneWord : Stack := (Stack.empty.push (U256.ofNat 7)).toOption.get (by decide)
private def words : Stack := (oneWord.push (U256.ofNat 256)).toOption.get (by decide)
private def expanded : Memory := Memory.empty.expand 32 (by decide)
private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl
private def written : Memory := expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
  right
  rw [expanded_size]
  decide)
private def entry : Log :=
  { address := high
    topics := #[Hash32.ofBytes32 slotHigh, Hash32.ofBytes32 slotLow,
      Hash32.ofBytes32 slotHigh]
    data := Bytes.ofList [255, 0, 128] }
private def rope : LogRope := .concat (.leaf [entry]) (.concat .empty (.leaf [entry]))
private def meter : GasMeter :=
  { gasLeft := 3, stateGasLeft := 101, stateGasBaseline := 2, refundCounter := -17,
    stateGasSpilled := 5, stateGasCommittedSpill := 11 }
private def sample : Frame :=
  Frame.mk (2 ^ 300 + 19) words written meter rope deleted
    (Bytes.ofList [0, 255, 128, 0]) warm slots

-- Observe every field completely, using each provider's public model.
#guard sample.pc == 2 ^ 300 + 19
#guard sample.stack.toList.map U256.toNat == [256, 7]
#guard sample.memory.toBytes == [0, 0, 0, 128, 255, 1] ++ List.replicate 26 0
#guard (sample.gasMeter.gasLeft, sample.gasMeter.stateGasLeft,
  sample.gasMeter.stateGasBaseline, sample.gasMeter.refundCounter,
  sample.gasMeter.stateGasSpilled, sample.gasMeter.stateGasCommittedSpill) ==
    (3, 101, 2, (-17 : Int), 5, 11)
#guard (sample.logs.toList.map fun log ↦
  (log.address.toNat, log.topics.toList.map Hash32.toNat, log.data.toList)) ==
    [(256, [256, 1, 256], [255, 0, 128]), (256, [256, 1, 256], [255, 0, 128])]
#guard sample.accountsToDelete.toList.map Address.toNat == [256]
#guard sample.returnData.toList == [0, 255, 128, 0]
#guard sample.accessedAddresses.toList.map Address.toNat == [1]
#guard (sample.accessedStorageKeys.toList.map fun (address, slot) ↦
  (address.toNat, slot.toNat)) == [(1, 256), (256, 1)]

-- Independent snapshots retain the original complete record by ordinary reduction.
private theorem return_update_retains_sample :
    { sample with returnData := Bytes.empty } =
      Frame.mk (2 ^ 300 + 19) words written meter rope deleted Bytes.empty warm slots := by
  rfl

end STFSpec.Conformance.Vm.Core.FrameGuards
