/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Child incorporation controls

Library `EthConformance`. The clients check the complete parent frame and
the public gas and warm-set laws. See `STFSpec/informal/modules/EthVmCore.md` §4.
-/

namespace STFSpec.Conformance.Vm.Core.IncorporateChildControls

open STFSpec.Base STFSpec.Vm.Core

private def returnedMeter (p c : GasMeter) : GasMeter :=
  { p with
    gasLeft := p.gasLeft + c.gasLeft
    stateGasLeft := p.stateGasLeft + c.stateGasLeft
    stateGasSpilled := p.stateGasSpilled + c.stateGasSpilled
    refundCounter := p.refundCounter + c.refundCounter }

private theorem success_frame (p c : Frame) (h : ChildSettled c false) :
    incorporateChild p c false h =
      { p with
        gasMeter := repayStateGasSpill (returnedMeter p.gasMeter c.gasMeter)
        logs := p.logs.append c.logs
        accountsToDelete := p.accountsToDelete.union c.accountsToDelete
        accessedAddresses := p.accessedAddresses.union c.accessedAddresses
        accessedStorageKeys := p.accessedStorageKeys.union c.accessedStorageKeys } :=
  rfl

private theorem failure_frame (p c : Frame) (h : ChildSettled c true) :
    incorporateChild p c true h = { p with gasMeter := returnedMeter p.gasMeter c.gasMeter } :=
  rfl

private theorem signed_refund (p c : Frame) (failed : Bool) (h : ChildSettled c failed) :
    (incorporateChild p c failed h).gasMeter.refundCounter =
      p.gasMeter.refundCounter + c.gasMeter.refundCounter := by
  cases failed <;> rfl

private theorem failed_child_refund (p c : Frame) (h : ChildSettled c true) :
    (incorporateChild p c true h).gasMeter.refundCounter = p.gasMeter.refundCounter := by
  have discarded : c.gasMeter.refundCounter = 0 := h.2.2.1
  rw [signed_refund, discarded, Int.add_zero]

private theorem potential (p c : Frame) (failed : Bool) (h : ChildSettled c failed) :
    (incorporateChild p c failed h).gasMeter.phi = p.gasMeter.phi + c.gasMeter.phi :=
  incorporateChild_phi p c failed h

private theorem chronological_logs (p c : Frame) (h : ChildSettled c false) :
    (incorporateChild p c false h).logs.toList = p.logs.toList ++ c.logs.toList :=
  LogRope.toList_append p.logs c.logs

private theorem copied_warm_sets (p c : Frame) (h : ChildSettled c false)
    (addresses : ∀ a, a ∈ p.accessedAddresses → a ∈ c.accessedAddresses)
    (slots : ∀ k, k ∈ p.accessedStorageKeys → k ∈ c.accessedStorageKeys) :
    (incorporateChild p c false h).accessedAddresses = c.accessedAddresses ∧
      (incorporateChild p c false h).accessedStorageKeys = c.accessedStorageKeys :=
  ⟨incorporateChild_accessedAddresses_of_subset p c h addresses,
    incorporateChild_accessedStorageKeys_of_subset p c h slots⟩

private def addressSet (entries : List Nat) : AddrSet :=
  entries.foldl (fun result value ↦ result.insert (Address.ofNat value)) ∅

private def slotSet (entries : List (Nat × Nat)) : SlotSet :=
  entries.foldl (fun result (addr, key) ↦ result.insert (Address.ofNat addr, FixedBytes.ofNat key)) ∅

private def log (n : Nat) : Log :=
  ⟨Address.ofNat n, #[Hash32.ofBytes32 (FixedBytes.ofNat (n + 1))],
    Bytes.ofList [0, UInt8.ofNat n, 255]⟩

private def parent (meter : GasMeter) : Frame :=
  let stack := (Stack.empty.push U256.max).toOption.getD Stack.empty
  ⟨2 ^ 260 + 3, stack, Memory.empty.expand 32 (by decide), meter,
    .concat (.leaf [log 2]) (.leaf [log 3]),
    addressSet [5, 7], Bytes.ofList [11, 0, 128],
    addressSet [13, 17], slotSet [(23, 29), (31, 37)]⟩

private inductive WarmLayout where
  | overlapping
  | copied
  | disjoint

private def child (meter : GasMeter) (layout : WarmLayout) : Frame :=
  let deleted := match layout with
    | .overlapping | .copied => addressSet [7, 11]
    | .disjoint => addressSet [11]
  let addresses := match layout with
    | .overlapping => addressSet [17, 19]
    | .copied => addressSet [13, 17, 19]
    | .disjoint => addressSet [19]
  let slots := match layout with
    | .overlapping => slotSet [(31, 37), (41, 43)]
    | .copied => slotSet [(23, 29), (31, 37), (41, 43)]
    | .disjoint => slotSet [(41, 43)]
  ⟨47, Stack.empty, Memory.empty.expand 64 (by decide), meter,
    .concat .empty (.leaf [log 53, log 2]), deleted, Bytes.ofList [59, 0, 255], addresses, slots⟩

private def frameModel (f : Frame) :=
  let g := f.gasMeter
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (g.gasLeft, g.stateGasLeft, g.stateGasBaseline, g.refundCounter,
      g.stateGasSpilled, g.stateGasCommittedSpill),
    f.logs.toList.map (fun l ↦
      (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (addr, key) ↦ (addr.toNat, key.toNat)))

private def runCase (parentMeter childMeter expected : GasMeter) (failed : Bool)
    (layout : WarmLayout) : Bool :=
  let p := parent parentMeter
  let c := child childMeter layout
  let wanted :=
    if failed then { p with gasMeter := expected }
    else { p with
      gasMeter := expected
      logs := .leaf [log 2, log 3, log 53, log 2]
      accountsToDelete := addressSet [5, 7, 11]
      accessedAddresses := addressSet [13, 17, 19]
      accessedStorageKeys := slotSet [(23, 29), (31, 37), (41, 43)] }
  if admitted : ChildSettled c failed then
    frameModel (incorporateChild p c failed admitted) == frameModel wanted
  else false

#guard runCase ⟨19, 37, 4, -13, 5, 11⟩ ⟨7, 3, 9, -4, 7, 0⟩
  ⟨38, 28, 4, -17, 0, 11⟩ false .overlapping
#guard runCase ⟨19, 1, 4, -13, 5, 11⟩ ⟨7, 2, 9, 6, 7, 0⟩
  ⟨29, 0, 4, -7, 9, 11⟩ false .overlapping
#guard runCase ⟨19, 0, 4, -13, 5, 11⟩ ⟨0, 0, 9, 6, 7, 0⟩
  ⟨19, 0, 4, -7, 12, 11⟩ false .overlapping
#guard runCase ⟨19, 9, 4, -13, 0, 11⟩ ⟨0, 2, 9, 6, 0, 0⟩
  ⟨19, 11, 4, -7, 0, 11⟩ false .overlapping
#guard runCase ⟨4, 2, 3, -19, 11, 13⟩ ⟨5, 7, 17, 37, 19, 0⟩
  ⟨18, 0, 3, 18, 21, 13⟩ false .copied
#guard runCase ⟨9, 6, 3, 19, 1, 23⟩ ⟨30, 11, 7, -43, 2, 0⟩
  ⟨42, 14, 3, -24, 0, 23⟩ false .disjoint
#guard runCase ⟨19, 37, 4, -13, 5, 11⟩ ⟨7, 9, 9, 0, 0, 0⟩
  ⟨26, 46, 4, -13, 5, 11⟩ true .overlapping
#guard runCase ⟨19, 1, 4, -13, 5, 11⟩ ⟨0, 9, 9, 0, 0, 0⟩
  ⟨19, 10, 4, -13, 5, 11⟩ true .disjoint

end STFSpec.Conformance.Vm.Core.IncorporateChildControls
