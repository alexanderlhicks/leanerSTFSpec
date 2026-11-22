/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Lean.Data.Json

/-!
# Transaction storage clear controls

Library `EthConformance`. See `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.DestroyStorageGuards

open STFSpec.Base STFSpec.State Lean

private structure Trace (α : Type) where
  result : α
  effects : List Nat

private instance : Monad Trace where
  pure value := ⟨value, [0]⟩
  bind x f :=
    let y := f x.result
    ⟨y.result, x.effects ++ [1] ++ y.effects⟩

private def target : Address := Address.ofNat (2 ^ 160 - 1)
private def other : Address := Address.ofNat (2 ^ 159 - 1)
private def slot0 : Bytes32 := FixedBytes.ofNat (2 ^ 256 - 1)
private def slot1 : Bytes32 := FixedBytes.ofNat (2 ^ 255 - 1)
private def slot2 : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 19)
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def bytes (ns : List Nat) : ByteArray := ⟨(ns.map UInt8.ofNat).toArray⟩

private def failProvider {α : Type} (tag : Nat) : Trace (Except WitnessError α) :=
  ⟨.error (.missing (.code (hash tag))), [tag]⟩

private def provider : PreState Trace where
  getAccount? := fun _ ↦ failProvider 2
  getStorage := fun _ _ ↦ failProvider 3
  getCode := fun _ ↦ failProvider 4
  stateRoot := fun _ ↦ failProvider 5

private abbrev SlotMap := Std.ExtTreeMap Bytes32 U256

private def slotMap (xs : List (Bytes32 × Nat)) : SlotMap :=
  xs.foldl (fun writes (key, value) ↦ writes.insert key (U256.ofNat value)) ∅

private def order {K : Type} [Ord K] [Std.TransOrd K] (keys : List K) : WriteOrder K :=
  keys.foldl WriteOrder.record WriteOrder.empty

private def block : BlockState Trace :=
  { BlockState.new provider ⟨hash 11, hash 12, hash 13, hash 14⟩ with
    accountWrites := (∅ : Std.ExtTreeMap Address (Option Account)).insert target
      (some ⟨2 ^ 143, U256.ofNat 37, hash 29⟩)
    accountOrder := order [target]
    storageWrites := ((∅ : Std.ExtTreeMap Address SlotMap).insert target (slotMap [(slot1, 31)]))
      |>.insert other (slotMap [(slot0, 17)])
    storageAddressOrder := order [target, other]
    storageSlotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
      |>.insert target (order [slot1]) |>.insert other (order [slot0])
    storageClears := (∅ : Std.ExtTreeSet Address).insert other
    codeWrites := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (hash 8) (bytes [0, 255])
    accountReads := (∅ : Std.HashSet Address).insert target
    storageReads := (∅ : Std.HashSet (Address × Bytes32)).insert (target, slot2)
    codeReads := (∅ : Std.HashSet Hash32).insert (hash 9)
    oldestAncestorOffset := some (2 ^ 143) }

private def oldReads : Std.HashSet (Address × Bytes32) :=
  (∅ : Std.HashSet (Address × Bytes32)).insert (other, slot1)

private def initial (patch : Option (List (Bytes32 × Nat))) (existingClear existingRead : Bool) :
    TxState Trace :=
  let otherPatch := (∅ : Std.ExtTreeMap Address SlotMap)
    |>.insert other (slotMap [(slot0, 53), (slot2, 61)])
  let otherOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
    |>.insert other (order [slot0, slot2])
  let addresses := order [other]
  let clears := (∅ : Std.ExtTreeSet Address).insert other
  { block
    rev := {
      accountWrites := (∅ : Std.ExtTreeMap Address (Option Account)).insert other none
      accountOrder := order [other]
      storageWrites := patch.elim otherPatch (fun xs ↦ otherPatch.insert target (slotMap xs))
      storageAddressOrder := patch.elim addresses (fun _ ↦ addresses.record target)
      storageSlotOrder := patch.elim otherOrder
        (fun xs ↦ otherOrder.insert target (order (xs.map Prod.fst)))
      codeWrites := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (hash 10) (bytes [255, 0, 1])
      storageClears := if existingClear then clears.insert target else clears
      transient := (∅ : Std.ExtTreeMap (Address × Bytes32) U256)
        |>.insert (target, slot0) (U256.ofNat 47) }
    obs := {
      accountReads := (∅ : Std.HashSet Address).insert other
      storageReads := if existingRead then oldReads.insert (target, slot0) else oldReads
      codeReads := (∅ : Std.HashSet Hash32).insert (hash slot0.toNat)
      createdAccounts := (∅ : Std.HashSet Address).insert target } }

private def observeOrder {K : Type} [Ord K] [Std.TransOrd K]
    (key : K → Nat) (o : WriteOrder K) : Nat × List (Nat × Nat) × List (Nat × Nat) :=
  (o.next, o.positions.toList.map (fun (k, p) ↦ (key k, p)),
    o.keysByPosition.toList.map (fun (p, k) ↦ (p, key k)))

private def observeOrders (accountOrder addressOrder : WriteOrder Address)
    (slotOrders : Std.ExtTreeMap Address (WriteOrder Bytes32)) : Json :=
  toJson (observeOrder Address.toNat accountOrder, observeOrder Address.toNat addressOrder,
    slotOrders.toList.map (fun (a, o) ↦ (a.toNat, observeOrder FixedBytes.toNat o)))

private def observeAccounts (xs : Std.ExtTreeMap Address (Option Account)) : Json :=
  toJson (xs.toList.map (fun (a, value) ↦
    (a.toNat, value.map (fun (acc : Account) ↦ (acc.nonce, acc.balance.toNat, acc.codeHash.toNat)))))

private def observeSlots (xs : Std.ExtTreeMap Address SlotMap) : Json :=
  toJson (xs.toList.map (fun (a, patch) ↦
    (a.toNat, patch.toList.map (fun (entry : Bytes32 × U256) ↦ (entry.1.toNat, entry.2.toNat)))))

private def observeCode (xs : Std.ExtTreeMap Hash32 ByteArray) : Json :=
  toJson (xs.toList.map (fun (h, code) ↦ (h.toNat, code.toList.map UInt8.toNat)))

private def observeStorageReads (xs : Std.HashSet (Address × Bytes32)) : List (Nat × Nat) :=
  (xs.toList.map (fun (a, k) ↦ (a.toNat, k.toNat))).mergeSort
    (fun (a, k) (b, l) ↦ a < b || (a == b && k ≤ l))

private def observeReadKeys {K : Type} [BEq K] [Hashable K]
    (key : K → Nat) (xs : Std.HashSet K) : Json :=
  toJson ((xs.toList.map key).mergeSort (· ≤ ·))

private def observeBlock (b : BlockState Trace) : Json :=
  Json.mkObj [
    ("accountWrites", observeAccounts b.accountWrites),
    ("storageWrites", observeSlots b.storageWrites),
    ("codeWrites", observeCode b.codeWrites),
    ("storageClears", toJson (b.storageClears.toList.map Address.toNat)),
    ("accountReads", observeReadKeys Address.toNat b.accountReads),
    ("storageReads", toJson (observeStorageReads b.storageReads)),
    ("codeReads", observeReadKeys Hash32.toNat b.codeReads),
    ("oldestAncestorOffset", toJson b.oldestAncestorOffset)]

private def observeTx (t : TxState Trace) : Json :=
  Json.mkObj [
    ("accountWrites", observeAccounts t.rev.accountWrites),
    ("storageWrites", observeSlots t.rev.storageWrites),
    ("codeWrites", observeCode t.rev.codeWrites),
    ("storageClears", toJson (t.rev.storageClears.toList.map Address.toNat)),
    ("transient", toJson (t.rev.transient.toList.map
      (fun ((a, k), v) ↦ ((a.toNat, k.toNat), v.toNat)))),
    ("accountReads", observeReadKeys Address.toNat t.obs.accountReads),
    ("storageReads", toJson (observeStorageReads t.obs.storageReads)),
    ("codeReads", observeReadKeys Hash32.toNat t.obs.codeReads),
    ("createdAccounts", observeReadKeys Address.toNat t.obs.createdAccounts)]

private def observeTxOrders (t : TxState Trace) : Json :=
  observeOrders t.rev.accountOrder t.rev.storageAddressOrder t.rev.storageSlotOrder

private def observeProvider {α : Type} (answer : Trace (Except WitnessError α)) : Json :=
  toJson (answer.effects, match answer.result with
    | .error (.missing (.code h)) => some h.toNat
    | _ => none)

private def observeBlockExtras (b : BlockState Trace) : Json :=
  toJson ([
    b.consts.emptyCodeHash.toNat, b.consts.emptyTrieRoot.toNat,
    b.consts.emptyOmmerHash.toNat, b.consts.transferTopic.toNat],
    observeOrders b.accountOrder b.storageAddressOrder b.storageSlotOrder,
    [observeProvider (b.preState.getAccount? target),
      observeProvider (b.preState.getStorage target slot1),
      observeProvider (b.preState.getCode (hash 7)),
      observeProvider (b.preState.stateRoot ⟨∅, [], ∅, [], ∅, ∅, ∅⟩)])

private def observeState (t : TxState Trace) : Json :=
  Json.mkObj [("block", observeBlock t.block), ("tx", observeTx t),
    ("blockExtras", observeBlockExtras t.block), ("txOrders", observeTxOrders t)]

private abbrev Cases := List (Option (List (Bytes32 × Nat)))

private def patches : Cases :=
  [none, some [], some [(slot0, 0)], some [(slot2, 71), (slot0, 0), (slot1, 43)]]

private def profiles : List (Nat × Bool × Bool × TxState Trace) :=
  patches.zipIdx.flatMap fun (patch, n) ↦ [false, true].flatMap fun cleared ↦
    [false, true].map fun read ↦ (n, cleared, read, initial patch cleared read)

private def runClear (t : TxState Trace) : Trace (Except StateError (Unit × TxState Trace)) :=
  ((destroyStorage target).run t).run

private def expectedCleared (t : TxState Trace) (kind : Nat) : TxState Trace :=
  let unpatched := initial none true false
  let reads := (if kind == 2 || kind == 3 then t.obs.storageReads.insert (target, slot0)
    else t.obs.storageReads)
  let reads := if kind == 3 then (reads.insert (target, slot1)).insert (target, slot2) else reads
  { unpatched with
    rev.storageAddressOrder.next := if kind == 0 then 1 else 2
    obs.storageReads := reads }

private def checkProfile (p : Nat × Bool × Bool × TxState Trace) : Bool :=
  let (kind, _, _, before) := p
  let first := runClear before
  match first.result with
  | .error _ => false
  | .ok ((), after) =>
    let second := runClear after
    first.effects == [0] && observeState after == observeState (expectedCleared before kind) &&
      second.effects == [0] && (match second.result with
        | .error _ => false
        | .ok ((), repeated) => observeState repeated == observeState after)

-- The selected reverse position may name a different key. A second reverse
-- occurrence of the target survives, and a ghost target slot adds no read.
private def malformedOrderControl : Bool :=
  let before := initial (some [(slot0, 0)]) false false
  let positions := (∅ : Std.ExtTreeMap Address Nat).insert target 4 |>.insert other 7
  let reverse := (∅ : Std.ExtTreeMap Nat Address).insert 4 other |>.insert 7 other |>.insert 9 target
  let before := { before with
    rev.storageAddressOrder := ⟨0, positions, reverse⟩
    rev.storageSlotOrder := before.rev.storageSlotOrder.insert target (order [slot2]) }
  let positions := (∅ : Std.ExtTreeMap Address Nat).insert other 7
  let reverse := (∅ : Std.ExtTreeMap Nat Address).insert 7 other |>.insert 9 target
  let expected := { expectedCleared before 2 with rev.storageAddressOrder := ⟨0, positions, reverse⟩ }
  match (runClear before).result with
  | .error _ => false
  | .ok ((), after) => observeState after == observeState expected

-- An absent patch can have a raw slot index and a reverse-only address entry.
private def orphanOrderControl : Bool :=
  let before := initial none false false
  let o := before.rev.storageAddressOrder
  let orphan := { o with keysByPosition := o.keysByPosition.insert 3 target }
  let before := { before with
    rev.storageAddressOrder := orphan
    rev.storageSlotOrder := before.rev.storageSlotOrder.insert target (order [slot2]) }
  let expected := { expectedCleared before 0 with rev.storageAddressOrder := orphan }
  match (runClear before).result with
  | .error _ => false
  | .ok ((), after) => observeState after == observeState expected

#guard profiles.length == 16
#guard profiles.all checkProfile
#guard malformedOrderControl
#guard orphanOrderControl

end STFSpec.Conformance.State.DestroyStorageGuards
