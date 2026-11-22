/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transient storage write checks

Library `EthConformance`. Check the complete write result, key isolation and a read
after the write through the State facade.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§4, 7.1 and 7.2.
-/

namespace STFSpec.Conformance.State.TransientStorageWriteChecks

open STFSpec.Base STFSpec.State

private def exactType :
    {m : Type → Type} → [Monad m] → Address → Bytes32 → U256 → STFSpec.State.StateM m Unit :=
  @setTransientStorage

private def updated {m : Type → Type} (t : TxState m)
    (a : Address) (k : Bytes32) (v : U256) : TxState m :=
  { t with rev.transient :=
      if v = U256.zero then t.rev.transient.erase (a, k)
      else t.rev.transient.insert (a, k) v }

private theorem literalAction {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (k : Bytes32) (v : U256) :
    ((setTransientStorage a k v).run t).run = pure (.ok ((), updated t a k v)) := rfl

private theorem retainedFields {m : Type → Type}
    (t : TxState m) (a : Address) (k : Bytes32) (v : U256) :
    { updated t a k v with rev.transient := t.rev.transient } = t := by
  cases t
  rfl

private theorem lookupWrittenKey {m : Type → Type} (t : TxState m)
    (a : Address) (k : Bytes32) (v : U256) :
    (updated t a k v).rev.transient[(a, k)]? =
      if v = U256.zero then none else some v := by
  by_cases h : v = U256.zero <;> simp [updated, h]

private theorem lookupOtherKey {m : Type → Type} (t : TxState m)
    (a b : Address) (k l : Bytes32) (v : U256) (h : compare (a, k) (b, l) ≠ .eq) :
    (updated t a k v).rev.transient[(b, l)]? = t.rev.transient[(b, l)]? := by
  by_cases hz : v = U256.zero <;>
    simp [updated, hz, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, h]

private theorem readAfterWrite (t : TxState Id) (a : Address) (k : Bytes32)
    (v : U256) :
    ((do setTransientStorage a k v; getTransientStorage a k : STFSpec.State.StateM Id U256).run
      t).run = .ok (v, updated t a k v) := by
  simp only [StateT.run_bind, ExceptT.run_bind, literalAction]
  change ((getTransientStorage a k).run (updated t a k v)).run = _
  rw [getTransientStorage_action, lookupWrittenKey]
  by_cases h : v = U256.zero <;> simp [h] <;> rfl

private abbrev Trace := StateT (List Nat) Id
private abbrev Entry := Nat × Nat × Nat

private structure WriteCase where
  name : String
  entries : List Entry
  address : Nat
  slot : Nat
  word : Nat
  expected : List Entry

private def cases : List WriteCase :=
  let a := 2 ^ 159 + 17
  let b := 17
  let c := 18
  let k := 2 ^ 255 + 11
  let l := 11
  let maximum := 2 ^ 256 - 1
  let base := [(b, k, 9), (a, l, 7), (a, k, 5)]
  let explicitZero := (b, l, 0) :: base
  [⟨"replace-and-repeat", base, a, k, maximum, [(b, k, 9), (a, l, 7), (a, k, maximum)]⟩,
   ⟨"erase", base, a, k, 0, [(b, k, 9), (a, l, 7)]⟩,
   ⟨"erase-absent-address", base, c, k, 0, base⟩,
   ⟨"insert-distinct-address", base, c, k, 3, [(b, k, 9), (c, k, 3), (a, l, 7), (a, k, 5)]⟩,
   ⟨"replace-distinct-slot", base, a, l, 11, [(b, k, 9), (a, l, 11), (a, k, 5)]⟩,
   ⟨"erase-explicit-zero", explicitZero, b, l, 0, base⟩,
   ⟨"replace-explicit-zero", explicitZero, b, l, 4, (b, l, 4) :: base⟩,
   ⟨"first-write", [], b, l, 6, [(b, l, 6)]⟩,
   ⟨"retain-unrelated-zero", explicitZero, a, k, 2, [(b, l, 0), (b, k, 9), (a, l, 7), (a, k, 2)]⟩,
   ⟨"insert-nearby-slot", base, a, k + 1, 12, base ++ [(a, k + 1, 12)]⟩]

private def called {α : Type} (tag : Nat) : Trace (Except WitnessError α) := do
  modify (tag :: ·)
  pure (.error (.missing (.node (Hash32.ofBytes32 (FixedBytes.ofNat tag)))))

private def initial (c : WriteCase) : TxState Trace :=
  let address := Address.ofNat c.address
  let slot : Bytes32 := FixedBytes.ofNat c.slot
  let hash := Hash32.ofBytes32 slot
  let provider : PreState Trace := ⟨fun _ ↦ called 1, fun _ _ ↦ called 2,
    fun _ ↦ called 3, fun _ ↦ called 4⟩
  let block := BlockState.new provider ⟨hash, hash, hash, hash⟩
  let other := Address.ofNat (c.address + 2)
  let rawOrder : WriteOrder Address :=
    ⟨0, (∅ : Std.ExtTreeMap Address Nat).insert other 4,
      (∅ : Std.ExtTreeMap Nat Address).insert 6 address⟩
  let transient : Std.ExtTreeMap (Address × Bytes32) U256 :=
    c.entries.foldl (fun map (a, k, v) ↦
      map.insert (Address.ofNat a, FixedBytes.ofNat k) (U256.ofNat v)) ∅
  let storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
    (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert address
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert slot U256.zero)
  let tombstones := (∅ : Std.ExtTreeMap Address (Option Account)).insert address none
  let clears := (∅ : Std.ExtTreeSet Address).insert address
  let rev : TxRevertible := ⟨tombstones, rawOrder, storage, rawOrder, ∅, ∅, clears, transient⟩
  let obs : TxObs := ⟨(∅ : Std.HashSet Address).insert other,
    (∅ : Std.HashSet (Address × Bytes32)).insert (address, slot),
    (∅ : Std.HashSet Hash32).insert hash, (∅ : Std.HashSet Address).insert address⟩
  ⟨{ block with storageWrites := storage, oldestAncestorOffset := some (2 ^ 180) }, rev, obs⟩

private def sameOrder (a b : WriteOrder Address) : Bool :=
  a.next == b.next && a.positions.toList == b.positions.toList &&
    a.keysByPosition.toList == b.keysByPosition.toList

private def rawFieldsRetained (start next : TxState Trace) (address : Address) (slot : Bytes32) :
    Bool :=
  next.block.oldestAncestorOffset == start.block.oldestAncestorOffset &&
    (next.block.storageWrites[address]?.bind (·[slot]?)) == some U256.zero &&
    next.rev.accountWrites.contains address &&
    (next.rev.storageWrites[address]?.bind (·[slot]?)) == some U256.zero &&
    sameOrder start.rev.accountOrder next.rev.accountOrder &&
    sameOrder start.rev.storageAddressOrder next.rev.storageAddressOrder &&
    next.rev.storageClears.contains address &&
    next.obs.accountReads.toList == start.obs.accountReads.toList &&
    next.obs.storageReads.toList == start.obs.storageReads.toList &&
    next.obs.codeReads.toList == start.obs.codeReads.toList &&
    next.obs.createdAccounts.toList == start.obs.createdAccounts.toList

private def observe (c : WriteCase) : Option (List (List Entry × Nat)) := do
  let address := Address.ofNat c.address
  let slot : Bytes32 := FixedBytes.ofNat c.slot
  let start := initial c
  let mut state := start
  let mut frames := []
  for _ in [:2] do
    let (result, calls) := (((do
      setTransientStorage address slot (U256.ofNat c.word)
      getTransientStorage address slot : STFSpec.State.StateM Trace U256).run state).run).run []
    let .ok (word, next) := result | none
    if !calls.isEmpty || !rawFieldsRetained start next address slot then
      none
    else
      state := next
      let entries := next.rev.transient.toList.map fun ((a, k), v) ↦ (a.toNat, k.toNat, v.toNat)
      frames := (entries, word.toNat) :: frames
  return frames.reverse

#guard cases.all (fun c ↦ observe c == some [(c.expected, c.word), (c.expected, c.word)])

end STFSpec.Conformance.State.TransientStorageWriteChecks
