/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transaction snapshot controls

Library `EthConformance`. Private clients check the complete R24 action and test
three nested restores, current observations and reuse of a saved Lean value.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3–5.
-/

namespace STFSpec.Conformance.State.TransactionSnapshotChecks

open STFSpec.Base STFSpec.State

private def copyType : {m : Type → Type} → TxState m → TxRevertible :=
  @copyTxState

private def restoreType :
    {m : Type → Type} → [Monad m] → TxRevertible → StateM m Unit :=
  @restoreTxState

private theorem savedRecord {m : Type → Type} (t : TxState m) :
    copyTxState t = t.rev := rfl

private theorem restoreAction {m : Type → Type} [Monad m] (t : TxState m)
    (snap : TxRevertible) :
    ((restoreTxState snap).run t).run =
      pure (.ok ((), TxState.mk t.block snap t.obs)) := rfl

private theorem restoreSavedRecord (saved current : TxState Id) :
    ((restoreTxState (copyTxState saved)).run current).run =
      .ok ((), TxState.mk current.block saved.rev current.obs) := rfl

private abbrev Trace := StateT Nat Id

private def address : Nat → Address := Address.ofNat
private def slot : Nat → Bytes32 := FixedBytes.ofNat
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)

private def failProvider {α : Type} : Trace (Except WitnessError α) :=
  fun calls ↦ (.error (.missing (.node (hash 89))), calls + 1)

private def block : BlockState Trace :=
  BlockState.new
    ⟨fun _ ↦ failProvider, fun _ _ ↦ failProvider, fun _ ↦ failProvider,
      fun _ ↦ failProvider⟩
    ⟨hash 90, hash 91, hash 92, hash 93⟩

private def owner : Nat := 2 ^ 159
private def key : Nat := 2 ^ 255
private def nonce : Nat := 2 ^ 256

private def rawOrder {K : Type} [Ord K] [Std.TransOrd K] (k : K) (n : Nat) :
    WriteOrder K :=
  ⟨2 ^ 96 + n, (∅ : Std.ExtTreeMap K Nat).insert k (n + 1),
    (∅ : Std.ExtTreeMap Nat K).insert (n + 10) k⟩

private def version (n : Nat) : TxRevertible where
  accountWrites := (∅ : Std.ExtTreeMap Address (Option Account))
    |>.insert (address owner) none
    |>.insert (address (owner + 1)) (some ⟨nonce + n, U256.ofNat n, hash (key + n)⟩)
  accountOrder := rawOrder (address owner) n
  storageWrites := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    |>.insert (address owner) ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot key) (U256.ofNat n))
    |>.insert (address (owner + 1)) ∅
  storageAddressOrder := rawOrder (address (owner + 1)) (n + 20)
  storageSlotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
    |>.insert (address (owner + 2)) (rawOrder (slot key) (n + 40))
    |>.insert (address (owner + 3)) WriteOrder.empty
  codeWrites := (∅ : Std.ExtTreeMap Hash32 ByteArray)
    |>.insert (hash key) ⟨#[0, UInt8.ofNat n, 255]⟩
    |>.insert (hash (key + 1)) ByteArray.empty
  storageClears := (∅ : Std.ExtTreeSet Address).insert (address (owner + n))
  transient := (∅ : Std.ExtTreeMap (Address × Bytes32) U256)
    |>.insert (address owner, slot key) (U256.ofNat n)
    |>.insert (address (owner + 1), slot key) (U256.ofNat (2 ^ 256 - 1 - n))

private def initial : TxState Trace :=
  ⟨block, version 0, ⟨∅, ∅, ∅, ∅⟩⟩

private def advance (n : Nat) (t : TxState Trace) : TxState Trace :=
  { block := { t.block with oldestAncestorOffset := some (2 ^ 180 + n) }
    rev := version n
    obs :=
      { accountReads := t.obs.accountReads.insert (address n)
        storageReads := t.obs.storageReads.insert (address n, slot (key + n))
        codeReads := t.obs.codeReads.insert (hash (key + n))
        createdAccounts := t.obs.createdAccounts.insert (address (owner + n)) } }

private def restore (snap : TxRevertible) (t : TxState Trace) : Option (TxState Trace) :=
  match ((restoreTxState snap).run t).run 17 with
  | (.ok ((), next), 17) => some next
  | _ => none

private def scenario : Option (List (TxState Trace)) := do
  let t0 := advance 0 initial
  let snap0 := copyTxState t0
  let t1 := advance 1 t0
  let snap1 := copyTxState t1
  let t2 := advance 2 t1
  let snap2 := copyTxState t2
  let t3 := advance 3 t2
  let r2 ← restore snap2 t3
  let r1 ← restore snap1 r2
  let r0 ← restore snap0 r1
  pure [t0, t1, t2, t3, r2, r1, r0]

private def hashNat (h : Hash32) : Nat := h.toBytes32.toNat

-- The same groups are observed in the pinned source. Storage addresses are a
-- separate group so an empty inner map and an absent address differ.
private def sourceFields (t : TxState Trace) : List (List (List Nat)) :=
  [t.rev.accountWrites.toList.map fun (a, account) ↦
      a.toNat :: (account.map fun v ↦ [v.nonce, v.balance.toNat, hashNat v.codeHash]).getD [],
    t.rev.storageWrites.toList.map fun (a, _) ↦ [a.toNat],
    t.rev.storageWrites.toList.flatMap fun (a, slots) ↦
      slots.toList.map fun (k, v) ↦ [a.toNat, k.toNat, v.toNat],
    t.rev.codeWrites.toList.map fun (h, bs) ↦ hashNat h :: bs.toList.map UInt8.toNat,
    t.rev.storageClears.toList.map fun a ↦ [a.toNat],
    t.rev.transient.toList.map fun ((a, k), v) ↦ [a.toNat, k.toNat, v.toNat],
    (t.obs.accountReads.toList.map Address.toNat).mergeSort (· ≤ ·) |>.map (· :: []),
    (t.obs.storageReads.toList.map fun (a, k) ↦ (a.toNat, k.toNat)).mergeSort
      (fun (a, k) (b, l) ↦ a < b || (a == b && k ≤ l)) |>.map fun (a, k) ↦ [a, k],
    (t.obs.codeReads.toList.map hashNat).mergeSort (· ≤ ·) |>.map (· :: []),
    (t.obs.createdAccounts.toList.map Address.toNat).mergeSort (· ≤ ·) |>.map (· :: []),
    t.block.oldestAncestorOffset.toList.map (· :: [])]

private def expectedSourceFields (writes observations : Nat) : List (List (List Nat)) :=
  let stages := List.range (observations + 1)
  [[[owner], [owner + 1, nonce + writes, writes, key + writes]],
    [[owner], [owner + 1]], [[owner, key, writes]],
    [[key, 0, writes, 255], [key + 1]], [[owner + writes]],
    [[owner, key, writes], [owner + 1, key, 2 ^ 256 - 1 - writes]],
    stages.map (· :: []), stages.map fun n ↦ [n, key + n],
    stages.map fun n ↦ [key + n], stages.map fun n ↦ [owner + n],
    [[2 ^ 180 + observations]]]

private def sourceRows : Option (List (List (List (List Nat)))) :=
  scenario.map (·.map sourceFields)

#guard sourceRows ==
  some ([(0, 0), (1, 1), (2, 2), (3, 3), (2, 3), (1, 3), (0, 3)].map
    fun (writes, observations) ↦ expectedSourceFields writes observations)

private def orderFields {K : Type} [Ord K] [Std.TransOrd K] (keyNat : K → Nat)
    (r : WriteOrder K) : List (List Nat) :=
  [ [r.next],
    r.positions.toList.flatMap fun (k, p) ↦ [keyNat k, p],
    r.keysByPosition.toList.flatMap fun (p, k) ↦ [p, keyNat k] ]

private def metadata (r : TxRevertible) : List (List Nat) :=
  orderFields Address.toNat r.accountOrder ++
  orderFields Address.toNat r.storageAddressOrder ++
  (r.storageSlotOrder.toList.flatMap fun (a, order) ↦
    [a.toNat] :: orderFields FixedBytes.toNat order)

private def expectedMetadata (n : Nat) : List (List Nat) :=
  [[2 ^ 96 + n], [owner, n + 1], [n + 10, owner],
    [2 ^ 96 + n + 20], [owner + 1, n + 21], [n + 30, owner + 1],
    [owner + 2], [2 ^ 96 + n + 40], [key, n + 41], [n + 50, key],
    [owner + 3], [0], [], []]

#guard scenario.map (fun states ↦ states.map fun t ↦ metadata t.rev) ==
  some ([0, 1, 2, 3, 2, 1, 0].map expectedMetadata)

private def reuse : Bool := Id.run do
  let t0 := advance 0 initial
  let snap := copyTxState t0
  let some first := restore snap (advance 1 t0) | return false
  let some again := restore snap (advance 2 first) | return false
  return metadata again.rev == expectedMetadata 0 &&
    sourceFields again == expectedSourceFields 0 2

#guard reuse

end STFSpec.Conformance.State.TransactionSnapshotChecks
