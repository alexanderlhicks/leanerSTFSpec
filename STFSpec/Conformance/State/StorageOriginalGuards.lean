/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Original storage controls

Private tests run the `EthState` action through its public facade. A supplied
provider records each call, and populated raw carriers expose unintended writes.
Spec guidance is in `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.StorageOriginalGuards

open STFSpec.State STFSpec.Base

private def address : Address := Address.ofNat (2 ^ 159 + 3)
private def otherAddress : Address := Address.ofNat 3
private def key : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 9)
private def otherKey : Bytes32 := FixedBytes.ofNat 9
private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def maxWord : Nat := 2 ^ 256 - 1
private def failureHash : Nat := 2 ^ 255 + 123

private abbrev Trace := List (List Nat)
private abbrev Probe := _root_.StateM Trace

private def provider (fails : Bool) : PreState Probe where
  getAccount? := fun a ↦ do
    modify (fun calls ↦ calls ++ [[0, a.toNat]])
    pure (.ok (some ⟨2 ^ 72 + 7, U256.ofNat 23, digest 42⟩))
  getStorage := fun a k ↦ do
    modify (fun calls ↦ calls ++ [[1, a.toNat, k.toNat]])
    if fails then pure (.error (.malformed (.node (digest failureHash))))
    else pure (.ok (U256.ofNat maxWord))
  getCode := fun h ↦ do
    modify (fun calls ↦ calls ++ [[2, h.toBytes32.toNat]])
    pure (.ok (ByteArray.mk #[0, 255, 9]))
  stateRoot := fun d ↦ do
    modify (fun calls ↦ calls ++ [[3, d.accountOrder.length]])
    pure (.ok (digest 77))

private structure Case where
  name : String
  created : Bool
  patch : Option (List (Nat × Nat))
  cleared : Bool
  fails : Bool
  expected : Option Nat
  callsProvider : Bool

private def cases : List Case := [
  ⟨"created-masks-block", true, some [(key.toNat, 314)], true, true, some 0, false⟩,
  ⟨"created-masks-provider", true, none, false, true, some 0, false⟩,
  ⟨"block-write-over-clear", false, some [(key.toNat, 314)], true, true, some 314, false⟩,
  ⟨"explicit-zero-over-provider", false, some [(key.toNat, 0)], false, true, some 0, false⟩,
  ⟨"block-clear-after-key-miss", false, some [(otherKey.toNat, 11)], true, true, some 0, false⟩,
  ⟨"block-clear-after-address-miss", false, none, true, true, some 0, false⟩,
  ⟨"empty-patch-provider", false, some [], false, false, some maxWord, true⟩,
  ⟨"other-slot-provider", false, some [(otherKey.toNat, 11)], false, false, some maxWord, true⟩,
  ⟨"no-patch-provider", false, none, false, false, some maxWord, true⟩,
  ⟨"provider-error", false, none, false, true, none, true⟩,
  ⟨"explicit-zero-over-clear", false, some [(key.toNat, 0)], true, true, some 0, false⟩]

private def index {K : Type} [Ord K] [Std.TransOrd K] (k : K) (n : Nat) : WriteOrder K :=
  ⟨n, (∅ : Std.ExtTreeMap K Nat).insert k (n + 1),
    (∅ : Std.ExtTreeMap Nat K).insert (n + 2) k⟩

private def slots (entries : List (Nat × Nat)) : Std.ExtTreeMap Bytes32 U256 :=
  entries.foldl (fun acc (k, value) ↦ acc.insert (FixedBytes.ofNat k) (U256.ofNat value)) ∅

private def transaction (c : Case) : TxState Probe where
  block := {
    preState := provider c.fails
    consts := ⟨digest 41, digest 43, digest 47, digest 53⟩
    accountWrites := Std.ExtTreeMap.insert ∅ otherAddress none
    accountOrder := index address 28
    storageWrites :=
      let writes := Std.ExtTreeMap.insert ∅ otherAddress (slots [(key.toNat, 13)])
      match c.patch with
      | none => writes
      | some patch => writes.insert address (slots patch)
    storageAddressOrder := index otherAddress 29
    storageSlotOrder := Std.ExtTreeMap.insert ∅ otherAddress (index otherKey 30)
    codeWrites := Std.ExtTreeMap.insert ∅ (digest 71) (ByteArray.mk #[255, 1, 0])
    storageClears := if c.cleared then Std.ExtTreeSet.insert ∅ address else ∅
    accountReads := Std.HashSet.insert ∅ address
    storageReads := Std.HashSet.insert ∅ (otherAddress, key)
    codeReads := Std.HashSet.insert ∅ (digest 73)
    oldestAncestorOffset := some 256 }
  rev := {
    accountWrites := Std.ExtTreeMap.insert ∅ address none
    accountOrder := index otherAddress 31
    storageWrites := Std.ExtTreeMap.insert ∅ address (slots [(key.toNat, 17)])
    storageAddressOrder := index address 32
    storageSlotOrder := Std.ExtTreeMap.insert ∅ address (index key 33)
    codeWrites := Std.ExtTreeMap.insert ∅ (digest 79) (ByteArray.mk #[0, 1, 255])
    storageClears := Std.ExtTreeSet.insert ∅ address
    transient := Std.ExtTreeMap.insert ∅ (address, key) (U256.ofNat 19) }
  obs := {
    accountReads := Std.HashSet.insert ∅ otherAddress
    storageReads := Std.HashSet.insert ∅ (otherAddress, otherKey)
    codeReads := Std.HashSet.insert ∅ (Hash32.ofBytes32 otherKey)
    createdAccounts := if c.created then (Std.HashSet.insert ∅ otherAddress).insert address
      else Std.HashSet.insert ∅ otherAddress }

private def group (fields : List (List Nat)) : List Nat :=
  fields.flatMap (fun field ↦ field.length :: field)

private def hashValue (h : Hash32) : Nat := h.toBytes32.toNat
private def byteValues (b : ByteArray) : List Nat := b.toList.map UInt8.toNat

private def accountFields : Option Account → List Nat
  | none => [0]
  | some a => [1, a.nonce, a.balance.toNat, hashValue a.codeHash]

private def errorFields : WitnessError → List Nat
  | .missing (.node h) => [0, 0, hashValue h]
  | .missing (.code h) => [0, 1, hashValue h]
  | .missing .leaf => [0, 2]
  | .malformed (.node h) => [1, 0, hashValue h]
  | .malformed (.code h) => [1, 1, hashValue h]
  | .malformed .leaf => [1, 2]
  | .unresolved h => [2, hashValue h]

private def probeFields {α : Type} (encode : α → List Nat) (action : Probe (Except WitnessError α)) :
    List Nat :=
  let (answer, calls) := action.run []
  let result := match answer with
    | .ok v => 0 :: encode v
    | .error e => 1 :: errorFields e
  group [result, group calls]

private def orderFields {K : Type} [Ord K] [Std.TransOrd K]
    (asNat : K → Nat) (order : WriteOrder K) : List Nat :=
  group [[order.next], group (order.positions.toList.map (fun (k, p) ↦ [asNat k, p])),
    group (order.keysByPosition.toList.map (fun (p, k) ↦ [p, asNat k]))]

private def slotFields
    (writes : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) : List Nat :=
  group (writes.toList.map fun (a, values) ↦
    a.toNat :: group (values.toList.map (fun (k, value) ↦ [k.toNat, value.toNat])))

private def codeFields (writes : Std.ExtTreeMap Hash32 ByteArray) : List Nat :=
  group (writes.toList.map (fun (h, b) ↦ hashValue h :: byteValues b))

private def stateFields (t : TxState Probe) : List (List Nat) :=
  let b := t.block
  let r := t.rev
  let o := t.obs
  let d : BlockDiff := ⟨b.accountWrites, b.accountOrder.toList, b.storageWrites,
    b.storageAddressOrder.toList, ∅, b.codeWrites, b.storageClears⟩
  [
    probeFields accountFields (b.preState.getAccount? address),
    probeFields (fun v ↦ [v.toNat]) (b.preState.getStorage otherAddress otherKey),
    probeFields byteValues (b.preState.getCode (digest 83)),
    probeFields (fun h ↦ [hashValue h]) (b.preState.stateRoot d),
    [hashValue b.consts.emptyCodeHash, hashValue b.consts.emptyTrieRoot,
      hashValue b.consts.emptyOmmerHash, hashValue b.consts.transferTopic],
    group (b.accountWrites.toList.map (fun (a, v) ↦ a.toNat :: accountFields v)),
    orderFields Address.toNat b.accountOrder,
    slotFields b.storageWrites,
    orderFields Address.toNat b.storageAddressOrder,
    group (b.storageSlotOrder.toList.map
      (fun (a, order) ↦ a.toNat :: orderFields FixedBytes.toNat order)),
    codeFields b.codeWrites,
    b.storageClears.toList.map Address.toNat,
    b.accountReads.toList.map Address.toNat,
    group (b.storageReads.toList.map (fun (a, k) ↦ [a.toNat, k.toNat])),
    b.codeReads.toList.map hashValue,
    b.oldestAncestorOffset.toList,
    group (r.accountWrites.toList.map (fun (a, v) ↦ a.toNat :: accountFields v)),
    orderFields Address.toNat r.accountOrder,
    slotFields r.storageWrites,
    orderFields Address.toNat r.storageAddressOrder,
    group (r.storageSlotOrder.toList.map
      (fun (a, order) ↦ a.toNat :: orderFields FixedBytes.toNat order)),
    codeFields r.codeWrites,
    r.storageClears.toList.map Address.toNat,
    group (r.transient.toList.map (fun ((a, k), v) ↦ [a.toNat, k.toNat, v.toNat])),
    o.accountReads.toList.map Address.toNat,
    group (o.storageReads.toList.map (fun (a, k) ↦ [a.toNat, k.toNat])),
    o.codeReads.toList.map hashValue,
    o.createdAccounts.toList.map Address.toNat ]

private structure Observation where
  value : Option Nat
  wrappedError : Option (List Nat)
  retained : Option Bool
  calls : Trace

private def observe (c : Case) : Observation :=
  let t := transaction c
  let (answer, calls) := (((getStorageOriginal address key).run t).run).run []
  match answer with
  | .ok (v, next) => ⟨some v.toNat, none, some (stateFields next == stateFields t), calls⟩
  | .error (.witness e) => ⟨none, some (errorFields e), none, calls⟩
  | .error _ => ⟨none, none, none, calls⟩

private def check (c : Case) (o : Observation) : Bool :=
  o.value == c.expected &&
    o.wrappedError == (if c.expected.isSome then none else some [1, 0, failureHash]) &&
    o.retained == (if c.expected.isSome then some true else none) &&
    o.calls == (if c.callsProvider then [[1, address.toNat, key.toNat]] else [])

#guard cases.length == 11
#guard cases.all (fun c ↦ check c (observe c))

end STFSpec.Conformance.State.StorageOriginalGuards
