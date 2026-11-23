/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Lean.Data.Json

open Lean STFSpec.Base STFSpec.State

private abbrev Trace := StateT (List Nat) Id

private structure ReadCase where
  id : String
  address : Address
  slot : Bytes32
  transient : Std.ExtTreeMap (Address × Bytes32) U256
  repeatCount : Nat

private def readCase (row : Json) : Except String ReadCase := do
  let id ← row.getObjValAs? String "id"
  let address ← row.getObjValAs? Nat "address"
  let slot ← row.getObjValAs? Nat "slot"
  let entries ← row.getObjValAs? (List (List Nat)) "transient"
  let repeatCount ← row.getObjValAs? Nat "repeat"
  let mut transient := ∅
  for entry in entries do
    match entry with
    | [a, k, v] => transient := transient.insert (Address.ofNat a, FixedBytes.ofNat k) (U256.ofNat v)
    | _ => throw "expected a transient address/slot/word"
  return ⟨id, Address.ofNat address, FixedBytes.ofNat slot, transient, repeatCount⟩

private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def suppliedAccount (salt : Nat) : Account :=
  ⟨2 ^ 180 + salt, U256.ofNat (2 ^ 200 + salt), digest (2 ^ 255 + salt)⟩

private def provider : PreState Trace where
  getAccount? := fun _ ↦ do
    modify (· ++ [1])
    pure (.ok (some (suppliedAccount 120)))
  getStorage := fun _ _ ↦ do
    modify (· ++ [2])
    pure (.ok (U256.ofNat (2 ^ 230 + 2)))
  getCode := fun _ ↦ do
    modify (· ++ [3])
    pure (.ok (ByteArray.mk #[120, 0, 255]))
  stateRoot := fun _ ↦ do
    modify (· ++ [4])
    pure (.ok (digest (2 ^ 231 + 4)))

private def index {K : Type} [Ord K] [Std.TransOrd K] (key : K) (salt : Nat) : WriteOrder K :=
  ⟨2 ^ 190 + salt, (∅ : Std.ExtTreeMap K Nat).insert key 3,
    (∅ : Std.ExtTreeMap Nat K).insert 5 key⟩

private def writes (r : ReadCase) (salt : Nat) (transient : Std.ExtTreeMap (Address × Bytes32) U256) :
    TxRevertible :=
  let accounts := (∅ : Std.ExtTreeMap Address (Option Account)).insert
    r.address (some (suppliedAccount salt)) |>.insert (Address.ofNat (salt + 1)) none
  let slots := (∅ : Std.ExtTreeMap Bytes32 U256).insert r.slot (U256.ofNat (2 ^ 170 + salt))
  let storage := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert
    r.address slots |>.insert (Address.ofNat (salt + 3)) ∅
  let slotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert
    r.address (index r.slot (salt + 2))
  let code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert
    (digest (2 ^ 153 + salt)) (ByteArray.mk #[0, UInt8.ofNat salt, 255])
  ⟨accounts, index r.address salt, storage, index r.address (salt + 1), slotOrder,
    code, (∅ : Std.ExtTreeSet Address).insert (Address.ofNat (salt + 1)), transient⟩

private def observations (salt : Nat) : TxObs :=
  let a := Address.ofNat (salt + 2)
  let k : Bytes32 := FixedBytes.ofNat (2 ^ 155 + salt)
  ⟨(∅ : Std.HashSet Address).insert a,
    (∅ : Std.HashSet (Address × Bytes32)).insert (a, k),
    (∅ : Std.HashSet Hash32).insert (digest (2 ^ 154 + salt)),
    (∅ : Std.HashSet Address).insert (Address.ofNat 97)⟩

private def initial (r : ReadCase) : TxState Trace :=
  let b := writes r 40 ∅
  let o := observations 40
  let consts : HashConsts :=
    ⟨digest (2 ^ 220 + 1), digest (2 ^ 220 + 2), digest (2 ^ 220 + 3), digest (2 ^ 220 + 4)⟩
  ⟨⟨provider, consts, b.accountWrites, b.accountOrder, b.storageWrites, b.storageAddressOrder,
    b.storageSlotOrder, b.codeWrites, b.storageClears, o.accountReads, o.storageReads,
    o.codeReads, some (2 ^ 140 + 13)⟩, writes r 80 r.transient, observations 80⟩

private def hashValue (hash : Hash32) : Nat := hash.toNat

private def bytesValue (bytes : ByteArray) : List Nat := bytes.toList.map UInt8.toNat

private def accountValue (account : Account) : Json :=
  toJson [account.nonce, account.balance.toNat, hashValue account.codeHash]

private def optionalAccountValue (account : Option Account) : Json :=
  (account.map accountValue).getD Json.null

private def storageReadValues (reads : Std.HashSet (Address × Bytes32)) : List (List Nat) :=
  let pairs := reads.toList.map fun (a, k) ↦ (a.toNat, k.toNat)
  (pairs.mergeSort (fun (a, k) (b, l) ↦ a < b || (a == b && k ≤ l))).map
    fun (a, k) ↦ [a, k]

private def addressValues (addresses : Std.HashSet Address) : List Nat :=
  (addresses.toList.map Address.toNat).mergeSort (· ≤ ·)

private def overlay
    (accounts : Std.ExtTreeMap Address (Option Account))
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) (clears : Std.ExtTreeSet Address)
    (accountReads : Std.HashSet Address) (storageReads : Std.HashSet (Address × Bytes32))
    (codeReads : Std.HashSet Hash32) : List (String × Json) :=
  [("accountWrites", toJson (accounts.toList.map fun (a, value) ↦
      [toJson a.toNat, optionalAccountValue value])),
    ("storageWrites", toJson (storage.toList.map fun entry ↦
      [toJson entry.1.toNat, toJson (entry.2.toList.map fun slot ↦ [slot.1.toNat, slot.2.toNat])])),
    ("codeWrites", toJson (code.toList.map fun (hash, bytes) ↦
      [toJson (hashValue hash), toJson (bytesValue bytes)])),
    ("storageClears", toJson (clears.toList.map Address.toNat)),
    ("accountReads", toJson (addressValues accountReads)),
    ("storageReads", toJson (storageReadValues storageReads)),
    ("codeReads", toJson ((codeReads.toList.map hashValue).mergeSort (· ≤ ·)))]

private def indexValue {K : Type} [Ord K] [Std.TransOrd K]
    (keyValue : K → Nat) (order : WriteOrder K) : Json :=
  toJson [toJson order.next,
    toJson (order.positions.toList.map fun (k, pos) ↦ [keyValue k, pos]),
    toJson (order.keysByPosition.toList.map fun (pos, k) ↦ [pos, keyValue k])]

private def orderValue (accountOrder storageAddressOrder : WriteOrder Address)
    (slotOrders : Std.ExtTreeMap Address (WriteOrder Bytes32)) : Json :=
  toJson [indexValue Address.toNat accountOrder, indexValue Address.toNat storageAddressOrder,
    toJson (slotOrders.toList.map fun (a, order) ↦
      [toJson a.toNat, indexValue FixedBytes.toNat order])]

private def resultValue {α : Type} (encode : α → Json) : Except WitnessError α → Json
  | .ok value => encode value
  | .error _ => Json.null

private def providerSamples (p : PreState Trace) (address : Address) (slot : Bytes32) :
    Trace Json := do
  let account ← p.getAccount? address
  let storage ← p.getStorage address slot
  let code ← p.getCode (digest 29)
  let root ← p.stateRoot ⟨∅, [], ∅, [], ∅, ∅, ∅⟩
  return toJson [resultValue optionalAccountValue account, resultValue (toJson ∘ U256.toNat) storage,
    resultValue (toJson ∘ bytesValue) code, resultValue (toJson ∘ hashValue) root]

private def frame (r : ReadCase) (t : TxState Trace) : Except String Json := do
  let b := t.block
  let w := t.rev
  let o := t.obs
  let (samples, probeCalls) := (providerSamples b.preState r.address r.slot).run []
  if probeCalls != [1, 2, 3, 4] then
    throw "retained provider sample calls differ"
  let block := overlay b.accountWrites b.storageWrites b.codeWrites
    b.storageClears b.accountReads b.storageReads b.codeReads
  let tx := overlay w.accountWrites w.storageWrites w.codeWrites
    w.storageClears o.accountReads o.storageReads o.codeReads
  let transient := w.transient.toList.map fun ((a, k), v) ↦ [a.toNat, k.toNat, v.toNat]
  return Json.mkObj [
    ("block", Json.mkObj (block ++ [("oldestAncestorOffset", toJson b.oldestAncestorOffset)])),
    ("tx", Json.mkObj (tx ++ [("createdAccounts", toJson (addressValues o.createdAccounts)),
      ("transient", toJson transient)])),
    ("consts", toJson ([b.consts.emptyCodeHash, b.consts.emptyTrieRoot, b.consts.emptyOmmerHash,
      b.consts.transferTopic].map hashValue)),
    ("blockOrder", orderValue b.accountOrder b.storageAddressOrder b.storageSlotOrder),
    ("txOrder", orderValue w.accountOrder w.storageAddressOrder w.storageSlotOrder),
    ("provider", samples)]

private def observe (r : ReadCase) : Except String Json := do
  let mut state := initial r
  let mut calls : List Nat := []
  let mut answers := #[]
  let mut frames := #[← frame r state]
  for _ in [:r.repeatCount] do
    let (result, nextCalls) := (((getTransientStorage r.address r.slot).run state).run).run calls
    match result with
    | .error _ => throw ("transient storage returned an error in " ++ r.id)
    | .ok (answer, next) =>
      calls := nextCalls
      state := next
      answers := answers.push answer.toNat
      frames := frames.push (← frame r state)
  return Json.mkObj [("id", toJson r.id), ("answers", toJson answers),
    ("calls", toJson calls), ("frames", toJson frames)]

/-- Read the checked-in input catalogue and emit complete observations in its order. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the transient storage input catalogue")
  let input ← IO.FS.readFile path
  let rows ← IO.ofExcept ((Json.parse input).bind Json.getArr?)
  for row in rows do
    let observed ← IO.ofExcept ((readCase row).bind observe)
    IO.println observed.compress
