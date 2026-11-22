/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Lean.Data.Json
import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions

open Lean STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private abbrev Trace := StateT (List Nat) Id
private abbrev Slots := Std.ExtTreeMap (Address × Bytes32) U256

private structure Case where
  id : String
  stackBottomFirst : List Nat
  gas : Nat
  target : Address
  transient : Slots
  cost : Nat
  pc : Nat
  isStatic : Bool

private def addr := Address.ofNat
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def digest (n : Nat) := Hash32.ofBytes32 (slot n)

private def readCase (row : Json) : Except String Case := do
  let id ← row.getObjValAs? String "id"
  let words ← row.getObjValAs? (List Nat) "stackBottomFirst"
  let prefixCount ← row.getObjValAs? Nat "prefixCount"
  let gas ← row.getObjValAs? Nat "gas"
  let target ← row.getObjValAs? Nat "target"
  let entries ← row.getObjValAs? (List (List Nat)) "transient"
  let cost ← row.getObjValAs? Nat "cost"
  let pc ← row.getObjValAs? Nat "pc"
  let isStatic ← row.getObjValAs? Bool "static"
  let mut transient : Slots := ∅
  for entry in entries do
    match entry with
    | [a, k, v] => transient := transient.insert (addr a, slot k) (U256.ofNat v)
    | _ => throw "expected a transient address, slot and word"
  return ⟨id, List.range prefixCount ++ words, gas, addr target, transient, cost, pc, isStatic⟩

private def ctx (r : Case) : FrameCtx :=
  let schedule := STFSpec.Fork.Amsterdam.vmConfig
  let costs := { schedule.costs with opcodeTload := r.cost, opcodeTstore := 151 }
  let config := { schedule with costs := costs }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 11, 13, #[digest 17, digest 19], addr 23, 29, 31,
      U256.ofNat 37, slot 41, U64.ofNat 43, digest 47, U64.ofNat 53⟩
  let tx : TransactionEnvironment :=
    ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
      79, 83, 89, ∅, ∅, #[], #[], some 0, some (digest 97)⟩
  ⟨config, block, tx, addr 101, r.target, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 103), Bytes.ofList [92], validJumpDestinations (Bytes.ofList [91, 0, 91]),
    7, by decide, true, r.isStatic, false, addr 107⟩

private def memory : Memory :=
  let expanded := Memory.empty.expand 32 (by decide)
  expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
    right
    have h : expanded.size = 32 := by
      change (Memory.empty.expand 32 _).size = 32
      rw [← Memory.length_toBytes, Memory.toBytes_expand, Memory.toBytes_empty]
      rfl
    rw [h]
    decide)

private def frame (r : Case) (stack : Stack) : Frame :=
  let log : Log := ⟨addr 256, #[digest 256, digest 1, digest 256], Bytes.ofList [255, 0, 128]⟩
  ⟨r.pc, stack, memory, ⟨r.gas, 11, 13, -17, 19, 23⟩,
    .concat (.leaf [log]) (.concat .empty (.leaf [log])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    (∅ : AddrSet).insert (addr 1),
    ((∅ : SlotSet).insert (addr 1, slot 256)).insert (addr 256, slot 1)⟩

private def provider : PreState Trace where
  getAccount? := fun _ ↦ do
    modify (· ++ [1])
    pure (.ok (some ⟨13, U256.ofNat 17, digest 19⟩))
  getStorage := fun _ _ ↦ do
    modify (· ++ [2])
    pure (.ok (U256.ofNat 107))
  getCode := fun _ ↦ do
    modify (· ++ [3])
    pure (.ok (ByteArray.mk #[0, 128, 255]))
  stateRoot := fun _ ↦ do
    modify (· ++ [4])
    pure (.ok (digest 113))

private def index {K : Type} [Ord K] [Std.TransOrd K] (key : K) (salt : Nat) : WriteOrder K :=
  ⟨salt + 11, (∅ : Std.ExtTreeMap K Nat).insert key (salt + 3),
    (∅ : Std.ExtTreeMap Nat K).insert (salt + 5) key⟩

private def writes (a : Address) (k : Bytes32) (salt : Nat) (transient : Slots) : TxRevertible :=
  let accounts := (∅ : Std.ExtTreeMap Address (Option Account)).insert a
    (some ⟨salt + 1, U256.ofNat (salt + 2), digest (salt + 3)⟩)
  let storage := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert k (U256.ofNat (salt + 4)))
  let slotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert a (index k (salt + 2))
  let code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (digest (salt + 5))
    (ByteArray.mk #[0, UInt8.ofNat salt, 255])
  ⟨accounts, index a salt, storage, index a (salt + 1), slotOrder, code,
    (∅ : Std.ExtTreeSet Address).insert (addr (salt + 6)), transient⟩

private def reads (salt : Nat) : TxObs :=
  ⟨(∅ : Std.HashSet Address).insert (addr (salt + 7)),
    (∅ : Std.HashSet (Address × Bytes32)).insert (addr (salt + 8), slot (salt + 9)),
    (∅ : Std.HashSet Hash32).insert (digest (salt + 10)),
    (∅ : Std.HashSet Address).insert (addr 97)⟩

private def world (r : Case) : VmWorld Trace :=
  let k := slot (r.stackBottomFirst.getLastD 0)
  let b := writes r.target k 40 ∅
  let o := reads 40
  let consts : HashConsts := ⟨digest 101, digest 103, digest 107, digest 109⟩
  ⟨⟨⟨provider, consts, b.accountWrites, b.accountOrder, b.storageWrites, b.storageAddressOrder,
      b.storageSlotOrder, b.codeWrites, b.storageClears, o.accountReads, o.storageReads, o.codeReads,
      some (2 ^ 140 + 13)⟩, writes r.target k 80 r.transient, reads 80⟩⟩

private def frameJson (f : Frame) : Json := Json.mkObj [
  ("pc", toJson f.pc), ("stack", toJson (f.stack.toList.map U256.toNat)),
  ("memory", toJson (f.memory.toBytes.map UInt8.toNat)),
  ("meter", toJson [Int.ofNat f.gasMeter.gasLeft, Int.ofNat f.gasMeter.stateGasLeft,
    Int.ofNat f.gasMeter.stateGasBaseline, f.gasMeter.refundCounter,
    Int.ofNat f.gasMeter.stateGasSpilled, Int.ofNat f.gasMeter.stateGasCommittedSpill]),
  ("logs", toJson (f.logs.toList.map fun l ↦ [
    toJson l.address.toNat, toJson (l.topics.toList.map Hash32.toNat),
    toJson (l.data.toList.map UInt8.toNat)])),
  ("deleted", toJson (f.accountsToDelete.toList.map Address.toNat)),
  ("returnData", toJson (f.returnData.toList.map UInt8.toNat)),
  ("warmAddresses", toJson (f.accessedAddresses.toList.map Address.toNat)),
  ("warmSlots", toJson (f.accessedStorageKeys.toList.map fun (a, k) ↦ [a.toNat, k.toNat]))]

private def accountJson (account : Option Account) : Json :=
  (account.map fun a ↦ toJson [a.nonce, a.balance.toNat, a.codeHash.toNat]).getD Json.null

private def stateFields
    (accounts : Std.ExtTreeMap Address (Option Account))
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) (clears : Std.ExtTreeSet Address)
    (accountReads : Std.HashSet Address) (storageReads : Std.HashSet (Address × Bytes32))
    (codeReads : Std.HashSet Hash32) : List (String × Json) :=
  [("accountWrites", toJson (accounts.toList.map fun (a, value) ↦
      [toJson a.toNat, accountJson value])),
    ("storageWrites", toJson (storage.toList.map fun (a, entries) ↦
      [toJson a.toNat, toJson (entries.toList.map fun (entry : Bytes32 × U256) ↦
        [entry.1.toNat, entry.2.toNat])])),
    ("codeWrites", toJson (code.toList.map fun (k, v) ↦
      [toJson k.toNat, toJson (v.toList.map UInt8.toNat)])),
    ("storageClears", toJson (clears.toList.map Address.toNat)),
    ("accountReads", toJson (accountReads.toList.map Address.toNat)),
    ("storageReads", toJson (storageReads.toList.map fun (a, k) ↦ [a.toNat, k.toNat])),
    ("codeReads", toJson (codeReads.toList.map Hash32.toNat))]

private def indexJson {K : Type} [Ord K] [Std.TransOrd K]
    (keyToNat : K → Nat) (order : WriteOrder K) : Json :=
  toJson [toJson order.next,
    toJson (order.positions.toList.map fun (k, pos) ↦ [keyToNat k, pos]),
    toJson (order.keysByPosition.toList.map fun (pos, k) ↦ [pos, keyToNat k])]

private def orderJson (accounts storage : WriteOrder Address)
    (slots : Std.ExtTreeMap Address (WriteOrder Bytes32)) : Json :=
  toJson [indexJson Address.toNat accounts, indexJson Address.toNat storage,
    toJson (slots.toList.map fun (a, order) ↦ [toJson a.toNat, indexJson FixedBytes.toNat order])]

private def resultJson {α : Type} (encode : α → Json) : Except WitnessError α → Json
  | .ok value => encode value
  | .error _ => Json.null

private def sampleProvider (p : PreState Trace) : Trace Json := do
  let account ← p.getAccount? (addr 1)
  let storage ← p.getStorage (addr 2) (slot 3)
  let code ← p.getCode (digest 5)
  let root ← p.stateRoot ⟨∅, [], ∅, [], ∅, ∅, ∅⟩
  return toJson [resultJson accountJson account, resultJson (toJson ∘ U256.toNat) storage,
    resultJson (toJson ∘ List.map UInt8.toNat ∘ ByteArray.toList) code,
    resultJson (toJson ∘ Hash32.toNat) root]

private def worldJson (w : VmWorld Trace) : Json :=
  let b := w.tx.block
  let r := w.tx.rev
  let o := w.tx.obs
  let block := stateFields b.accountWrites b.storageWrites b.codeWrites b.storageClears
    b.accountReads b.storageReads b.codeReads
  let tx := stateFields r.accountWrites r.storageWrites r.codeWrites r.storageClears
    o.accountReads o.storageReads o.codeReads
  let (samples, calls) := (sampleProvider b.preState).run []
  Json.mkObj [
    ("block", Json.mkObj (block ++ [("oldestAncestorOffset", toJson b.oldestAncestorOffset)])),
    ("tx", Json.mkObj (tx ++ [("createdAccounts", toJson (o.createdAccounts.toList.map Address.toNat)),
      ("transient", toJson (r.transient.toList.map fun ((a, k), v) ↦ [a.toNat, k.toNat, v.toNat]))])),
    ("consts", toJson ([b.consts.emptyCodeHash, b.consts.emptyTrieRoot, b.consts.emptyOmmerHash,
      b.consts.transferTopic].map Hash32.toNat)),
    ("blockOrder", orderJson b.accountOrder b.storageAddressOrder b.storageSlotOrder),
    ("txOrder", orderJson r.accountOrder r.storageAddressOrder r.storageSlotOrder),
    ("provider", samples), ("sampleCalls", toJson calls)]

private def observe (r : Case) : Except String Json := do
  let stack ← (r.stackBottomFirst.foldlM (fun s n ↦ Stack.push s (U256.ofNat n)) Stack.empty).mapError
    (fun _ ↦ "invalid TLOAD input stack")
  let input := frame r stack
  let initial := world r
  let (result, calls) := (((tload (ctx r) input).run initial).run).run []
  let .ok (result, final) := result | throw "TLOAD returned VmFault"
  let (tag, output) ← match result with
    | .continue output => pure ("continue", output)
    | .halt output .stackUnderflow => pure ("underflow", output)
    | .halt output .outOfGas => pure ("outOfGas", output)
    | _ => throw "TLOAD returned an unexpected result"
  return Json.mkObj [("id", toJson r.id), ("tag", toJson tag), ("calls", toJson calls),
    ("before", frameJson input), ("after", frameJson output),
    ("worldBefore", worldJson initial), ("worldAfter", worldJson final)]

/-- Run the public TLOAD handler on each supplied frame and transaction. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the TLOAD input catalogue")
  let input ← IO.FS.readFile path
  let rows ← IO.ofExcept ((Json.parse input).bind Json.getArr?)
  for row in rows do
    let observed ← IO.ofExcept ((readCase row).bind observe)
    IO.println observed.compress
