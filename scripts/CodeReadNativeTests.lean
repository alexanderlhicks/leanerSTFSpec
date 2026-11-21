/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Lean.Data.Json

/-!
# Code read observations

The same input-only recipes exercise the public action natively and interpreted.
Each attempt captures the whole answer and its provider trace. A success returns
a transaction state for the next attempt. After a failure, the test can run
another attempt on the original supplied state.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4.
-/

open STFSpec.Base STFSpec.State Lean

private def array (xs : List Json) : Json := .arr xs.toArray
private def num (n : Nat) : Json := toJson n
private def pair (a b : Json) : Json := array [a, b]
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def hashValue (h : Hash32) : Nat := h.toBytes32.toNat
private def hashJson (h : Hash32) : Json := num (hashValue h)
private def byteList (b : ByteArray) : List Nat := b.toList.map UInt8.toNat

private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else throw "expected lowercase hex digit"

private def bytesOfHex : List Char → Except String (List UInt8)
  | [] => pure []
  | a :: b :: cs => do
    let n := (← nibble a) * 16 + (← nibble b)
    return UInt8.ofNat n :: (← bytesOfHex cs)
  | [_] => throw "expected full bytes"

private def readBytes (j : Json) : Except String ByteArray := do
  return ByteArray.mk (← bytesOfHex (← j.getStr?).toList).toArray

private def readHash (j : Json) : Except String Hash32 := do
  let s ← j.getStr?
  if s.length != 64 then throw "expected 32-byte hash"
  return hash (← s.toList.foldlM (fun acc c ↦ do return acc * 16 + (← nibble c)) 0)

private def readMap (j : Json) : Except String (Std.ExtTreeMap Hash32 ByteArray) := do
  (← j.getArr?).toList.foldlM (fun out entry ↦ do
    match (← entry.getArr?).toList with
    | [k, v] => return out.insert (← readHash k) (← readBytes v)
    | _ => throw "expected code entry") ∅

private def readItem (j : Json) : Except String WitnessItem := do
  if j.getStr? matches .ok "leaf" then return .leaf
  if let .ok value := j.getObjVal? "node" then return .node (← readHash value)
  return .code (← readHash (← j.getObjVal? "code"))

private def readError (j : Json) : Except String WitnessError := do
  if let .ok value := j.getObjVal? "missing" then return .missing (← readItem value)
  if let .ok value := j.getObjVal? "malformed" then return .malformed (← readItem value)
  return .unresolved (← readHash (← j.getObjVal? "unresolved"))

private structure Recipe where
  name : String
  query : Hash32
  reserved : Hash32
  blockCode : Std.ExtTreeMap Hash32 ByteArray
  txCode : Std.ExtTreeMap Hash32 ByteArray
  providerCode : Std.ExtTreeMap Hash32 ByteArray
  providerError : WitnessError
  oldReads : Std.HashSet Hash32
  attempts : Nat

private def readRecipe (j : Json) : Except String Recipe := do
  let reads ← (← (← j.getObjVal? "old_reads").getArr?).toList.mapM readHash
  return ⟨← (← j.getObjVal? "id").getStr?, ← readHash (← j.getObjVal? "hash"),
    ← readHash (← j.getObjVal? "emptyCodeHash"), ← readMap (← j.getObjVal? "block"),
    ← readMap (← j.getObjVal? "tx"), ← readMap (← j.getObjVal? "provider"),
    ← readError (← j.getObjVal? "providerError"), reads.foldl (·.insert ·) ∅,
    ← (← j.getObjVal? "repeat").getNat?⟩

private abbrev Trace := StateT (List (List Nat)) Id

private def supplied (r : Recipe) : PreState Trace where
  getAccount? := fun a ↦ do
    modify (· ++ [[1, a.toNat]])
    pure (.ok (some ⟨2 ^ 80 + a.toNat, U256.ofNat 17, hash 62⟩))
  getStorage := fun a k ↦ do
    modify (· ++ [[2, a.toNat, k.toNat]])
    pure (.ok (U256.ofNat (a.toNat + k.toNat)))
  getCode := fun h ↦ do
    modify (· ++ [[0, hashValue h]])
    pure <| match r.providerCode[h]? with
    | some bytes => .ok bytes
    | none => .error r.providerError
  stateRoot := fun d ↦ do
    let n := d.codeChanges.size
    modify (· ++ [[3, n]])
    pure (.ok (hash (73 + n)))

private def order {K : Type} [Ord K] [Std.TransOrd K] (k l : K)
    (salt : Nat) : WriteOrder K :=
  ⟨2 ^ 410 + salt,
    (∅ : Std.ExtTreeMap K Nat).insert k (7 + salt) |>.insert l (91 + salt),
    (∅ : Std.ExtTreeMap Nat K).insert (9 + salt) l |>.insert (71 + salt) l⟩

private def accountWrites (salt : Nat) : Std.ExtTreeMap Address (Option Account) :=
  (∅ : Std.ExtTreeMap Address (Option Account)).insert (Address.ofNat salt) none
    |>.insert (Address.ofNat (salt + 1))
      (some ⟨2 ^ 80 + salt, U256.ofNat (2 ^ 256 - 1), hash (salt + 2)⟩)

private def storageWrites (salt : Nat) : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert (Address.ofNat salt) ∅
    |>.insert (Address.ofNat (salt + 1))
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert (FixedBytes.ofNat 17) U256.zero
       |>.insert (FixedBytes.ofNat 19) (U256.ofNat (2 ^ 256 - 1)))

private def addressOrder (salt : Nat) : WriteOrder Address :=
  order (Address.ofNat salt) (Address.ofNat (salt + 1)) salt

private def slotOrders (salt : Nat) : Std.ExtTreeMap Address (WriteOrder Bytes32) :=
  (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert (Address.ofNat salt)
    WriteOrder.empty |>.insert (Address.ofNat (salt + 2))
      (order (FixedBytes.ofNat 17) (FixedBytes.ofNat 19) salt)

private def clears (salt : Nat) : Std.ExtTreeSet Address := (∅ : Std.ExtTreeSet Address)
  |>.insert (Address.ofNat salt) |>.insert (Address.ofNat (salt + 3))

private def accountReads (salt : Nat) : Std.HashSet Address := (∅ : Std.HashSet Address)
  |>.insert (Address.ofNat (salt + 4)) |>.insert (Address.ofNat salt)

private def storageReads (salt : Nat) : Std.HashSet (Address × Bytes32) :=
  (∅ : Std.HashSet (Address × Bytes32)).insert (Address.ofNat salt, FixedBytes.ofNat 17)
    |>.insert (Address.ofNat (salt + 1), FixedBytes.ofNat 19)

private def initial (r : Recipe) : TxState Trace :=
  let block : BlockState Trace := ⟨supplied r, ⟨r.reserved, hash 11, hash 12, hash 13⟩,
    accountWrites 31, addressOrder 31, storageWrites 31, addressOrder 32, slotOrders 31,
    r.blockCode, clears 31, accountReads 31, storageReads 31,
    (∅ : Std.HashSet Hash32).insert (hash 41) |>.insert (hash 43), some (2 ^ 420 + 3)⟩
  let rev : TxRevertible := ⟨accountWrites 61, addressOrder 61, storageWrites 61,
    addressOrder 62, slotOrders 61, r.txCode, clears 61,
    (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
      (Address.ofNat 62, FixedBytes.ofNat 17) U256.zero |>.insert
      (Address.ofNat 63, FixedBytes.ofNat 19) (U256.ofNat (2 ^ 256 - 1))⟩
  ⟨block, rev, ⟨accountReads 61, storageReads 61, r.oldReads, accountReads 71⟩⟩

private def itemJson : WitnessItem → Json
  | .node h => Json.mkObj [("node", hashJson h)]
  | .code h => Json.mkObj [("code", hashJson h)]
  | .leaf => toJson "leaf"

private def errorJson : WitnessError → Json
  | .missing item => Json.mkObj [("missing", itemJson item)]
  | .malformed item => Json.mkObj [("malformed", itemJson item)]
  | .unresolved h => Json.mkObj [("unresolved", hashJson h)]

private def stateErrorJson : StateError → Json
  | .witness e => Json.mkObj [("witness", errorJson e)]
  | .balanceUnderflow => toJson "balanceUnderflow"
  | .balanceOverflow => toJson "balanceOverflow"
  | .storageOnMissingAccount => toJson "storageOnMissingAccount"

private def accountJson (a : Account) : Json :=
  toJson [a.nonce, a.balance.toNat, hashValue a.codeHash]

private def accountsJson (xs : Std.ExtTreeMap Address (Option Account)) : Json :=
  array (xs.toList.map (fun (k, v) ↦ pair (num k.toNat) (v.elim .null accountJson)))

private def storageJson (xs : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) : Json :=
  array (xs.toList.map (fun (a, slots) ↦
    pair (num a.toNat) (toJson (slots.toList.map (fun (k, v) ↦ [k.toNat, v.toNat])))))

private def codeJson (xs : Std.ExtTreeMap Hash32 ByteArray) : Json :=
  array (xs.toList.map (fun (k, v) ↦ pair (hashJson k) (toJson (byteList v))))

private def addressReadsJson (xs : Std.HashSet Address) : Json :=
  toJson ((xs.toList.map Address.toNat).mergeSort (· ≤ ·))

private def storageReadsJson (xs : Std.HashSet (Address × Bytes32)) : Json :=
  toJson (((xs.toList.map (fun (a, k) ↦ (a.toNat, k.toNat))).mergeSort
    (fun a b ↦ a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))).map (fun (a, k) ↦ [a, k]))

private def codeReadsJson (xs : Std.HashSet Hash32) : Json :=
  toJson ((xs.toList.map hashValue).mergeSort (· ≤ ·))

private def commonFrame (t : TxState Trace) : Json :=
  let b := t.block
  let r := t.rev
  let o := t.obs
  Json.mkObj [("block", Json.mkObj [
    ("account_reads", addressReadsJson b.accountReads),
    ("account_writes", accountsJson b.accountWrites),
    ("storage_reads", storageReadsJson b.storageReads),
    ("storage_writes", storageJson b.storageWrites),
    ("code_reads", codeReadsJson b.codeReads), ("code_writes", codeJson b.codeWrites),
    ("oldest_ancestor_offset", b.oldestAncestorOffset.elim .null num),
    ("storage_clears", toJson (b.storageClears.toList.map Address.toNat))]),
    ("tx", Json.mkObj [
      ("account_reads", addressReadsJson o.accountReads),
      ("account_writes", accountsJson r.accountWrites),
      ("storage_reads", storageReadsJson o.storageReads),
      ("storage_writes", storageJson r.storageWrites),
      ("code_writes", codeJson r.codeWrites), ("created_accounts", addressReadsJson o.createdAccounts),
      ("storage_clears", toJson (r.storageClears.toList.map Address.toNat)),
      ("transient_storage", toJson (r.transient.toList.map (fun ((a, k), v) ↦
        [a.toNat, k.toNat, v.toNat])))])]

private def rawOrder {K : Type} [Ord K] [Std.TransOrd K] (key : K → Nat)
    (o : WriteOrder K) : Json :=
  Json.mkObj [("next", num o.next),
    ("positions", toJson (o.positions.toList.map (fun (k, p) ↦ [key k, p]))),
    ("keysByPosition", toJson (o.keysByPosition.toList.map (fun (p, k) ↦ [p, key k])))]

private def slotOrdersJson (xs : Std.ExtTreeMap Address (WriteOrder Bytes32)) : Json :=
  array (xs.toList.map (fun (a, o) ↦ pair (num a.toNat) (rawOrder FixedBytes.toNat o)))

private def traceResult {α : Type} (ok : α → Json)
    (result : Except WitnessError α × List (List Nat)) : Json :=
  pair (match result.1 with
    | .ok value => Json.mkObj [("ok", ok value)]
    | .error e => Json.mkObj [("error", errorJson e)]) (toJson result.2)

private def probes (r : Recipe) (p : PreState Trace) (b : BlockState Trace) : Json :=
  let hashes := (r.providerCode.toList.map Prod.fst) ++ [r.query, hash 101]
  Json.mkObj [
    ("account", traceResult (fun a ↦ a.elim .null accountJson) ((p.getAccount? (Address.ofNat 19)).run [])),
    ("storage", traceResult (fun v ↦ num v.toNat)
      ((p.getStorage (Address.ofNat 23) (FixedBytes.ofNat 29)).run [])),
    ("code", array (hashes.map (fun h ↦
      pair (hashJson h) (traceResult (fun v ↦ toJson (byteList v)) ((p.getCode h).run []))))),
    ("root", traceResult hashJson ((p.stateRoot (extractBlockDiff b)).run []))]

private def leanFrame (r : Recipe) (t : TxState Trace) : Json :=
  let b := t.block
  let v := t.rev
  Json.mkObj [("consts", toJson ([b.consts.emptyCodeHash, b.consts.emptyTrieRoot,
      b.consts.emptyOmmerHash, b.consts.transferTopic].map hashValue)),
    ("blockOrders", array [rawOrder Address.toNat b.accountOrder,
      rawOrder Address.toNat b.storageAddressOrder, slotOrdersJson b.storageSlotOrder]),
    ("txOrders", array [rawOrder Address.toNat v.accountOrder,
      rawOrder Address.toNat v.storageAddressOrder, slotOrdersJson v.storageSlotOrder]),
    ("provider", probes r b.preState b)]

private def observe (r : Recipe) : Json := Id.run do
  let start := initial r
  let mut state := start
  let mut attempts := #[]
  for _ in [:r.attempts] do
    let (result, calls) := (((getCode r.query).run state).run).run []
    match result with
    | .ok (bytes, next) =>
      attempts := attempts.push (Json.mkObj [("answer", Json.mkObj [("ok", toJson (byteList bytes))]),
        ("calls", toJson calls), ("reads", codeReadsJson next.obs.codeReads),
        ("frame", commonFrame next), ("lean", leanFrame r next)])
      state := next
    | .error error =>
      attempts := attempts.push (Json.mkObj [("answer", Json.mkObj [("error", stateErrorJson error)]),
        ("calls", toJson calls), ("reads", .null), ("frame", .null), ("lean", .null)])
      state := start
  return Json.mkObj [("id", toJson r.name), ("frameBefore", commonFrame start),
    ("leanBefore", leanFrame r start), ("attempts", .arr attempts)]

/-- Emit one whole JSON observation per input recipe. -/
def main (args : List String) : IO Unit := do
  let path := args.headD "STFSpec/Conformance/State/code_read_inputs.json"
  let rows ← IO.ofExcept (← IO.ofExcept (Json.parse (← IO.FS.readFile path))).getArr?
  for row in rows do
    let recipe ← IO.ofExcept (readRecipe row)
    IO.println (observe recipe).compress
