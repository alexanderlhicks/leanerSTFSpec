/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Lean.Data.Json

/-!
# Standalone ordered account write controls

Run the actual State action on every supplied step. Emit the typed finite source
projection and complete raw order metadata before the first step and after each write.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1/7.5.
-/

open STFSpec.State STFSpec.Base Lean

private abbrev Trace := StateT (List Nat) Id

private structure AccountInput where
  nonce : Nat
  balance : Nat
  codeHash : Nat
  deriving FromJson

private structure Write where
  address : Nat
  account : Option AccountInput
  deriving FromJson

private structure IndexInput where
  next : Nat
  positions : List (Nat × Nat)
  keysByPosition : List (Nat × Nat)
  deriving FromJson

private structure History where
  name : String
  initial : List Write
  index : Option IndexInput
  writes : List Write
  deriving FromJson

private def hashOfNat (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def hashNat (h : Hash32) : Nat := h.toBytes32.toNat
private def wide : Nat := 2 ^ 152 + 5

private def AccountInput.value (x : AccountInput) : Account :=
  ⟨x.nonce, U256.ofNat x.balance, hashOfNat x.codeHash⟩

private def Write.decode (w : Write) : Address × Option Account :=
  (Address.ofNat w.address, w.account.map AccountInput.value)

private def providerReply {α : Type} (tag : Nat) : Trace (Except WitnessError α) := do
  modify (· ++ [tag])
  pure (.error (.missing .leaf))

private def provider : PreState Trace where
  getAccount? := fun _ ↦ providerReply 1
  getStorage := fun _ _ ↦ providerReply 2
  getCode := fun _ ↦ providerReply 3
  stateRoot := fun _ ↦ providerReply 4

private def index {K : Type} [Ord K] [Std.TransOrd K] (k : K) :
    WriteOrder K :=
  ⟨2 ^ 180 + 17, (∅ : Std.ExtTreeMap K Nat).insert k 31,
    (∅ : Std.ExtTreeMap Nat K).insert 31 k⟩

private def initial (h : History) : TxState Trace :=
  let a := Address.ofNat 5
  let b := Address.ofNat wide
  let c := Address.ofNat 9
  let k : Bytes32 := FixedBytes.ofNat 7
  let j : Bytes32 := FixedBytes.ofNat (2 ^ 248 + 7)
  let digest := hashOfNat (2 ^ 250 + 11)
  let storage := ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
    (((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero)
      |>.insert j (U256.ofNat (2 ^ 256 - 1)))).insert b ∅
  let slotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert a (index j)
  let codes := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert digest ⟨#[0, 255, 128]⟩
  let clears := (∅ : Std.ExtTreeSet Address).insert c
  let reads := (∅ : Std.HashSet Address).insert b
  let storageReads := (∅ : Std.HashSet (Address × Bytes32)).insert (a, j)
  let codeReads := (∅ : Std.HashSet Hash32).insert digest
  let blockAccounts :=
    (∅ : Std.ExtTreeMap Address (Option Account)).insert c (some ⟨33, U256.one, digest⟩)
  let block : BlockState Trace := ⟨provider, ⟨hashOfNat 21, hashOfNat 22, hashOfNat 23, hashOfNat 24⟩,
    blockAccounts, index c, storage, index b, slotOrder, codes, clears,
    reads, storageReads, codeReads, some (2 ^ 80 + 3)⟩
  let rawWrites := h.initial.map Write.decode
  let accountWrites := rawWrites.foldl (fun acc p ↦ acc.insert p.1 p.2)
    (∅ : Std.ExtTreeMap Address (Option Account))
  let accountOrder := match h.index with
    | none => rawWrites.foldl (fun acc p ↦ acc.record p.1) WriteOrder.empty
    | some idx =>
      ⟨idx.next, idx.positions.foldl (fun acc p ↦ acc.insert (Address.ofNat p.1) p.2) ∅,
        idx.keysByPosition.foldl (fun acc p ↦ acc.insert p.1 (Address.ofNat p.2)) ∅⟩
  let transient := (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert (b, k) (U256.ofNat 23)
  ⟨block, ⟨accountWrites, accountOrder, storage, index b, slotOrder, codes, clears, transient⟩,
    ⟨reads, storageReads, codeReads, (∅ : Std.HashSet Address).insert c⟩⟩

private def observeAccount (x : Account) : Json :=
  Json.mkObj [("nonce", toJson x.nonce), ("balance", toJson x.balance.toNat),
    ("codeHash", toJson (hashNat x.codeHash))]

private def observeAccounts (m : Std.ExtTreeMap Address (Option Account)) : Json :=
  toJson (m.toList.map (fun p ↦ (p.1.toNat, (p.2.map observeAccount).getD Json.null)))

private def observeIndex {K : Type} [Ord K] [Std.TransOrd K]
    (key : K → Nat) (r : WriteOrder K) : Json :=
  Json.mkObj [("next", toJson r.next),
    ("positions", toJson (r.positions.toList.map (fun p ↦ (key p.1, p.2)))),
    ("keysByPosition", toJson (r.keysByPosition.toList.map (fun p ↦ (p.1, key p.2))))]

private def observeStorage (m : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) : Json :=
  toJson (m.toList.map (fun p ↦ (p.1.toNat, p.2.toList.map (fun q ↦ (q.1.toNat, q.2.toNat)))))

private def observeCode (m : Std.ExtTreeMap Hash32 ByteArray) : Json :=
  toJson (m.toList.map (fun p ↦ (hashNat p.1, p.2.toList.map UInt8.toNat)))

private def observeAddressSet (s : Std.HashSet Address) : Json :=
  toJson ((s.toList.map Address.toNat).mergeSort (· ≤ ·))

private def observeStorageSet (s : Std.HashSet (Address × Bytes32)) : Json :=
  toJson ((s.toList.map (fun p ↦ (p.1.toNat, p.2.toNat))).mergeSort
    (fun p q ↦ p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)))

private def observeCodeSet (s : Std.HashSet Hash32) : Json :=
  toJson ((s.toList.map hashNat).mergeSort (· ≤ ·))

private def observeSlotOrders (m : Std.ExtTreeMap Address (WriteOrder Bytes32)) : Json :=
  toJson (m.toList.map (fun p ↦ (p.1.toNat, observeIndex FixedBytes.toNat p.2)))

private def observeCommon (t : TxState Trace) : Json :=
  let b := t.block
  let r := t.rev
  let o := t.obs
  Json.mkObj [
    ("block", Json.mkObj [
      ("accountWrites", observeAccounts b.accountWrites),
      ("accountOrder", toJson (b.accountOrder.toList.map Address.toNat)),
      ("storageWrites", observeStorage b.storageWrites),
      ("codeWrites", observeCode b.codeWrites),
      ("storageClears", toJson (b.storageClears.toList.map Address.toNat)),
      ("accountReads", observeAddressSet b.accountReads),
      ("storageReads", observeStorageSet b.storageReads),
      ("codeReads", observeCodeSet b.codeReads),
      ("oldestAncestorOffset", toJson b.oldestAncestorOffset)]),
    ("tx", Json.mkObj [
      ("accountWrites", observeAccounts r.accountWrites),
      ("accountOrder", toJson (r.accountOrder.toList.map Address.toNat)),
      ("storageWrites", observeStorage r.storageWrites),
      ("codeWrites", observeCode r.codeWrites),
      ("storageClears", toJson (r.storageClears.toList.map Address.toNat)),
      ("transient", toJson (r.transient.toList.map (fun p ↦
        [p.1.1.toNat, p.1.2.toNat, p.2.toNat]))),
      ("accountReads", observeAddressSet o.accountReads),
      ("storageReads", observeStorageSet o.storageReads),
      ("codeReads", observeCodeSet o.codeReads),
      ("createdAccounts", observeAddressSet o.createdAccounts)])]

private def observe (t : TxState Trace) (calls : List Nat) : Json :=
  let b := t.block
  let r := t.rev
  Json.mkObj [("common", observeCommon t), ("calls", toJson calls),
    ("accountIndex", observeIndex Address.toNat r.accountOrder),
    ("blockAccountIndex", observeIndex Address.toNat b.accountOrder),
    ("blockStorageIndex", observeIndex Address.toNat b.storageAddressOrder),
    ("blockSlotIndexes", observeSlotOrders b.storageSlotOrder),
    ("txStorageIndex", observeIndex Address.toNat r.storageAddressOrder),
    ("txSlotIndexes", observeSlotOrders r.storageSlotOrder),
    ("consts", toJson ([b.consts.emptyCodeHash, b.consts.emptyTrieRoot,
      b.consts.emptyOmmerHash, b.consts.transferTopic].map hashNat))]

private def runHistory (h : History) : IO Json := do
  let mut t := initial h
  let mut calls := [99]
  let mut snapshots := #[observe t calls]
  for w in h.writes do
    let (a, account) := Write.decode w
    let (result, trace) := (((setAccount a account).run t).run).run calls
    match result with
    | .error _ => throw (IO.userError ("setAccount failed in " ++ h.name))
    | .ok ((), next) =>
      t := next
      calls := trace
      snapshots := snapshots.push (observe t calls)
  return Json.mkObj [("name", toJson h.name), ("snapshots", toJson snapshots)]

/-- Run the shared input catalogue and emit one complete row per history. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one input catalogue path")
  let input ← IO.FS.readFile path
  let histories ← IO.ofExcept (Json.parse input >>= (fromJson? (α := List History)))
  for h in histories do
    IO.println (← runHistory h).compress
