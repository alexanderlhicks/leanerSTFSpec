/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Current storage read controls

Library `EthConformance`. Exercise R11 through the State facade under a tracing
base monad. The compared frames retain all state fields and probe the provider's
four retained callbacks at fixed inputs.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.CurrentStorageGuards

open STFSpec.State STFSpec.Base

private abbrev Trace := StateT (List (List Nat)) Id

private def address : Address := Address.ofNat (2 ^ 160 - 1)
private def otherAddress : Address := Address.ofNat (2 ^ 159 - 1)
private def key : Bytes32 := FixedBytes.ofNat (2 ^ 256 - 1)
private def otherKey : Bytes32 := FixedBytes.ofNat (2 ^ 255 - 1)
private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def errorHash : Hash32 := digest (2 ^ 255 + 2 ^ 128 + 255)

private structure History where
  txPatch : Nat
  txClear : Bool
  blockPatch : Nat
  blockClear : Bool
  fails : Bool
  created : Bool

private def provider (fails : Bool) : PreState Trace where
  getAccount? a := do
    modify (· ++ [[1, a.toNat]])
    pure (.ok (some ⟨61, U256.ofNat 62, digest 63⟩))
  getStorage a k := do
    let calls ← get
    set (calls ++ [[0, a.toNat, k.toNat]])
    if fails then pure (.error (.malformed (.node errorHash)))
    else pure (.ok (U256.ofNat (717 + 2 * calls.length)))
  getCode h := do
    modify (· ++ [[2, h.toNat]])
    pure (.ok ⟨#[68, 0, 255]⟩)
  stateRoot d := do
    modify (· ++ [3 :: d.accountOrder.map Address.toNat])
    pure (.ok (digest 71))

private def writes (patch amount unrelated : Nat) :
    Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  let atOther := (∅ : Std.ExtTreeMap Bytes32 U256).insert key (U256.ofNat unrelated)
  let base := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    |>.insert otherAddress atOther
  let wrong := (∅ : Std.ExtTreeMap Bytes32 U256).insert otherKey (U256.ofNat (amount - 1))
  match patch with
  | 0 => base
  | 1 => base.insert address ∅
  | 2 => base.insert address wrong
  | 3 => base.insert address ((∅ : Std.ExtTreeMap Bytes32 U256).insert key U256.zero)
  | _ => base.insert address (wrong.insert key (U256.ofNat amount))

private def clears (clear : Bool) : Std.ExtTreeSet Address :=
  let old := (∅ : Std.ExtTreeSet Address).insert otherAddress
  if clear then old.insert address else old

private def index {K : Type} [Ord K] [Std.TransOrd K] (k : K) (n : Nat) : WriteOrder K :=
  ⟨2 ^ 301 + n, (∅ : Std.ExtTreeMap K Nat).insert k n,
    (∅ : Std.ExtTreeMap Nat K).insert (n + 1) k⟩

private def initial (r : History) : TxState Trace :=
  let block : BlockState Trace := {
    preState := provider r.fails
    consts := ⟨digest 11, digest 12, digest 13, digest 14⟩
    accountWrites := (∅ : Std.ExtTreeMap Address (Option Account)).insert address none
    accountOrder := index otherAddress 7
    storageWrites := writes r.blockPatch 313 271
    storageAddressOrder := index otherAddress 8
    storageSlotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
      |>.insert otherAddress (index key 9)
    codeWrites := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (digest 41) ⟨#[0, 255]⟩
    storageClears := clears r.blockClear
    accountReads := (∅ : Std.HashSet Address).insert address
    storageReads := (∅ : Std.HashSet (Address × Bytes32)).insert (otherAddress, key)
    codeReads := (∅ : Std.HashSet Hash32).insert (digest 43)
    oldestAncestorOffset := some (2 ^ 300) }
  let rev : TxRevertible := {
    accountWrites := (∅ : Std.ExtTreeMap Address (Option Account)).insert otherAddress none
    accountOrder := index address 17
    storageWrites := writes r.txPatch 113 272
    storageAddressOrder := index address 18
    storageSlotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
      |>.insert address (index otherKey 19)
    codeWrites := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (digest 42) ⟨#[128, 0, 1]⟩
    storageClears := clears r.txClear
    transient := (∅ : Std.ExtTreeMap (Address × Bytes32) U256)
      |>.insert (address, key) (U256.ofNat 472) }
  let accountReads := (∅ : Std.HashSet Address).insert otherAddress
  ⟨block, rev, ⟨accountReads,
    (∅ : Std.HashSet (Address × Bytes32)).insert (otherAddress, otherKey),
    (∅ : Std.HashSet Hash32).insert (digest 44),
    if r.created then accountReads.insert address else accountReads⟩⟩

private def sequence (xs : List (List Nat)) : List Nat :=
  xs.length :: xs.flatMap (fun x ↦ x.length :: x)

private def accountValues (a : Account) : List Nat := [a.nonce, a.balance.toNat, a.codeHash.toNat]

private def itemValues : WitnessItem → List Nat
  | .node h => [0, h.toNat]
  | .code h => [1, h.toNat]
  | .leaf => [2]

private def errorValues : WitnessError → List Nat
  | .missing item => 0 :: itemValues item
  | .malformed item => 1 :: itemValues item
  | .unresolved h => [2, h.toNat]

private def resultValues {α : Type} (f : α → List Nat) : Except WitnessError α → List Nat
  | .ok x => 0 :: f x
  | .error e => 1 :: errorValues e

private def storageReads (t : TxState Trace) : List (Address × Bytes32) :=
  t.obs.storageReads.toList.mergeSort (fun p q ↦ compare p q != .gt)

private def slotPair (p : Address × Bytes32) : List Nat := [p.1.toNat, p.2.toNat]

private def accounts (m : Std.ExtTreeMap Address (Option Account)) : List Nat :=
  sequence (m.toList.map (fun (a, o) ↦ a.toNat :: (o.map accountValues).getD []))

private def storage (m : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) : List Nat :=
  sequence (m.toList.map (fun (a, ws) ↦ a.toNat ::
    sequence (ws.toList.map (fun (k, v) ↦ [k.toNat, v.toNat]))))

private def code (m : Std.ExtTreeMap Hash32 ByteArray) : List Nat :=
  sequence (m.toList.map (fun (h, b) ↦ h.toNat :: b.toList.map UInt8.toNat))

private def addressSet (s : Std.HashSet Address) : List Nat :=
  (s.toList.map Address.toNat).mergeSort (· ≤ ·)

private def sharedFrame (t : TxState Trace) : List (List Nat) :=
  let b := t.block
  let r := t.rev
  [accounts b.accountWrites, storage b.storageWrites, code b.codeWrites,
    b.storageClears.toList.map Address.toNat, addressSet b.accountReads,
    sequence (b.storageReads.toList.map slotPair |>.mergeSort (fun p q ↦ compare p q != .gt)),
    (b.codeReads.toList.map Hash32.toNat).mergeSort (· ≤ ·), b.oldestAncestorOffset.toList,
    accounts r.accountWrites, storage r.storageWrites, code r.codeWrites,
    r.storageClears.toList.map Address.toNat,
    sequence (r.transient.toList.map (fun (p, v) ↦ slotPair p ++ [v.toNat])),
    addressSet t.obs.accountReads, (t.obs.codeReads.toList.map Hash32.toNat).mergeSort (· ≤ ·),
    addressSet t.obs.createdAccounts]

private def indexValues {K : Type} [Ord K] [Std.TransOrd K] (f : K → Nat)
    (r : WriteOrder K) : List Nat :=
  r.next :: (sequence (r.positions.toList.map (fun (k, p) ↦ [f k, p])) ++
    sequence (r.keysByPosition.toList.map (fun (p, k) ↦ [p, f k])))

private def slotIndexes (m : Std.ExtTreeMap Address (WriteOrder Bytes32)) : List Nat :=
  sequence (m.toList.map (fun (a, r) ↦ a.toNat :: indexValues FixedBytes.toNat r))

private def callback {α : Type} (f : α → List Nat) (call : Trace (Except WitnessError α)) :
    List Nat :=
  let (answer, effects) := call.run []
  sequence [resultValues f answer, sequence effects]

private def leanFrame (t : TxState Trace) : List (List Nat) :=
  let b := t.block
  let r := t.rev
  let c := b.consts
  let ps := b.preState
  [[c.emptyCodeHash.toNat, c.emptyTrieRoot.toNat, c.emptyOmmerHash.toNat, c.transferTopic.toNat],
    indexValues Address.toNat b.accountOrder, indexValues Address.toNat b.storageAddressOrder,
    slotIndexes b.storageSlotOrder, indexValues Address.toNat r.accountOrder,
    indexValues Address.toNat r.storageAddressOrder, slotIndexes r.storageSlotOrder,
    callback (fun o ↦ (o.map accountValues).getD []) (ps.getAccount? otherAddress),
    callback (fun v ↦ [v.toNat]) (ps.getStorage otherAddress otherKey),
    callback (fun b ↦ b.toList.map UInt8.toNat) (ps.getCode (digest 29)),
    callback (fun h ↦ [h.toNat]) (ps.stateRoot { extractBlockDiff b with accountOrder := [address] })]

private def runRead (t : TxState Trace) (calls : List (List Nat)) :=
  (((getStorage address key).run t).run).run calls

private def answer : Except StateError (U256 × TxState Trace) → List Nat
  | .ok (v, _) => [0, v.toNat]
  | .error (.witness e) => 1 :: 0 :: errorValues e
  | .error .balanceUnderflow => [1, 1]
  | .error .balanceOverflow => [1, 2]
  | .error .storageOnMissingAccount => [1, 3]

private def check (r : History) (values : List (List Nat)) (calls : List (List Nat)) : Bool :=
  let t := initial r
  let (first, firstCalls) := runRead t []
  let (second, secondCalls) := runRead ((first.toOption.map Prod.snd).getD t) firstCalls
  [answer first, answer second] == values && secondCalls == calls &&
    [first, second].all (fun result ↦ match result with
      | .error _ => true
      | .ok (_, next) =>
        (storageReads next).map slotPair == [[otherAddress.toNat, otherKey.toNat],
          [address.toNat, key.toNat]] &&
        sharedFrame next == sharedFrame t && leanFrame next == leanFrame t)

#guard check ⟨3, true, 4, true, true, true⟩ [[0, 0], [0, 0]] []
#guard check ⟨4, false, 3, true, true, false⟩ [[0, 113], [0, 113]] []
#guard check ⟨1, true, 4, false, true, false⟩ [[0, 0], [0, 0]] []
#guard check ⟨2, false, 4, true, true, true⟩ [[0, 313], [0, 313]] []
#guard check ⟨0, false, 3, true, true, false⟩ [[0, 0], [0, 0]] []
#guard check ⟨2, false, 2, true, true, true⟩ [[0, 0], [0, 0]] []
#guard check ⟨0, false, 1, false, false, true⟩ [[0, 717], [0, 719]]
  [[0, 2 ^ 160 - 1, 2 ^ 256 - 1], [0, 2 ^ 160 - 1, 2 ^ 256 - 1]]
#guard check ⟨1, false, 2, false, true, false⟩
  [[1, 0, 1, 0, 2 ^ 255 + 2 ^ 128 + 255], [1, 0, 1, 0, 2 ^ 255 + 2 ^ 128 + 255]]
  [[0, 2 ^ 160 - 1, 2 ^ 256 - 1], [0, 2 ^ 160 - 1, 2 ^ 256 - 1]]

private def checkModel (r : History) (expected : Nat) : Bool :=
  let raw := initial r
  let c := raw.block.consts
  let acct : Account := ⟨0, U256.one, c.emptyCodeHash⟩
  let σ : MathState := {
    accounts := ((∅ : Std.ExtTreeMap Address Account).insert address acct)
      |>.insert otherAddress acct
    storage := writes 4 571 572
    code := ∅ }
  let ps : PreState Id := {
    getAccount? := fun a ↦ .ok (σ.account? a)
    getStorage := fun a k ↦ .ok (σ.storageAt a k)
    getCode := fun h ↦ match σ.code? c h with
      | some b => .ok b
      | none => .error (.missing (.code h))
    stateRoot := fun _ ↦ .error (.missing .leaf) }
  let b := { BlockState.new ps c with
    storageWrites := raw.block.storageWrites
    storageClears := raw.block.storageClears }
  let t : TxState Id := ⟨b, raw.rev, raw.obs⟩
  match ((getStorage address key).run t).run with
  | .error _ => false
  | .ok (value, _) => value.toNat == expected && value == (t.view σ).storageAt address key

#guard checkModel ⟨3, true, 4, false, false, false⟩ 0
#guard checkModel ⟨2, true, 4, false, false, false⟩ 0
#guard checkModel ⟨1, false, 4, true, false, false⟩ 313
#guard checkModel ⟨1, false, 1, true, false, false⟩ 0
#guard checkModel ⟨2, false, 0, false, false, true⟩ 571

end STFSpec.Conformance.State.CurrentStorageGuards
