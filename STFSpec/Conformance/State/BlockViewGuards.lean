/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete mathematical block-view controls

Library `EthConformance`: independent numerical association-list application.
Every account, optional storage map, slot and code byte is observed completely.
Finite mathematical controls imply no source runtime, witness or resource result.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.BlockViewGuards

open STFSpec.State STFSpec.Base

private abbrev AccountRecipe := Nat × Nat × Nat
private structure Model where
  accounts : List (Nat × AccountRecipe)
  storage : List (Nat × List (Nat × Nat))
  code : List (Nat × List Nat)
private structure Effects where
  accounts : List (Nat × Option AccountRecipe)
  storage : List (Nat × List (Nat × Nat))
  code : List (Nat × List Nat)
  clears : List Nat
private structure Recipe where
  state : Model
  effects : Effects

private def lookup {V : Type} (xs : List (Nat × V)) (k : Nat) : Option V :=
  (xs.find? (fun p ↦ p.1 == k)).map Prod.snd
private def remove {V : Type} (xs : List (Nat × V)) (k : Nat) : List (Nat × V) :=
  xs.filter (fun p ↦ p.1 != k)
private def put {V : Type} (xs : List (Nat × V)) (k : Nat) (v : V) : List (Nat × V) :=
  remove xs k ++ [(k, v)]
private def sorted {V : Type} (xs : List (Nat × V)) : List (Nat × V) :=
  xs.mergeSort (fun a b ↦ a.1 ≤ b.1)

-- This numerical/list oracle uses no State operation, key type or production map.
private def modelApply (s : Model) (d : Effects) : Model := Id.run do
  let mut accounts := s.accounts
  for (a, value) in d.accounts do
    accounts := match value with
      | none => remove accounts a
      | some x => put accounts a x
  let mut storage := s.storage.filter (fun p ↦ !d.clears.contains p.1)
  for (a, writes) in d.storage do
    let mut slots := (lookup storage a).getD []
    for (k, v) in writes do
      slots := if v == 0 then remove slots k else put slots k v
    storage := if slots.isEmpty then remove storage a else put storage a slots
  let mut code := s.code
  for (h, bs) in d.code do code := put code h bs
  return ⟨accounts, storage, code⟩

private def digits (width n : Nat) : List Nat :=
  (List.range width).map (fun i ↦ n / 256 ^ (width - 1 - i) % 256)
private def frame (xs : List (List Nat)) : List Nat :=
  xs.length :: xs.flatMap (fun x ↦ x.length :: x)
private def expected (s : Model) : List Nat := frame [
  frame ((sorted s.accounts).map (fun p ↦ digits 20 p.1 ++
    [p.2.1, p.2.2.1] ++ digits 32 p.2.2.2)),
  frame ((sorted s.storage).map (fun p ↦ digits 20 p.1 ++
    frame ((sorted p.2).map (fun q ↦ digits 32 q.1 ++ [q.2])))),
  frame ((sorted s.code).map (fun p ↦ digits 32 p.1 ++ p.2))]

private def address (n : Nat) : Address := Address.ofNat n
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)
private def bytes (xs : List Nat) : ByteArray := ⟨(xs.map UInt8.ofNat).toArray⟩
private def account (a : AccountRecipe) : Account := ⟨a.1, U256.ofNat a.2.1, hash a.2.2⟩
private def buildStorage (xs : List (Nat × List (Nat × Nat))) :
    Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  xs.foldl (fun t p ↦ t.insert (address p.1)
    (p.2.foldl (fun t q ↦ t.insert (slot q.1) (U256.ofNat q.2)) ∅)) ∅
private def buildCode (xs : List (Nat × List Nat)) : Std.ExtTreeMap Hash32 ByteArray :=
  xs.foldl (fun t p ↦ t.insert (hash p.1) (bytes p.2)) ∅
private def buildState (s : Model) : MathState :=
  ⟨s.accounts.foldl (fun t p ↦ t.insert (address p.1) (account p.2)) ∅,
    buildStorage s.storage, buildCode s.code⟩
private def provider (n : Nat) : PreState Id where
  getAccount? := fun _ ↦ .error (.missing (.node (hash n)))
  getStorage := fun _ _ ↦ .ok (U256.ofNat n)
  getCode := fun _ ↦ .error (.malformed (.code (hash (n + 1))))
  stateRoot := fun _ ↦ .ok (hash (n + 2))
private def constants (n : Nat) : HashConsts :=
  ⟨hash n, hash (n + 1), hash (n + 2), hash (n + 3)⟩
private def malformed {K : Type} [Ord K] [Std.TransOrd K] (key : Nat → K) : WriteOrder K :=
  ⟨2 ^ 1024 + 17, (∅ : Std.ExtTreeMap K Nat).insert (key 99) 4,
    ((∅ : Std.ExtTreeMap Nat K).insert 100 (key 7)).insert 3 (key 7)⟩
private def buildBlock (d : Effects) : BlockState Id where
  preState := provider 0
  consts := constants 0
  accountWrites := d.accounts.foldl (fun t p ↦ t.insert (address p.1) (p.2.map account)) ∅
  accountOrder := malformed address
  storageWrites := buildStorage d.storage
  storageAddressOrder := WriteOrder.empty
  storageSlotOrder := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32))
    |>.insert (address 99) (malformed slot) |>.insert (address 7) WriteOrder.empty
  codeWrites := buildCode d.code
  storageClears := d.clears.foldl (fun t a ↦ t.insert (address a)) ∅
  accountReads := ∅
  storageReads := ∅
  codeReads := ∅
  oldestAncestorOffset := none

private def observedBytes (b : ByteArray) : List Nat := b.toList.map UInt8.toNat
private def observe (s : MathState) : List Nat := frame [
  frame (s.accounts.toList.map (fun p ↦ observedBytes p.1.toBytes.toByteArray ++
    [p.2.nonce, p.2.balance.toNat] ++ observedBytes p.2.codeHash.toBytes.toByteArray)),
  frame (s.storage.toList.map (fun p ↦ observedBytes p.1.toBytes.toByteArray ++
    frame (p.2.toList.map (fun q ↦ observedBytes q.1.toBytes.toByteArray ++ [q.2.toNat])))),
  frame (s.code.toList.map (fun p ↦ observedBytes p.1.toBytes.toByteArray ++ observedBytes p.2))]

private def base (a k h : Nat) : Recipe :=
  let huge := (2 ^ 1024 + 17, 2 ^ 256 - 1, h)
  ⟨⟨[(a + 1, huge), (7, (0, 0, 0))],
      [(a + 1, [(k + 1, 0), (7, 99)]), (7, []), (99, [(7, 0)])],
      [(0, [128, 0, 255]), (h + 1, [])]⟩,
    ⟨[(a + 1, none), (8, some huge)],
      [(7, []), (99, [(7, 0)]), (8, [(k + 1, 2 ^ 255 + 9)])],
      [(0, [255, 0]), (h + 1, [0, 129, 255, 0])], [8]⟩⟩
private def special : List Recipe :=
  let r := base 0 0 0
  [⟨⟨[], [], []⟩, ⟨[], [], [], []⟩⟩,
    { r with effects := ⟨[], [], [], []⟩ },
    { r with effects := ⟨[(1, none)], [], [], []⟩ },
    { r with effects := ⟨[], [(99, [(7, 1)])], [], []⟩ },
    { r with effects := ⟨[], [(1, [(7, 0)])], [], []⟩ },
    { r with effects := ⟨[], [(1, [])], [], [1]⟩ },
    { r with effects := ⟨[], [(1, [(7, 17)])], [], [1]⟩ },
    { r with effects := ⟨[], [(7, [])], [], []⟩ },
    { r with effects := ⟨[], [], [(0, []), (1, [255, 128, 0])], []⟩ }, r]
private def recipes : List Recipe := special ++
  (List.range 20).map (fun i ↦ base (129 * 256 ^ i) 0 0) ++
  (List.range 32).map (fun i ↦ base 0 (129 * 256 ^ i) 0) ++
  (List.range 32).map (fun i ↦ base 0 0 (129 * 256 ^ i))

private def permute (r : Recipe) : Recipe :=
  ⟨⟨r.state.accounts.reverse, r.state.storage.reverse.map (fun p ↦ (p.1, p.2.reverse)),
      r.state.code.reverse⟩,
    ⟨r.effects.accounts.reverse,
      r.effects.storage.reverse.map (fun p ↦ (p.1, p.2.reverse)),
      r.effects.code.reverse, r.effects.clears.reverse⟩⟩
private def ignored (b : BlockState Id) : List (BlockState Id) :=
  [{ b with preState := provider (2 ^ 255 + 7) },
    { b with consts := constants (2 ^ 255 + 7) },
    { b with accountReads := (∅ : Std.HashSet Address).insert (address 99) },
    { b with storageReads := (∅ : Std.HashSet (Address × Bytes32)).insert (address 99, slot 9) },
    { b with codeReads := (∅ : Std.HashSet (Address × Hash32)).insert (address 99, hash 9) },
    { b with oldestAncestorOffset := some 0 },
    { b with oldestAncestorOffset := some (2 ^ 1024 + 17) },
    { b with accountOrder := WriteOrder.empty },
    { b with storageAddressOrder := malformed address },
    { b with storageSlotOrder := ∅ }]
private def controls : List (List Nat × List Nat) := recipes.flatMap fun r ↦
  let s := buildState r.state
  let b := buildBlock r.effects
  let sibling := { b with codeWrites := ∅ }
  let want := expected (modelApply r.state r.effects)
  let wantSibling := expected (modelApply r.state { r.effects with code := [] })
  let p := permute r
  [(observe (b.view s), want),
    (observe ((buildBlock p.effects).view (buildState p.state)), want),
    (observe (sibling.view s), wantSibling), (observe s, expected r.state)] ++
  (ignored b).map (fun c ↦ (observe (c.view s), want)) ++
  [(observe (b.view s), want), (observe (sibling.view s), wantSibling),
    (observe s, expected r.state)]

#guard controls.all (fun p ↦ p.1 == p.2)
#guard recipes.length == 94
#guard controls.length == 1598

end STFSpec.Conformance.State.BlockViewGuards
