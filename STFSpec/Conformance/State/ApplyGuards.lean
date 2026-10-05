/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Apply

/-!
# Complete finite mathematical apply regressions

Library `EthConformance`: independent association-list model and complete raw/value observations.
These finite guards establish no WF, history, reference-host or cost theorem.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.ApplyGuards

open STFSpec.Base STFSpec.State

private structure Model where
  accounts : List (Address × Account)
  storage : List (Address × List (Bytes32 × U256))
  code : List (Hash32 × ByteArray)

private structure Changes where
  accounts : List (Address × Option Account)
  storage : List (Address × List (Bytes32 × U256))
  code : List (Hash32 × ByteArray)
  clears : List Address

private def lookup {K V : Type} [DecidableEq K] (table : List (K × V)) (key : K) : Option V :=
  (table.find? (fun row ↦ decide (row.1 = key))).map Prod.snd

private def remove {K V : Type} [DecidableEq K] (table : List (K × V)) (key : K) :
    List (K × V) := table.filter (fun row ↦ decide (row.1 ≠ key))

private def put {K V : Type} [DecidableEq K] (table : List (K × V)) (key : K) (value : V) :
    List (K × V) := remove table key ++ [(key, value)]

private def ordered {K V : Type} [Ord K] (table : List (K × V)) : List (K × V) :=
  table.mergeSort (fun x y ↦ compare x.1 y.1 != .gt)

private def canonical (m : Model) : Model :=
  ⟨ordered m.accounts, ordered m.storage |>.map (fun (a, slots) ↦ (a, ordered slots)),
    ordered m.code⟩

private def modelApply (m : Model) (d : Changes) : Model := Id.run do
  let mut storage := m.storage.filter (fun row ↦ decide (row.1 ∉ d.clears))
  let mut accounts := m.accounts
  for (a, replacement) in d.accounts do
    accounts := match replacement with
      | none => remove accounts a
      | some account => put accounts a account
  for (a, writes) in d.storage do
    let mut slots := (lookup storage a).getD []
    for (k, v) in writes do
      slots := if v = U256.zero then remove slots k else put slots k v
    storage := if slots.isEmpty then remove storage a else put storage a slots
  let mut code := m.code
  for (h, bytes) in d.code do
    code := put code h bytes
  return canonical ⟨accounts, storage, code⟩

private def build (m : Model) : MathState :=
  ⟨m.accounts.foldl (fun out (a, x) ↦ out.insert a x) ∅,
    m.storage.foldl (fun out (a, slots) ↦
      out.insert a (slots.foldl (fun inner (k, v) ↦ inner.insert k v) ∅)) ∅,
    m.code.foldl (fun out (h, bytes) ↦ out.insert h bytes) ∅⟩

private def pattern (width seed : Nat) : Nat :=
  (List.range width).foldl (fun n i ↦ n * 256 + (seed + 37 * i) % 256) 0

private def addr (n : Nat) : Address := Address.ofNat n
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)
private def bytes (xs : List UInt8) : ByteArray := (Bytes.ofList xs).toByteArray

private def addresses : List Address :=
  [addr 0, addr 1, addr (2 ^ 152), addr (2 ^ 160 - 1),
    addr (pattern 20 0), addr (pattern 20 128), addr (2 ^ 72 + 128), addr 999]
private def keys : List Bytes32 :=
  [slot 0, slot 1, slot (2 ^ 248), slot (2 ^ 256 - 1),
    slot (pattern 32 0), slot (pattern 32 128), slot (2 ^ 120 + 255), slot 999]
private def hashes : List Hash32 := keys.map Hash32.ofBytes32
private def huge : Account := ⟨2 ^ 2048 + 257, U256.max, hash (pattern 32 128)⟩
private def constants : List HashConsts :=
  [⟨hash 1, hash 999, hash 0, hash (pattern 32 128)⟩,
    ⟨hash 0, hash 1, hash (2 ^ 248), hash 999⟩,
    ⟨hash (pattern 32 128), hash (pattern 32 0), hash 1, hash 0⟩,
    HashConsts.literals]

private def base : Model :=
  ⟨[(addr 1, huge), (addr (2 ^ 152), emptyAccount HashConsts.literals)],
    [(addr 1, [(slot 1, U256.one), (slot (2 ^ 248), U256.max)]),
      (addr (2 ^ 152), []), (addr 999, [(slot 0, U256.zero)])],
    [(hash 0, ByteArray.empty), (hash 1, bytes [128, 0, 255]),
      (hash (2 ^ 248), bytes (List.range 300 |>.map UInt8.ofNat))]⟩
private def dense : Model :=
  ⟨addresses.zipIdx |>.map (fun (a, i) ↦ (a, ⟨2 ^ (256 + i) + i, U256.max, hash i⟩)),
    addresses.map (fun a ↦ (a, keys.zipIdx |>.map (fun (k, i) ↦
      (k, if i = 0 then U256.zero else U256.ofNat (2 ^ (31 * i) + i))))),
    hashes.zipIdx |>.map (fun (h, i) ↦
      (h, bytes ([0, 128, 255] ++ (List.range (65 + i)).map UInt8.ofNat)))⟩
private def nilChanges : Changes := ⟨[], [], [], []⟩
private def cases : List (Model × Changes) :=
  [(⟨[], [], []⟩, nilChanges), (base, nilChanges), (dense, nilChanges),
    (base, ⟨[(addr 1, none)], [], [], []⟩),
    (⟨[], [], []⟩, ⟨[], [(addr 999, [(slot 1, U256.one)])], [], []⟩),
    (base, ⟨[], [(addr (2 ^ 152), [])], [], []⟩),
    (base, ⟨[], [(addr 999, [])], [], []⟩),
    (base, ⟨[], [(addr 1, [(slot 1, U256.ofNat 3)])], [], [addr 1]⟩),
    (base, ⟨[], [(addr 1, [(slot 1, U256.zero)])], [], []⟩),
    (base, ⟨[], [(addr 999, [(slot 0, U256.zero)])], [], []⟩),
    (base, ⟨[], [], [(hash 1, bytes [128, 0])], []⟩),
    (base, ⟨[], [], [(hash 0, bytes [255, 0]), (hash 1, ByteArray.empty)], []⟩),
    (base, ⟨[], [], [], [addr 999, addr 0, addr (2 ^ 152)]⟩),
    (base, ⟨[], [(addr 1, []), (addr (2 ^ 152), [(slot 0, U256.zero)])], [], [addr 1]⟩),
    (base, ⟨[(addr 0, some huge), (addr 1, some (emptyAccount HashConsts.literals))],
      [], [], []⟩),
    (dense, ⟨[(addr 1, none), (addr 999, some huge)],
      [(addr 1, [(slot 1, U256.max), (slot (pattern 32 0), U256.zero)]),
        (addr (pattern 20 128), [(slot (pattern 32 128), U256.ofNat (2 ^ 255))])],
      [(hash (pattern 32 128), bytes [0, 255, 128, 0])], [addr 1, addr 999]⟩),
    (dense, ⟨addresses.map (fun a ↦ (a, none)),
      addresses.map (fun a ↦ (a, keys.map (fun k ↦ (k, U256.zero)))),
      hashes.map (fun h ↦ (h, ByteArray.empty)), addresses⟩),
    (dense, ⟨[], addresses.reverse.map (fun a ↦
      (a, keys.reverse.map (fun k ↦ (k, U256.max)))), [], []⟩)]

private def buildDiff (d : Changes) (metadata : Nat) : BlockDiff :=
  ⟨d.accounts.foldl (fun out (a, v) ↦ out.insert a v) ∅,
    if metadata = 0 then [] else [addr 999, addr 1, addr 999],
    d.storage.foldl (fun out (a, slots) ↦
      out.insert a (slots.foldl (fun inner (k, v) ↦ inner.insert k v) ∅)) ∅,
    if metadata = 0 then addresses else addresses.reverse ++ addresses,
    if metadata = 0 then ∅ else
      (∅ : Std.ExtTreeMap Address (List Bytes32)).insert (addr 999) (keys.reverse ++ keys),
    d.code.foldl (fun out (h, b) ↦ out.insert h b) ∅,
    d.clears.foldl (fun out a ↦ out.insert a) ∅⟩

private def observeAccount (x : Account) := (x.nonce, x.balance.toNat, x.codeHash.toBytes.toList)

private def observeDiff (d : BlockDiff) :=
  (d.accountChanges.toList.map (fun (a, x) ↦
      (a.toBytes.toList, x.map observeAccount)),
    d.accountOrder.map (fun a ↦ a.toBytes.toList),
    d.storageChanges.toList.map (fun (a, inner) ↦
      (a.toBytes.toList, inner.toList.map (fun (kv : Bytes32 × U256) ↦
        (kv.1.toBytes.toList, kv.2.toNat)))),
    d.storageAddressOrder.map (fun a ↦ a.toBytes.toList),
    d.storageSlotOrder.toList.map (fun (a, ks) ↦
      (a.toBytes.toList, ks.map (fun (k : Bytes32) ↦ k.toBytes.toList))),
    d.codeChanges.toList.map (fun (h, b) ↦ (h.toBytes.toList, b.toList)),
    d.storageClears.toList.map (fun a ↦ a.toBytes.toList))

private def observe (σ : MathState) (consts : HashConsts) :=
  ((σ.accounts.toList.map (fun (a, x) ↦ (a.toBytes.toList, observeAccount x)),
    σ.storage.toList.map (fun (a, inner) ↦
      (a.toBytes.toList, inner.toList.map (fun (kv : Bytes32 × U256) ↦
        (kv.1.toBytes.toList, kv.2.toNat)))),
    σ.code.toList.map (fun (h, b) ↦ (h.toBytes.toList, b.toList))),
    addresses.map (fun a ↦ ((σ.account? a).map observeAccount,
      (σ.storage[a]?).map (fun inner ↦ inner.toList.map (fun (kv : Bytes32 × U256) ↦
        (kv.1.toBytes.toList, kv.2.toNat))),
      keys.map (fun k ↦ (((σ.storage[a]?).bind (fun inner ↦ inner[k]?)).map U256.toNat,
        (σ.storageAt a k).toNat)))),
    hashes.map (fun h ↦ ((σ.code[h]?).map ByteArray.toList,
      (σ.code? consts h).map ByteArray.toList)))

private def expected (input : Model) (consts : HashConsts) :=
  let m := canonical input
  ((m.accounts.map (fun (a, x) ↦ (a.toBytes.toList, observeAccount x)),
    m.storage.map (fun (a, inner) ↦
      (a.toBytes.toList, inner.map (fun (kv : Bytes32 × U256) ↦
        (kv.1.toBytes.toList, kv.2.toNat)))),
    m.code.map (fun (h, b) ↦ (h.toBytes.toList, b.toList))),
    addresses.map (fun a ↦ ((lookup m.accounts a).map observeAccount,
      (lookup m.storage a).map (fun inner ↦ inner.map (fun (kv : Bytes32 × U256) ↦
        (kv.1.toBytes.toList, kv.2.toNat))),
      keys.map (fun k ↦
        let raw := (lookup m.storage a).bind (fun inner ↦ lookup inner k)
        (raw.map U256.toNat, (raw.getD U256.zero).toNat)))),
    hashes.map (fun h ↦ ((lookup m.code h).map ByteArray.toList,
      if h = consts.emptyCodeHash then some [] else (lookup m.code h).map ByteArray.toList)))

/-- Complete case observations and full-value comparisons for the native runner. -/
def rows : List (Bool × String) := Id.run do
  let mut result := []
  for ((input, changes), i) in cases.zipIdx do
    let σ := build input
    for (consts, j) in constants.zipIdx do
      let before := observe σ consts
      let d := buildDiff changes 0
      let e := buildDiff changes 1
      let actual := observe (σ.apply d) consts
      let reference := expected (modelApply input changes) consts
      let sibling := observe (σ.apply e) consts
      let retained := observe σ consts
      let constantsRaw := [consts.emptyCodeHash, consts.emptyTrieRoot,
        consts.emptyOmmerHash, consts.transferTopic].map (fun h ↦ h.toBytes.toList)
      let pass := before == expected input consts && actual == reference &&
        sibling == reference && retained == before
      result := result ++ [(pass,
        s!"apply/{i}/{j} consts={repr constantsRaw} diff={repr (observeDiff d)} " ++
        s!"metadataSiblingDiff={repr (observeDiff e)} before={repr before} " ++
        s!"actual={repr actual} expected={repr reference} sibling={repr sibling} " ++
        s!"retained={repr retained}")]
  return result

#guard rows.all Prod.fst

end STFSpec.Conformance.ApplyGuards
