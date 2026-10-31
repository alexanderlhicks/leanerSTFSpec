/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete raw block-state controls

Library `EthConformance`: independent finite numeric recipes and complete framed
observations of all thirteen fields, including supplied callback arguments/results.
These synthetic callbacks test storage only; they interpret no original Protocol
operation or generic effect. Retained siblings establish no ownership/cost theorem.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.BlockStateGuards

open STFSpec.State STFSpec.Base

variable {α : Type}

private def address (n : Nat) : Address := Address.ofNat n
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)
private def bytes (ns : List Nat) : ByteArray := ByteArray.mk ((ns.map UInt8.ofNat).toArray)

-- Every list and optional tag is framed; neither counts nor partial keys stand in for payloads.
private def sequence (xs : List (List Nat)) : List Nat :=
  xs.length :: xs.flatMap (fun x ↦ x.length :: x)
private def optional (f : α → List Nat) : Option α → List Nat
  | none => [0]
  | some x => 1 :: f x
private def byteValues (b : ByteArray) : List Nat := b.toList.map UInt8.toNat
private def addressValues (a : Address) : List Nat := a.toBytes.toList.map UInt8.toNat
private def slotValues (k : Bytes32) : List Nat := k.toBytes.toList.map UInt8.toNat
private def hashValues (h : Hash32) : List Nat := h.toBytes.toList.map UInt8.toNat
private def digits (width n : Nat) : List Nat :=
  (List.range width).map (fun i ↦ (n / 256 ^ (width - 1 - i)) % 256)

private def accountValues (a : Account) : List Nat :=
  [a.nonce, a.balance.toNat] ++ hashValues a.codeHash
private def itemValues : WitnessItem → List Nat
  | .node h => 0 :: hashValues h
  | .code h => 1 :: hashValues h
  | .leaf => [2]
private def errorValues : WitnessError → List Nat
  | .missing i => 0 :: itemValues i
  | .malformed i => 1 :: itemValues i
  | .unresolved h => 2 :: hashValues h
private def resultValues (f : α → List Nat) : Except WitnessError α → List Nat
  | .ok x => 0 :: f x
  | .error e => 1 :: errorValues e

private def suppliedError (seed : Nat) : WitnessError :=
  match seed % 7 with
  | 0 => .missing (.node (digest seed))
  | 1 => .missing (.code (digest seed))
  | 2 => .missing .leaf
  | 3 => .malformed (.node (digest seed))
  | 4 => .malformed (.code (digest seed))
  | 5 => .malformed .leaf
  | _ => .unresolved (digest seed)

private def expectedError (seed : Nat) : List Nat :=
  match seed % 7 with
  | 0 => [0, 0] ++ digits 32 seed
  | 1 => [0, 1] ++ digits 32 seed
  | 2 => [0, 2]
  | 3 => [1, 0] ++ digits 32 seed
  | 4 => [1, 1] ++ digits 32 seed
  | 5 => [1, 2]
  | _ => 2 :: digits 32 seed

private def provider (seed : Nat) : PreState Id where
  getAccount? := fun a ↦
    if a.toNat % 3 = 0 then .ok none
    else if a.toNat % 3 = 1 then
      .ok (some ⟨2 ^ 1024 + seed + a.toNat, U256.ofNat (2 ^ 256 - 1), digest seed⟩)
    else .error (suppliedError seed)
  getStorage := fun a k ↦
    if (a.toNat + k.toNat) % 3 = 0 then .ok U256.zero
    else if (a.toNat + k.toNat) % 3 = 1 then .ok (U256.ofNat (2 ^ 255 + seed))
    else .error (suppliedError seed)
  getCode := fun h ↦
    if h.toBytes32.toNat % 3 = 0 then .ok ByteArray.empty
    else if h.toBytes32.toNat % 3 = 1 then .ok (bytes (seed :: hashValues h ++ [255, 0]))
    else .error (suppliedError seed)
  stateRoot := fun d ↦
    if d.accountOrder.length % 2 = 0 then .ok (digest (seed + d.storageAddressOrder.length))
    else .error (suppliedError seed)

private structure Index where
  next : Nat
  positions : List (Nat × Nat)
  reverse : List (Nat × Nat)

private structure Recipe where
  seed : Nat
  consts : Nat × Nat × Nat × Nat
  accounts : List (Nat × Option (Nat × Nat × Nat))
  accountIndex : Index
  storage : List (Nat × List (Nat × Nat))
  addressIndex : Index
  slotIndexes : List (Nat × Index)
  code : List (Nat × List Nat)
  clears : List Nat
  accountReads : List Nat
  storageReads : List (Nat × Nat)
  codeReads : List (Nat × Nat)
  offset : Option Nat

private def account (v : Nat × Nat × Nat) : Account :=
  ⟨v.1, U256.ofNat v.2.1, digest v.2.2⟩
private def addressIndex (r : Index) : WriteOrder Address :=
  ⟨r.next, r.positions.foldl (fun m p ↦ m.insert (address p.1) p.2) ∅,
    r.reverse.foldl (fun m p ↦ m.insert p.1 (address p.2)) ∅⟩
private def slotIndex (r : Index) : WriteOrder Bytes32 :=
  ⟨r.next, r.positions.foldl (fun m p ↦ m.insert (slot p.1) p.2) ∅,
    r.reverse.foldl (fun m p ↦ m.insert p.1 (slot p.2)) ∅⟩
private def supplied (r : Recipe) : BlockState Id :=
  ⟨provider r.seed, ⟨digest r.consts.1, digest r.consts.2.1,
      digest r.consts.2.2.1, digest r.consts.2.2.2⟩,
    r.accounts.foldl (fun m p ↦ m.insert (address p.1) (p.2.map account)) ∅,
    addressIndex r.accountIndex,
    r.storage.foldl (fun m p ↦ m.insert (address p.1)
      (p.2.foldl (fun m q ↦ m.insert (slot q.1) (U256.ofNat q.2)) ∅)) ∅,
    addressIndex r.addressIndex,
    r.slotIndexes.foldl (fun m p ↦ m.insert (address p.1) (slotIndex p.2)) ∅,
    r.code.foldl (fun m p ↦ m.insert (digest p.1) (bytes p.2)) ∅,
    r.clears.foldl (fun s n ↦ s.insert (address n)) ∅,
    r.accountReads.foldl (fun s n ↦ s.insert (address n)) ∅,
    r.storageReads.foldl (fun s p ↦ s.insert (address p.1, slot p.2)) ∅,
    r.codeReads.foldl (fun s p ↦ s.insert (address p.1, digest p.2)) ∅, r.offset⟩

private def observeIndex {K : Type} [Ord K] [Std.TransOrd K]
    (key : K → List Nat) (r : WriteOrder K) : List Nat :=
  sequence [[r.next], sequence (r.positions.toList.map (fun p ↦ key p.1 ++ [p.2])),
    sequence (r.keysByPosition.toList.map (fun p ↦ p.1 :: key p.2)),
    sequence (r.toList.map key)]

private def probes : List Nat := [0, 1, 2, 3, 4, 5, 2 ^ 159 + 7, 2 ^ 159 + 8]
private def probePairs : List (Nat × Nat) :=
  probes.flatMap (fun x ↦ probes.map (fun y ↦ (x, y)))
private def rootInputs : List BlockDiff :=
  [⟨∅, [], ∅, [], ∅, ∅, ∅⟩,
   ⟨(∅ : Std.ExtTreeMap Address (Option Account)).insert (address 9) none,
    [address 9, address 9, address 2],
    (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert (address 7)
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot (2 ^ 255)) U256.zero),
    [address 7, address 7],
    (∅ : Std.ExtTreeMap Address (List Bytes32)).insert (address 99) [slot 4, slot 4],
    (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (digest (2 ^ 255)) (bytes [0, 255]),
    (∅ : Std.ExtTreeSet Address).insert (address 5)⟩]

private def observeDiff (d : BlockDiff) : List Nat :=
  sequence [sequence (d.accountChanges.toList.map (fun p ↦ addressValues p.1 ++ optional
      accountValues p.2)),
    sequence (d.accountOrder.map addressValues),
    sequence (d.storageChanges.toList.map (fun p ↦ addressValues p.1 ++
      sequence (p.2.toList.map (fun q ↦ slotValues q.1 ++ [q.2.toNat])))),
    sequence (d.storageAddressOrder.map addressValues),
    sequence (d.storageSlotOrder.toList.map (fun p ↦ addressValues p.1 ++ sequence (p.2.map
        slotValues))),
    sequence (d.codeChanges.toList.map (fun p ↦ hashValues p.1 ++ byteValues p.2)),
    sequence (d.storageClears.toList.map addressValues)]

private def observeProvider (ps : PreState Id) : List Nat :=
  sequence [sequence (probes.map (fun n ↦ addressValues (address n) ++
      resultValues (optional accountValues) (ps.getAccount? (address n)))),
    sequence (probePairs.map (fun p ↦ addressValues (address p.1) ++ slotValues (slot p.2) ++
      resultValues (fun v ↦ [v.toNat]) (ps.getStorage (address p.1) (slot p.2)))),
    sequence (probes.map (fun n ↦ hashValues (digest n) ++ resultValues byteValues (ps.getCode
        (digest n)))),
    sequence (rootInputs.map (fun d ↦ sequence [observeDiff d, resultValues hashValues
        (ps.stateRoot d)]))]

private def observe (b : BlockState Id) : List Nat :=
  sequence [observeProvider b.preState,
    sequence [hashValues b.consts.emptyCodeHash, hashValues b.consts.emptyTrieRoot,
      hashValues b.consts.emptyOmmerHash, hashValues b.consts.transferTopic],
    sequence (b.accountWrites.toList.map (fun p ↦ addressValues p.1 ++ optional accountValues
        p.2)),
    observeIndex addressValues b.accountOrder,
    sequence (b.storageWrites.toList.map (fun p ↦ addressValues p.1 ++
      sequence (p.2.toList.map (fun q ↦ slotValues q.1 ++ [q.2.toNat])))),
    observeIndex addressValues b.storageAddressOrder,
    sequence (b.storageSlotOrder.toList.map (fun p ↦ addressValues p.1 ++ observeIndex slotValues
        p.2)),
    sequence (b.codeWrites.toList.map (fun p ↦ hashValues p.1 ++ byteValues p.2)),
    sequence (b.storageClears.toList.map addressValues),
    sequence ((b.accountReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      addressValues),
    sequence ((b.storageReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      (fun p ↦ addressValues p.1 ++ slotValues p.2)),
    sequence ((b.codeReads.toList.mergeSort (fun x y ↦
      (compare x.1 y.1).then (compare x.2 y.2) != .gt)).map
        (fun p ↦ addressValues p.1 ++ hashValues p.2)),
    optional (fun n ↦ [n]) b.oldestAncestorOffset]

-- Independent association-list last-write and sorting model; no Std container is built here.
private def normalized (xs : List (Nat × α)) : List (Nat × α) :=
  (xs.foldl (fun acc p ↦ acc.filter (fun q ↦ q.1 != p.1) ++ [p]) []).mergeSort
    (fun p q ↦ p.1 ≤ q.1)
private def expectedIndex (width : Nat) (r : Index) : List Nat :=
  let forward := normalized (r.positions.map (fun p ↦ (p.1 % 256 ^ width, p.2)))
  let reverse := normalized r.reverse
  sequence [[r.next], sequence (forward.map (fun p ↦ digits width p.1 ++ [p.2])),
    sequence (reverse.map (fun p ↦ p.1 :: digits width p.2)),
    sequence (reverse.map (fun p ↦ digits width p.2))]
private def expectedAccount (v : Nat × Nat × Nat) : List Nat :=
  [v.1, v.2.1 % 2 ^ 256] ++ digits 32 v.2.2
private def expectedAddresses (ns : List Nat) : List Nat :=
  sequence (((ns.map (fun n ↦ n % 2 ^ 160)).eraseDups).mergeSort (· ≤ ·) |>.map (digits 20))
private def expectedPairs (ps : List (Nat × Nat)) : List Nat :=
  sequence (((ps.map (fun p ↦ (p.1 % 2 ^ 160, p.2 % 2 ^ 256))).eraseDups).mergeSort
    (fun p q ↦ (compare p.1 q.1).then (compare p.2 q.2) != .gt) |>.map
      (fun p ↦ digits 20 p.1 ++ digits 32 p.2))

private def expectedProvider (seed : Nat) : List Nat :=
  sequence [sequence (probes.map (fun n ↦ digits 20 n ++
      if n % 3 = 0 then [0, 0]
      else if n % 3 = 1 then [0, 1, 2 ^ 1024 + seed + n, 2 ^ 256 - 1] ++ digits 32 seed
      else 1 :: expectedError seed)),
    sequence (probePairs.map (fun p ↦ digits 20 p.1 ++ digits 32 p.2 ++
      if (p.1 + p.2) % 3 = 0 then [0, 0]
      else if (p.1 + p.2) % 3 = 1 then [0, (2 ^ 255 + seed) % 2 ^ 256]
      else 1 :: expectedError seed)),
    sequence (probes.map (fun n ↦ digits 32 n ++
      if n % 3 = 0 then [0]
      else if n % 3 = 1 then [0, seed % 256] ++ digits 32 n ++ [255, 0]
      else 1 :: expectedError seed)),
    sequence (rootInputs.map (fun d ↦ sequence [observeDiff d,
      if d.accountOrder.length % 2 = 0 then 0 :: digits 32 (seed + d.storageAddressOrder.length)
      else 1 :: expectedError seed]))]

private def expected (r : Recipe) : List Nat :=
  sequence [expectedProvider r.seed,
    sequence [digits 32 r.consts.1, digits 32 r.consts.2.1, digits 32 r.consts.2.2.1, digits 32
        r.consts.2.2.2],
    sequence ((normalized (r.accounts.map (fun p ↦ (p.1 % 2 ^ 160, p.2)))).map
      (fun p ↦ digits 20 p.1 ++ optional expectedAccount p.2)),
    expectedIndex 20 r.accountIndex,
    sequence ((normalized (r.storage.map (fun p ↦ (p.1 % 2 ^ 160, p.2)))).map
      (fun p ↦ digits 20 p.1 ++
        sequence ((normalized (p.2.map (fun q ↦ (q.1 % 2 ^ 256, q.2)))).map
          (fun q ↦ digits 32 q.1 ++ [q.2 % 2 ^ 256])))),
    expectedIndex 20 r.addressIndex,
    sequence ((normalized (r.slotIndexes.map (fun p ↦ (p.1 % 2 ^ 160, p.2)))).map
      (fun p ↦ digits 20 p.1 ++ expectedIndex 32 p.2)),
    sequence ((normalized (r.code.map (fun p ↦ (p.1 % 2 ^ 256, p.2)))).map
      (fun p ↦ digits 32 p.1 ++ p.2.map (· % 256))),
    expectedAddresses r.clears, expectedAddresses r.accountReads,
    expectedPairs r.storageReads, expectedPairs r.codeReads, optional (fun n ↦ [n]) r.offset]

private def rawIndex (n : Nat) : Index :=
  ⟨2 ^ 100 + n, [(9, 100), (2, 4), (9, 6), (2 ^ 159 + 3, 4)],
    [(100, 9), (4, 2), (2 ^ 140 + 7, 9), (6, 9)]⟩
private def parentRecipe : Recipe :=
  ⟨2 ^ 255 + 9, (2 ^ 255 + 1, 2 ^ 254 + 2, 2 ^ 253 + 3, 2 ^ 252 + 4),
    [(8, some (0, 0, 0)), (2 ^ 159 + 1, none), (8, some (2 ^ 1024 + 17, 2 ^ 256 - 1, 2 ^ 255 + 9)),
      (99, none)], rawIndex 7,
    [(8, [(4, 0), (2 ^ 255 + 3, 2 ^ 256 - 1), (4, 17)]), (99, []), (3, [(7, 0)])],
    rawIndex 19,
    [(123, rawIndex 27), (8, ⟨0, [(2 ^ 255, 7)], [(9, 2 ^ 255), (100, 2 ^ 255)]⟩)],
    [(2 ^ 255, [0, 128, 255, 0]), (0, []), (2 ^ 255, [255, 0, 129, 7])],
    [6, 6, 2 ^ 159 + 8], [1, 1 + 2 ^ 160, 2 ^ 159 + 9],
    [(3, 4), (3 + 2 ^ 160, 4 + 2 ^ 256), (8, 4), (3, 9)],
    [(9, 2 ^ 255), (9, 7), (8, 2 ^ 255)], some (2 ^ 1024 + 99)⟩
private def otherRecipe : Recipe :=
  ⟨1, (17, 18, 19, 20), [(0, none), (1, some (2, 3, 4))], ⟨0, [], []⟩,
    [(7, []), (2, [(3, 0)])], ⟨0, [(5, 2)], []⟩, [], [(77, [255, 0])],
    [91], [92], [(93, 94)], [(95, 96)], none⟩

private def controls : List (BlockState Id × Recipe) := Id.run do
  let p := supplied parentRecipe
  let q := supplied otherRecipe
  let mut cs := [(p, parentRecipe), (q, otherRecipe)]
  cs := cs ++ [({ p with preState := q.preState }, { parentRecipe with seed := otherRecipe.seed }),
    ({ p with consts := q.consts }, { parentRecipe with consts := otherRecipe.consts }),
    ({ p with accountWrites := q.accountWrites },
      { parentRecipe with accounts := otherRecipe.accounts }),
    ({ p with accountOrder := q.accountOrder },
      { parentRecipe with accountIndex := otherRecipe.accountIndex }),
    ({ p with storageWrites := q.storageWrites },
      { parentRecipe with storage := otherRecipe.storage }),
    ({ p with storageAddressOrder := q.storageAddressOrder },
      { parentRecipe with addressIndex := otherRecipe.addressIndex }),
    ({ p with storageSlotOrder := q.storageSlotOrder },
      { parentRecipe with slotIndexes := otherRecipe.slotIndexes }),
    ({ p with codeWrites := q.codeWrites }, { parentRecipe with code := otherRecipe.code }),
    ({ p with storageClears := q.storageClears },
      { parentRecipe with clears := otherRecipe.clears }),
    ({ p with accountReads := q.accountReads },
      { parentRecipe with accountReads := otherRecipe.accountReads }),
    ({ p with storageReads := q.storageReads },
      { parentRecipe with storageReads := otherRecipe.storageReads }),
    ({ p with codeReads := q.codeReads },
      { parentRecipe with codeReads := otherRecipe.codeReads }),
    ({ p with oldestAncestorOffset := some 0 }, { parentRecipe with offset := some 0 }),
    ({ p with oldestAncestorOffset := none }, { parentRecipe with offset := none }),
    (p, parentRecipe), (q, otherRecipe)]
  for i in List.range 7 do
    let r := { parentRecipe with seed := 2 ^ 255 + i }
    cs := cs ++ [(supplied r, r)]
  for i in List.range 32 do
    let n := 129 * 256 ^ i + 17
    let r := { parentRecipe with
      consts := (n, n + 1, n + 2, n + 3)
      storage := [(8, [(n, 0), (n + 1, 2 ^ 255 + n)])]
      code := [(n, [0, 255, i, 129])]
      storageReads := [(3, n), (8, n)]
      codeReads := [(3, n), (8, n)] }
    cs := cs ++ [(supplied r, r)]
  for i in List.range 20 do
    let n := 129 * 256 ^ i + 17
    let r := { parentRecipe with
      accounts := [(n, none), (n + 1, some (n, n, n))]
      storage := [(n, [])]
      clears := [n]
      accountReads := [n + 1]
      storageReads := [(n, 7), (n + 1, 7)]
      codeReads := [(n, 9), (n + 1, 9)] }
    cs := cs ++ [(supplied r, r)]
  return cs

private def completeControls : Bool := controls.all (fun c ↦ observe c.1 == expected c.2)

#guard completeControls
#guard observe (supplied { parentRecipe with offset := none }) !=
  observe (supplied { parentRecipe with offset := some 0 })
#guard observe (supplied parentRecipe) != observe (supplied otherRecipe)

end STFSpec.Conformance.State.BlockStateGuards
