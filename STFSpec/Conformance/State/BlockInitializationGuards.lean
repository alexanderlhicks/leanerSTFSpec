/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete initialized block-state controls

Library `EthConformance`: private complete field and callback observations against
independent finite expectations. These inspect public outputs by execution; they
are not consumer proofs that unfold the initialization body. Synthetic callbacks
supply values only, without original Protocol/backend execution or cost claims.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7/8.
-/

namespace STFSpec.Conformance.State.BlockInitializationGuards

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
    sequence ((b.accountReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map addressValues),
    sequence ((b.storageReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      (fun p ↦ addressValues p.1 ++ slotValues p.2)),
    sequence ((b.codeReads.toList.mergeSort (fun x y ↦
      (compare x.1 y.1).then (compare x.2 y.2) != .gt)).map
        (fun p ↦ addressValues p.1 ++ hashValues p.2)),
    optional (fun n ↦ [n]) b.oldestAncestorOffset]

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

private def suppliedConsts (ns : Nat × Nat × Nat × Nat) : HashConsts :=
  ⟨digest ns.1, digest ns.2.1, digest ns.2.2.1, digest ns.2.2.2⟩

-- Literal frames for each empty output, including both maps and next=0 in each
-- B1 index. No production container or initialization expression builds this oracle.
private def expected (seed : Nat) (ns : Nat × Nat × Nat × Nat) : List Nat :=
  sequence [expectedProvider seed,
    sequence [digits 32 ns.1, digits 32 ns.2.1, digits 32 ns.2.2.1, digits 32 ns.2.2.2],
    [0], [4, 1, 0, 1, 0, 1, 0, 1, 0], [0], [4, 1, 0, 1, 0, 1, 0, 1, 0],
    [0], [0], [0], [0], [0], [0], [0]]

private def samples : List (Nat × (Nat × Nat × Nat × Nat)) :=
  [(0, (0, 0, 0, 0)), (1, (2 ^ 256 - 1, 17, 2 ^ 255, 255)),
    (2 ^ 255 + 9, (2 ^ 255 + 1, 2 ^ 254 + 2, 2 ^ 253 + 3, 2 ^ 252 + 4))] ++
  (List.range 7).map (fun i ↦ (i, (7, 11, 13, 17))) ++
  (List.range 32).flatMap (fun i ↦
    let n := 129 * 256 ^ i
    [(i, (n, 0, 0, 0)), (i, (0, n, 0, 0)),
      (i, (0, 0, n, 0)), (i, (0, 0, 0, n))])

private def controls : List (List Nat × List Nat) := samples.flatMap fun (seed, ns) ↦
  let ps := provider seed
  let consts := suppliedConsts ns
  let b := BlockState.new ps consts
  let sibling := BlockState.new (provider (seed + 1)) (suppliedConsts (1, 2, 3, 4))
  let changed := { b with oldestAncestorOffset := some 0 }
  [(observe b, expected seed ns),
    (observe sibling, expected (seed + 1) (1, 2, 3, 4)),
    (observeProvider ps, expectedProvider seed),
    (sequence [hashValues consts.emptyCodeHash, hashValues consts.emptyTrieRoot,
        hashValues consts.emptyOmmerHash, hashValues consts.transferTopic],
      sequence [digits 32 ns.1, digits 32 ns.2.1, digits 32 ns.2.2.1, digits 32 ns.2.2.2]),
    (observe changed, sequence [expectedProvider seed,
      sequence [digits 32 ns.1, digits 32 ns.2.1, digits 32 ns.2.2.1, digits 32 ns.2.2.2],
      [0], [4, 1, 0, 1, 0, 1, 0, 1, 0], [0], [4, 1, 0, 1, 0, 1, 0, 1, 0],
      [0], [0], [0], [0], [0], [0], [1, 0]]),
    (observe b, expected seed ns), (observeProvider ps, expectedProvider seed),
    (observe sibling, expected (seed + 1) (1, 2, 3, 4))]

private def completeControls : Bool := controls.all (fun p ↦ p.1 == p.2)

#guard samples.length == 138
#guard controls.length == 1104
#guard completeControls
#guard let b := BlockState.new (provider 0) (suppliedConsts (1, 2, 3, 4))
  observe b != observe { b with oldestAncestorOffset := some 0 }
#guard observe (BlockState.new (provider 0) (suppliedConsts (1, 2, 3, 4))) !=
  observe (BlockState.new (provider 1) (suppliedConsts (1, 2, 3, 4)))
#guard observe (BlockState.new (provider 0) (suppliedConsts (1, 2, 3, 4))) !=
  observe (BlockState.new (provider 0) (suppliedConsts (4, 3, 2, 1)))

end STFSpec.Conformance.State.BlockInitializationGuards
