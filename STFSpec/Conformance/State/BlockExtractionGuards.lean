/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete raw extraction controls

Library `EthConformance`: private numerical/list recipes independently frame every
output byte, optional tag, word and metadata occurrence. The source has coupled
ordered dicts; malformed separate indexes exercise Q85's Lean raw completion.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.BlockExtractionGuards

open STFSpec.State STFSpec.Base

private structure OrderRecipe where
  next : Nat
  forward : List (Nat × Nat)
  reverse : List (Nat × Nat)

private structure Recipe where
  accounts : List (Nat × Option (Nat × Nat × Nat))
  storage : List (Nat × List (Nat × Nat))
  code : List (Nat × List Nat)
  clears : List Nat
  accountOrder : OrderRecipe
  addressOrder : OrderRecipe
  slotOrders : List (Nat × OrderRecipe)

private def digits (width n : Nat) : List Nat :=
  (List.range width).map (fun i ↦ n / 256 ^ (width - 1 - i) % 256)
private def frame (xs : List (List Nat)) : List Nat :=
  xs.length :: xs.flatMap (fun x ↦ x.length :: x)
private def optional {α : Type} (f : α → List Nat) : Option α → List Nat
  | none => [0]
  | some x => 1 :: f x
private def address (n : Nat) : Address := Address.ofNat n
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)
private def bytes (ns : List Nat) : ByteArray := ⟨(ns.map UInt8.ofNat).toArray⟩
private def byteValues (b : ByteArray) : List Nat := b.toList.map UInt8.toNat
private def addressValues (a : Address) : List Nat := byteValues a.toBytes.toByteArray
private def slotValues (k : Bytes32) : List Nat := byteValues k.toBytes.toByteArray
private def hashValues (h : Hash32) : List Nat := byteValues h.toBytes.toByteArray
private def accountValues (a : Account) : List Nat :=
  [a.nonce, a.balance.toNat] ++ hashValues a.codeHash

private def buildOrder {K : Type} [Ord K] [Std.TransOrd K]
    (key : Nat → K) (r : OrderRecipe) : WriteOrder K :=
  ⟨r.next, r.forward.foldl (fun t p ↦ t.insert (key p.1) p.2) ∅,
    r.reverse.foldl (fun t p ↦ t.insert p.1 (key p.2)) ∅⟩

private def provider (n : Nat) : PreState Id where
  getAccount? := fun _ ↦ .error (.missing (.node (digest n)))
  getStorage := fun _ _ ↦ .error (.malformed (.code (digest (n + 1))))
  getCode := fun _ ↦ .ok (bytes [0, n, 255])
  stateRoot := fun _ ↦ .ok (digest (n + 2))
private def constants (n : Nat) : HashConsts :=
  ⟨digest n, digest (n + 1), digest (n + 2), digest (n + 3)⟩
private def account (a : Nat × Nat × Nat) : Account :=
  ⟨a.1, U256.ofNat a.2.1, digest a.2.2⟩

private def build (r : Recipe) : BlockState Id where
  preState := provider 0
  consts := constants 0
  accountWrites := r.accounts.foldl (fun t p ↦ t.insert (address p.1) (p.2.map account)) ∅
  accountOrder := buildOrder address r.accountOrder
  storageWrites := r.storage.foldl (fun t p ↦ t.insert (address p.1)
    (p.2.foldl (fun t q ↦ t.insert (slot q.1) (U256.ofNat q.2)) ∅)) ∅
  storageAddressOrder := buildOrder address r.addressOrder
  storageSlotOrder := r.slotOrders.foldl (fun t p ↦ t.insert (address p.1)
    (buildOrder slot p.2)) ∅
  codeWrites := r.code.foldl (fun t p ↦ t.insert (digest p.1) (bytes p.2)) ∅
  storageClears := r.clears.foldl (fun t a ↦ t.insert (address a)) ∅
  accountReads := ∅
  storageReads := ∅
  codeReads := ∅
  oldestAncestorOffset := none

private def observe (d : BlockDiff) : List Nat :=
  frame [frame (d.accountChanges.toList.map (fun p ↦ addressValues p.1 ++
      optional accountValues p.2)),
    frame (d.accountOrder.map addressValues),
    frame (d.storageChanges.toList.map (fun p ↦ addressValues p.1 ++
      frame (p.2.toList.map (fun q ↦ slotValues q.1 ++ [q.2.toNat])))),
    frame (d.storageAddressOrder.map addressValues),
    frame (d.storageSlotOrder.toList.map (fun p ↦ addressValues p.1 ++
      frame (p.2.map slotValues))),
    frame (d.codeChanges.toList.map (fun p ↦ hashValues p.1 ++ byteValues p.2)),
    frame (d.storageClears.toList.map addressValues)]

private def sorted {V : Type} (xs : List (Nat × V)) : List (Nat × V) :=
  xs.mergeSort (fun a b ↦ a.1 ≤ b.1)
private def orderKeys (r : OrderRecipe) : List Nat := (sorted r.reverse).map Prod.snd

-- This oracle never calls extractBlockDiff, WriteOrder.toList, or a production container.
-- Recipes have unique map keys; repeated reverse values intentionally remain repeated.
private def expected (r : Recipe) : List Nat :=
  frame [frame ((sorted r.accounts).map (fun p ↦ digits 20 p.1 ++ optional
      (fun a ↦ [a.1, a.2.1 % 2 ^ 256] ++ digits 32 a.2.2) p.2)),
    frame ((orderKeys r.accountOrder).map (digits 20)),
    frame ((sorted r.storage).map (fun p ↦ digits 20 p.1 ++ frame
      ((sorted p.2).map (fun q ↦ digits 32 q.1 ++ [q.2 % 2 ^ 256])))),
    frame ((orderKeys r.addressOrder).map (digits 20)),
    frame ((sorted r.slotOrders).map (fun p ↦ digits 20 p.1 ++ frame
      ((orderKeys p.2).map (digits 32)))),
    frame ((sorted r.code).map (fun p ↦ digits 32 p.1 ++ p.2.map (· % 256))),
    frame ((r.clears.mergeSort (· ≤ ·)).map (digits 20))]

private def emptyOrder : OrderRecipe := ⟨0, [], []⟩
private def good (a b : Nat) : OrderRecipe :=
  ⟨2 ^ 100 + 17, [(a, 4), (b, 100)], [(100, b), (4, a)]⟩

-- Nine global/slot order entries (seven distinct cases; entries 7 and 8 repeat the
-- well-formed first case): huge gaps, bounds, duplicate reverse values, forward-only,
-- reverse-only and mismatched maps. Tombstones and zero writes come from the separate
-- write recipes below.
private def orderCases (a b x : Nat) : List OrderRecipe :=
  [good a b, { good a b with next := 0 },
    ⟨0, [(a, 4)], [(100, a), (4, a)]⟩,
    ⟨1, [(a, 0)], []⟩, ⟨1, [], [(0, x)]⟩,
    ⟨1, [(a, 0)], [(0, b)]⟩,
    good a b, good a b, ⟨1, [(a, 0)], [(0, a)]⟩]

private def base (a k h : Nat) : Recipe :=
  ⟨[(a + 9, none), (a + 2, some (2 ^ 1024 + 17, 2 ^ 256 - 1, h)),
      (a + 7, some (0, 0, h + 1))],
    [(a + 9, [(k + 9, 0), (k + 2, 2 ^ 256 - 1)]), (a + 7, [])],
    [(h, [0, 255, 239, 0, 1]), (h + 1, []), (h + 2, List.range 256)],
    [a + 9, a + 7], good (a + 9) (a + 2), good (a + 9) (a + 7),
    [(a + 9, good (k + 9) (k + 2)), (a + 11, emptyOrder)]⟩

-- Each index is varied on its own so one implementation cannot substitute another.
private def orderRecipes : List Recipe :=
  let r := base 0 0 0
  (orderCases 9 2 11).map (fun o ↦ { r with accountOrder := o }) ++
  (orderCases 9 7 11).map (fun o ↦ { r with addressOrder := o }) ++
  (orderCases 9 2 11).map (fun o ↦ { r with slotOrders := [(9, o)] }) ++
  [( { r with accounts := [(9, none)] }),
    { r with storage := [(9, [(9, 0)])] }, { r with storage := [(9, [])] }]

-- Six optional-map cases from the approved raw proposal, with whole optional tags.
private def optionalRecipes : List Recipe :=
  let r := base 0 0 0
  [{ r with slotOrders := [], storage := [] },
    { r with slotOrders := [], storage := [(9, [(9, 0)])] },
    { r with slotOrders := [(9, emptyOrder)], storage := [] },
    { r with slotOrders := [(9, emptyOrder)], storage := [(9, [])] },
    { r with slotOrders := [(9, ⟨0, [], [(100, 11)]⟩)], storage := [] },
    { r with
      slotOrders := [(9, ⟨0, [(9, 4)], [(100, 9), (7, 11), (4, 9)]⟩)]
      storage := [(9, [(9, 0)])] }]

private def byteRecipes : List Recipe :=
  (List.range 20).map (fun i ↦ base (129 * 256 ^ i) 0 0) ++
  (List.range 32).map (fun i ↦ base 0 (129 * 256 ^ i) 0) ++
  (List.range 32).map (fun i ↦ base 0 0 (129 * 256 ^ i))
private def recipes : List Recipe := orderRecipes ++ optionalRecipes ++ byteRecipes

private def optionalObservation (d : BlockDiff) : List Nat :=
  frame ([2, 7, 9, 11, 99].map (fun n ↦ optional
    (fun ks ↦ frame (ks.map slotValues)) (d.storageSlotOrder[address n]?)))
private def expectedOptional (r : Recipe) : List Nat :=
  frame ([2, 7, 9, 11, 99].map (fun n ↦ optional
    (fun o ↦ frame ((orderKeys o).map (digits 32)))
    ((r.slotOrders.find? (fun p ↦ p.1 == n)).map Prod.snd)))

private def discardedVariants (b : BlockState Id) : List (BlockState Id) :=
  [{ b with preState := provider (2 ^ 255 + 1) },
    { b with consts := constants (2 ^ 255 + 1) },
    { b with accountReads := (∅ : Std.HashSet Address).insert (address 11) },
    { b with
      storageReads :=
        (∅ : Std.HashSet (Address × Bytes32)).insert (address 11, slot (2 ^ 255 + 7)) },
    { b with
      codeReads :=
        (∅ : Std.HashSet (Address × Hash32)).insert (address 11, digest (2 ^ 255 + 8)) },
    { b with oldestAncestorOffset := some 0 },
    { b with oldestAncestorOffset := some (2 ^ 1024 + 17) }]

private def permuted (r : Recipe) : Recipe :=
  { r with
    accounts := r.accounts.reverse
    storage := r.storage.reverse.map (fun p ↦ (p.1, p.2.reverse))
    code := r.code.reverse
    clears := r.clears.reverse
    accountOrder := { r.accountOrder with
      forward := r.accountOrder.forward.reverse
      reverse := r.accountOrder.reverse.reverse }
    addressOrder := { r.addressOrder with
      forward := r.addressOrder.forward.reverse
      reverse := r.addressOrder.reverse.reverse }
    slotOrders := r.slotOrders.reverse.map (fun p ↦ (p.1, { p.2 with
      forward := p.2.forward.reverse
      reverse := p.2.reverse.reverse })) }

private def controls : List (List Nat × List Nat) := recipes.flatMap fun r ↦
  let b := build r
  let parent := extractBlockDiff b
  let siblingRecipe := { r with accountOrder := emptyOrder }
  let sibling := extractBlockDiff (build siblingRecipe)
  let children := (discardedVariants b).map extractBlockDiff
  [(observe parent, expected r), (optionalObservation parent, expectedOptional r),
    (observe (extractBlockDiff (build (permuted r))), expected r),
    (observe sibling, expected siblingRecipe)] ++
  children.map (fun d ↦ (observe d, expected r)) ++
  [(observe parent, expected r), (observe sibling, expected siblingRecipe)]

private def sensitive : Bool :=
  let r := base 0 0 0
  let want := expected r
  [ { r with accounts := [] }, { r with storage := [] }, { r with code := [] },
    { r with clears := [] }, { r with accountOrder := emptyOrder },
    { r with addressOrder := emptyOrder }, { r with slotOrders := [] } ].all
      (fun q ↦ observe (extractBlockDiff (build q)) != want)

private def completeControls : Bool := controls.all (fun p ↦ p.1 == p.2)
#guard recipes.length == 120
#guard controls.length == 1560
#guard completeControls
#guard sensitive
#guard let r := base 0 0 0
  optionalObservation (extractBlockDiff (build { r with slotOrders := [] })) !=
    optionalObservation (extractBlockDiff (build { r with slotOrders := [(9, emptyOrder)] }))

end STFSpec.Conformance.State.BlockExtractionGuards
