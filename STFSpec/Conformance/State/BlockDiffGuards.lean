/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockDiff

/-!
# Complete raw BlockDiff observations

Library `EthConformance`: finite association-list expectations retain every raw
presence tag, payload and metadata occurrence. No tracker or apply law is tested.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.BlockDiffGuards

open STFSpec.Base STFSpec.State

/-- Complete fixed-width address bytes. -/
def addressBytes (a : Address) : List Nat := a.toBytes.toList.map UInt8.toNat
/-- Complete fixed-width slot bytes. -/
def slotBytes (k : Bytes32) : List Nat := k.toBytes.toList.map UInt8.toNat
/-- Complete fixed-width hash bytes. -/
def hashBytes (h : Hash32) : List Nat := h.toBytes.toList.map UInt8.toNat
/-- Complete account payload, without collapsing absence or deletion. -/
def accountValue (a : Account) : Nat × Nat × List Nat :=
  (a.nonce, a.balance.toNat, hashBytes a.codeHash)
/-- Complete arbitrary code payload. -/
def codeBytes (b : ByteArray) : List Nat := b.data.toList.map UInt8.toNat

/-- Seven complete observable fields; list occurrence order remains exact. -/
abbrev Observation :=
  List (List Nat × Option (Nat × Nat × List Nat)) × List (List Nat) ×
  List (List Nat × List (List Nat × Nat)) × List (List Nat) ×
  List (List Nat × List (List Nat)) × List (List Nat × List Nat) × List (List Nat)

/-- Observe every complete raw field through public projections and Std enumerations. -/
def observe (d : BlockDiff) : Observation :=
  (d.accountChanges.toList.map (fun x => (addressBytes x.1, x.2.map accountValue)),
   d.accountOrder.map addressBytes,
   d.storageChanges.toList.map (fun x =>
     (addressBytes x.1, x.2.toList.map (fun y => (slotBytes y.1, y.2.toNat)))),
   d.storageAddressOrder.map addressBytes,
   d.storageSlotOrder.toList.map (fun x => (addressBytes x.1, x.2.map slotBytes)),
   d.codeChanges.toList.map (fun x => (hashBytes x.1, codeBytes x.2)),
   d.storageClears.toList.map addressBytes)

/-- A finite raw list model; association lists use last assignment, metadata is untouched. -/
structure Model where
  accounts : List (Address × Option Account)
  accountOrder : List Address
  storage : List (Address × List (Bytes32 × U256))
  storageOrder : List Address
  slotOrder : List (Address × List Bytes32)
  code : List (Hash32 × ByteArray)
  clears : List Address

/-- Independent last-assignment association-list update, comparing the whole key value. -/
def assign {α β : Type} (key : α → Nat) (xs : List (α × β)) (entry : α × β) : List (α × β) :=
  xs.filter (fun x => key x.1 != key entry.1) ++ [entry]
/-- Canonical finite map expectations use full-key numerical order and last assignment. -/
def canonical {α β : Type} (key : α → Nat) (xs : List (α × β)) : List (α × β) :=
  (xs.foldl (assign key) []).mergeSort (fun x y => key x.1 ≤ key y.1)
/-- Build the raw seven-field value with ordinary public Std insertions. -/
def build (m : Model) : BlockDiff :=
  ⟨m.accounts.foldl (fun t x => t.insert x.1 x.2) ∅, m.accountOrder,
   m.storage.foldl (fun t x =>
     t.insert x.1 (x.2.foldl (fun u y => u.insert y.1 y.2) ∅)) ∅,
   m.storageOrder, m.slotOrder.foldl (fun t x => t.insert x.1 x.2) ∅,
   m.code.foldl (fun t x => t.insert x.1 x.2) ∅,
   m.clears.foldl (fun t a => t.insert a) ∅⟩
/-- Association-list oracle for all seven fields, independent of tree enumeration. -/
def expected (m : Model) : Observation :=
  ((canonical Address.toNat m.accounts).map (fun x =>
      (addressBytes x.1, x.2.map accountValue)),
   m.accountOrder.map addressBytes,
   (canonical Address.toNat m.storage).map (fun x =>
     (addressBytes x.1, (canonical FixedBytes.toNat x.2).map
       (fun y => (slotBytes y.1, y.2.toNat)))),
   m.storageOrder.map addressBytes,
   (canonical Address.toNat m.slotOrder).map (fun x =>
     (addressBytes x.1, x.2.map slotBytes)),
   (canonical Hash32.toNat m.code).map (fun x => (hashBytes x.1, codeBytes x.2)),
   (canonical Address.toNat (m.clears.map (fun a => (a, ())))).map
     (fun x => addressBytes x.1))

/-- Indexed bytes with leading zeros, early/late differences and high bytes. -/
def bytesFor (n seed : Nat) : ByteArray :=
  ((List.range n).map (fun i => UInt8.ofNat ((i * 37 + seed) % 256))).toByteArray
/-- Arbitrary raw hashes from full-width values, without hash authenticity. -/
def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
/-- Complete indexed big-endian key patterns, including significant leading zeros. -/
def keyNumber (width seed : Nat) : Nat :=
  (List.range width).foldl (fun n i => n * 256 + (i * 37 + seed) % 256) 0
/-- Complete unequal 20-byte address keys. -/
def addresses : List Address :=
  [0, 1, 2, 255, 256, 2^152, 2^159, 2^160-1, 2^80+17, keyNumber 20 0, keyNumber 20 211,
   keyNumber 20 0 + 1, keyNumber 20 0 + 2^152].map Address.ofNat
/-- Complete unequal 32-byte slot keys. -/
def slots : List Bytes32 :=
  [0, 1, 2, 255, 256, 2^248, 2^255, 2^256-1, 2^128+17, keyNumber 32 0, keyNumber 32 211,
   keyNumber 32 0 + 1, keyNumber 32 0 + 2^248].map FixedBytes.ofNat
/-- Reconstructed equal address keys exercise value equality. -/
def rebuiltAddresses : List Address := addresses.map (fun a => Address.ofNat a.toNat)
/-- Reconstructed equal slot keys exercise value equality. -/
def rebuiltSlots : List Bytes32 := slots.map (fun k => FixedBytes.ofNat k.toNat)
/-- A raw corpus containing absence, deletion, empty/replacement accounts and large values. -/
def baseModel : Model :=
  { accounts := [(Address.ofNat 1, none),
      (Address.ofNat 2, some (emptyAccount HashConsts.literals)),
      (Address.ofNat (2^159), some ⟨2^1024+17, U256.max, hash (2^255+19)⟩)]
    accountOrder := [Address.ofNat 99, Address.ofNat 1, Address.ofNat 1, Address.ofNat 2]
    storage := [(Address.ofNat 99, []),
      (Address.ofNat 1, [(FixedBytes.ofNat 0, U256.zero),
        (FixedBytes.ofNat (2^255), U256.max), (FixedBytes.ofNat 0, U256.zero)])]
    storageOrder := [Address.ofNat 99, Address.ofNat 99, Address.ofNat 1, Address.ofNat 42]
    slotOrder := [(Address.ofNat 99, []),
      (Address.ofNat 42, [FixedBytes.ofNat 3, FixedBytes.ofNat 3, FixedBytes.ofNat 7])]
    code := [(HashConsts.literals.emptyCodeHash, bytesFor 513 211),
      (hash 0, ByteArray.empty), (hash (2^255), bytesFor 1025 7)]
    clears := [Address.ofNat 99, Address.ofNat 1, Address.ofNat 99] }
/-- Finite indexed full-key corpus, including rebuilt equal keys and duplicate assignments. -/
def indexedModel (seed : Nat) : Model :=
  { accounts := (addresses ++ rebuiltAddresses).zipIdx.map (fun x =>
      (x.1, if x.2 % 3 == 0 then none else
        some ⟨2^(256+seed)+x.2, U256.ofNat (2^255+x.2), hash (2^248+x.2)⟩))
    accountOrder := rebuiltAddresses.reverse ++ addresses ++ [Address.ofNat 42]
    storage := (addresses ++ rebuiltAddresses).zipIdx.map (fun x =>
      (x.1, if x.2 % 4 == 0 then [] else
        (slots ++ rebuiltSlots).zipIdx.map (fun y =>
          (y.1, if y.2 % 3 == 0 then U256.zero else U256.ofNat (2^255+seed+y.2)))))
    storageOrder := addresses.reverse ++ addresses
    slotOrder := (addresses ++ rebuiltAddresses).zipIdx.map (fun x =>
      (x.1, if x.2 % 3 == 0 then [] else rebuiltSlots.reverse ++ slots))
    code := (slots ++ rebuiltSlots).zipIdx.map (fun x =>
      (Hash32.ofBytes32 x.1, bytesFor (65+x.2*17) (seed+x.2)))
    clears := addresses.reverse ++ rebuiltAddresses }
/-- Seven independent field variations; metadata-only differences are preserved. -/
def variations : List Model :=
  [baseModel,
   {baseModel with accounts := baseModel.accounts ++ [(Address.ofNat 42, none)]},
   {baseModel with accountOrder := baseModel.accountOrder.reverse},
   {baseModel with storage := baseModel.storage ++ [(Address.ofNat 42, [])]},
   {baseModel with storageOrder := baseModel.storageOrder.reverse},
   {baseModel with slotOrder := baseModel.slotOrder ++ [(Address.ofNat 7, [])]},
   {baseModel with code := baseModel.code ++ [(hash 7, bytesFor 777 255)]},
   {baseModel with clears := baseModel.clears ++ [Address.ofNat 42]}]
/-- Models with different insertion orders but identical complete maps and sets. -/
def permuted (m : Model) : Model :=
  {m with accounts := (canonical Address.toNat m.accounts).reverse
          storage := (canonical Address.toNat m.storage).reverse.map (fun x =>
            (x.1, (canonical FixedBytes.toNat x.2).reverse))
          slotOrder := (canonical Address.toNat m.slotOrder).reverse
          code := (canonical Hash32.toNat m.code).reverse
          clears := m.clears.reverse}
/-- Same-key absence, deletion, empty/replacement account and storage presence controls. -/
def presenceControls : Bool :=
  let empty := {baseModel with accounts := []}
  let deleted := {baseModel with accounts := [(Address.ofNat 1, none)]}
  let present := {baseModel with accounts :=
    [(Address.ofNat 1, some (emptyAccount HashConsts.literals))]}
  let replacement := {baseModel with accounts :=
    [(Address.ofNat 1, some ⟨2^1024+17, U256.max, hash 17⟩)]}
  let missingStorage := {baseModel with storage := []}
  let emptyStorage := {baseModel with storage := [(Address.ofNat 1, [])]}
  let zeroStorage := {baseModel with storage :=
    [(Address.ofNat 1, [(FixedBytes.ofNat 0, U256.zero)])]}
  observe (build empty) != observe (build deleted) &&
  observe (build deleted) != observe (build present) &&
  observe (build present) != observe (build replacement) &&
  observe (build missingStorage) != observe (build emptyStorage) &&
  observe (build emptyStorage) != observe (build zeroStorage)

/-- Full-value corpus agreement and sensitivity to each of the seven fields. -/
def guards : Bool :=
  presenceControls && (variations ++ (List.range 4).map indexedModel).all (fun m =>
    observe (build m) == expected m && observe (build (permuted m)) == expected m) &&
  variations.tail.all (fun m => observe (build m) != observe (build baseModel)) &&
  (observe (build {baseModel with slotOrder := []}) !=
    observe (build {baseModel with slotOrder := [(Address.ofNat 99, [])]}))

#guard guards

end STFSpec.Conformance.State.BlockDiffGuards
