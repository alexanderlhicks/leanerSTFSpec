/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete logical-read-set controls

Library `EthConformance`: complete membership vectors use the transparent predicates
and existing Std decidability. A separate numeric-list model supplies expectations.
All helpers and controls are private; there is no enumeration or instance API.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.State.ReadSetsGuards

open STFSpec.State STFSpec.Base

private def address (n : Nat) : Address := Address.ofNat n
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)
private def addresses (xs : List Nat) : Std.HashSet Address :=
  xs.foldl (fun s n ↦ s.insert (address n)) ∅
private def slots (xs : List (Nat × Nat)) : Std.HashSet (Address × Bytes32) :=
  xs.foldl (fun s p ↦ s.insert (address p.1, slot p.2)) ∅

-- No callback is called by either view. The variants below also supply a provider
-- with every callback changed, so field dependence cannot hide behind an empty result.
private def provider (n : Nat) : PreState Id where
  getAccount? := fun _ ↦ .error (.unresolved (digest n))
  getStorage := fun _ _ ↦ .ok (U256.ofNat n)
  getCode := fun _ ↦ .ok (ByteArray.mk #[UInt8.ofNat n, 0, 255])
  stateRoot := fun _ ↦ .error (.missing (.code (digest (n + 1))))

private def supplied (ar : List Nat) (sr : List (Nat × Nat)) : BlockState Id :=
  ⟨provider 7, ⟨digest 1, digest 2, digest 3, digest 4⟩,
    ∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅,
    addresses ar, slots sr, ∅, none⟩

-- Complete digit recipes are independent of Base's concrete key export.
private def digits (width n : Nat) : List Nat :=
  (List.range width).map (fun i ↦ n / 256 ^ (width - 1 - i) % 256)
private def accountExpected (xs : List Nat) (n : Nat) : Bool :=
  xs.any (fun x ↦ x % 2 ^ 160 == n % 2 ^ 160)
private def storageExpected (xs : List (Nat × Nat)) (p : Nat × Nat) : Bool :=
  xs.any (fun x ↦ x.1 % 2 ^ 160 == p.1 % 2 ^ 160 && x.2 % 2 ^ 256 == p.2 % 2 ^ 256)

private def observe (b : BlockState Id) (aq : List Nat) (sq : List (Nat × Nat)) :
    List (List Nat) :=
  aq.zipIdx |>.map (fun (n, i) ↦ [0, i] ++
    ((address n).toBytes.toList.map UInt8.toNat) ++
    [if @decide (b.accountReadSet (address n))
      (decidable_of_iff (address n ∈ b.accountReads)
        (BlockState.accountReadSet_iff b (address n)).symm) then 1 else 0]) |>.append
  (sq.zipIdx.map (fun (p, i) ↦ [1, i] ++
    ((address p.1).toBytes.toList.map UInt8.toNat) ++
    ((slot p.2).toBytes.toList.map UInt8.toNat) ++
    [if @decide (b.storageReadSet (address p.1, slot p.2))
      (decidable_of_iff ((address p.1, slot p.2) ∈ b.storageReads)
        (BlockState.storageReadSet_iff b (address p.1, slot p.2)).symm) then 1 else 0]))

private def expected (ar : List Nat) (sr : List (Nat × Nat))
    (aq : List Nat) (sq : List (Nat × Nat)) : List (List Nat) :=
  aq.zipIdx |>.map (fun (n, i) ↦ [0, i] ++ digits 20 n ++
    [if accountExpected ar n then 1 else 0]) |>.append
  (sq.zipIdx.map (fun (p, i) ↦ [1, i] ++ digits 20 p.1 ++ digits 32 p.2 ++
    [if storageExpected sr p then 1 else 0]))

private def probes : List Nat := [0, 1, 3, 5, 7, 16, 2 ^ 159, 2 ^ 160 - 1]
private def pairProbes : List (Nat × Nat) :=
  [(0, 0), (3, 5), (3, 7), (7, 5), (7, 7), (0, 2 ^ 255), (2 ^ 159, 0),
    (2 ^ 160 - 1, 2 ^ 256 - 1)]

private def sample (label : String) (b : BlockState Id) (ar : List Nat)
    (sr : List (Nat × Nat)) (aq : List Nat := probes)
    (sq : List (Nat × Nat) := pairProbes) : String × List (List Nat) × List (List Nat) :=
  (label, observe b aq sq, expected ar sr aq sq)

private def ar : List Nat := [0, 3, 16, 2 ^ 159]
private def sr : List (Nat × Nat) := [(3, 5), (3, 7), (7, 5), (0, 2 ^ 255)]
private def parent : BlockState Id := supplied ar sr

-- Each irrelevant field changes separately. Malformed order indexes, tombstones,
-- zero writes, empty inner maps and incoherent constants impose no view premise.
private def rawSlots : WriteOrder Bytes32 :=
  ⟨17, ∅, ((∅ : Std.ExtTreeMap Nat Bytes32).insert 3 (slot 5)).insert 9 (slot 5)⟩

private def variants : List (String × BlockState Id) :=
  [("provider", { parent with preState := provider (2 ^ 255 + 99) }),
    ("constants", { parent with consts := ⟨digest 9, digest 8, digest 7, digest 6⟩ }),
    ("accountWrites", { parent with accountWrites :=
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (address 0) none }),
    ("accountOrder", { parent with accountOrder :=
      ⟨2 ^ 1024, ∅, (∅ : Std.ExtTreeMap Nat Address).insert 7 (address 99)⟩ }),
    ("storageWrites", { parent with storageWrites :=
      ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert (address 3)
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot 5) U256.zero)).insert (address 7) ∅ }),
    ("storageAddressOrder", { parent with storageAddressOrder :=
      ⟨0, ∅, (∅ : Std.ExtTreeMap Nat Address).insert (2 ^ 300) (address 3)⟩ }),
    ("storageSlotOrder", { parent with storageSlotOrder :=
      (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert (address 7) rawSlots }),
    ("codeWrites", { parent with codeWrites :=
      (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (digest 99) (ByteArray.mk #[0, 255, 0]) }),
    ("storageClears", { parent with storageClears :=
      (∅ : Std.ExtTreeSet Address).insert (address 3) }),
    ("codeReads", { parent with codeReads :=
      (∅ : Std.HashSet (Address × Hash32)).insert (address 3, digest 5) }),
    ("offset-zero", { parent with oldestAncestorOffset := some 0 }),
    ("offset-huge", { parent with oldestAncestorOffset := some (2 ^ 1024 + 17) })]

private def controls : List (String × List (List Nat) × List (List Nat)) :=
  [sample "empty" (supplied [] []) [] [],
    sample "parent" parent ar sr,
    sample "duplicates-reconstructed" (supplied
      [0, 3, 16, 2 ^ 159, 3 + 2 ^ 160, 0]
      [(3, 5), (3, 7), (7, 5), (0, 2 ^ 255), (3 + 2 ^ 160, 5 + 2 ^ 256), (3, 5)]) ar sr,
    sample "insertion-permutation" (supplied ar.reverse sr.reverse) ar sr,
    sample "account-sibling" { parent with accountReads := addresses [1, 7] } [1, 7] sr,
    sample "storage-sibling" { parent with storageReads := slots [(7, 7)] } ar [(7, 7)],
    sample "retained-parent" parent ar sr] ++
  variants.map (fun (label, b) ↦ sample label b ar sr) ++
  (List.range 20).flatMap (fun i ↦ [1, 128, 129].map fun byte ↦
    let n := byte * 256 ^ i
    sample s!"address-byte-{i}-{byte}" (supplied [n] [(n, 5)]) [n] [(n, 5)]
      [0, n, n + 1, n + 2 ^ 160] [(n, 5), (n + 1, 5), (n, 7), (n + 2 ^ 160, 5)]) ++
  (List.range 32).flatMap (fun i ↦ [1, 128, 129].map fun byte ↦
    let n := byte * 256 ^ i
    sample s!"slot-byte-{i}-{byte}" (supplied [3] [(3, n), (7, n)]) [3] [(3, n), (7, n)]
      [0, 3, 7] [(3, n), (7, n), (3, n + 1), (0, n), (3, n + 2 ^ 256)]) ++
  [sample "retained-parent-after-siblings" parent ar sr]

#guard controls.length == 176
#guard controls.all (fun (_, actual, oracle) ↦ actual == oracle)
-- Distinct complete keys can share low hash bits under the actual canonical dictionary.
-- This is a bounded collision control, not a hash-distribution or bucket-layout theorem.
#guard hash (address 0) % 16 == hash (address 16) % 16
#guard hash (address 0) != hash (address 16)
#guard (observe parent probes pairProbes) != expected [3] sr probes pairProbes
#guard (observe parent probes pairProbes) != expected ar [(3, 5)] probes pairProbes

end STFSpec.Conformance.State.ReadSetsGuards
