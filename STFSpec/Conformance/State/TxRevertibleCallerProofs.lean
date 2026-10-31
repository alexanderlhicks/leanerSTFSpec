/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete raw revertible-data facade clients

Library `EthConformance`. Every authored declaration is private. Arbitrary clients
check exact construction, whole projections, reconstruction and eight independent
updates; finite kernel controls observe every raw field through public Base/Std APIs.
No tracker, snapshot, observation or backend operation is exercised.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.State.TxRevertibleCallerProofs

open STFSpec.Base STFSpec.State

private def exactConstructor :
    Std.ExtTreeMap Address (Option Account) → WriteOrder Address →
    Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) → WriteOrder Address →
    Std.ExtTreeMap Address (WriteOrder Bytes32) → Std.ExtTreeMap Hash32 ByteArray →
    Std.ExtTreeSet Address → Std.ExtTreeMap (Address × Bytes32) U256 → TxRevertible :=
  @TxRevertible.mk

private theorem complete_construction
    (accountWrites : Std.ExtTreeMap Address (Option Account))
    (accountOrder : WriteOrder Address)
    (storageWrites : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (storageAddressOrder : WriteOrder Address)
    (storageSlotOrder : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (codeWrites : Std.ExtTreeMap Hash32 ByteArray)
    (storageClears : Std.ExtTreeSet Address)
    (transient : Std.ExtTreeMap (Address × Bytes32) U256)
    :
    let r := exactConstructor accountWrites accountOrder storageWrites
      storageAddressOrder storageSlotOrder codeWrites storageClears transient
    (r.accountWrites, r.accountOrder, r.storageWrites,
      r.storageAddressOrder, r.storageSlotOrder, r.codeWrites, r.storageClears, r.transient) =
      (accountWrites, accountOrder, storageWrites,
        storageAddressOrder, storageSlotOrder, codeWrites, storageClears, transient) := by
  rfl

private theorem reconstruction (r : TxRevertible) :
    TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
      r.storageAddressOrder r.storageSlotOrder r.codeWrites r.storageClears r.transient = r := by
  rfl

private theorem replace_accountWrites (r : TxRevertible)
    (replacement : Std.ExtTreeMap Address (Option Account)) :
    ({ r with accountWrites := replacement } : TxRevertible) =
      TxRevertible.mk replacement r.accountOrder r.storageWrites
        r.storageAddressOrder r.storageSlotOrder r.codeWrites r.storageClears r.transient := by
  rfl

private theorem replace_accountOrder (r : TxRevertible)
    (replacement : WriteOrder Address) :
    ({ r with accountOrder := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites replacement r.storageWrites
        r.storageAddressOrder r.storageSlotOrder r.codeWrites r.storageClears r.transient := by
  rfl

private theorem replace_storageWrites (r : TxRevertible)
    (replacement : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ r with storageWrites := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder replacement
        r.storageAddressOrder r.storageSlotOrder r.codeWrites r.storageClears r.transient := by
  rfl

private theorem replace_storageAddressOrder (r : TxRevertible)
    (replacement : WriteOrder Address) :
    ({ r with storageAddressOrder := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
        replacement r.storageSlotOrder r.codeWrites r.storageClears r.transient := by
  rfl

private theorem replace_storageSlotOrder (r : TxRevertible)
    (replacement : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ r with storageSlotOrder := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
        r.storageAddressOrder replacement r.codeWrites r.storageClears r.transient := by
  rfl

private theorem replace_codeWrites (r : TxRevertible)
    (replacement : Std.ExtTreeMap Hash32 ByteArray) :
    ({ r with codeWrites := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
        r.storageAddressOrder r.storageSlotOrder replacement r.storageClears r.transient := by
  rfl

private theorem replace_storageClears (r : TxRevertible)
    (replacement : Std.ExtTreeSet Address) :
    ({ r with storageClears := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
        r.storageAddressOrder r.storageSlotOrder r.codeWrites replacement r.transient := by
  rfl

private theorem replace_transient (r : TxRevertible)
    (replacement : Std.ExtTreeMap (Address × Bytes32) U256) :
    ({ r with transient := replacement } : TxRevertible) =
      TxRevertible.mk r.accountWrites r.accountOrder r.storageWrites
        r.storageAddressOrder r.storageSlotOrder r.codeWrites r.storageClears replacement := by
  rfl

-- Complete byte models are injective owner observations, not container internals.
private def addressBytes (a : Address) : List UInt8 := a.toBytes.toList
private def slotBytes (k : Bytes32) : List UInt8 := k.toBytes.toList
private def hashBytes (h : Hash32) : List UInt8 := h.toBytes.toList
private def accountValue (a : Account) : Nat × Nat × List UInt8 :=
  (a.nonce, a.balance.toNat, hashBytes a.codeHash)
private def orderValue {K : Type} [Ord K] [Std.TransOrd K]
    (bytes : K → List UInt8) (r : WriteOrder K) :
    Nat × List (List UInt8 × Nat) × List (Nat × List UInt8) :=
  (r.next, r.positions.toList.map (fun (k, p) ↦ (bytes k, p)),
    r.keysByPosition.toList.map (fun (p, k) ↦ (p, bytes k)))

private abbrev Observation :=
  List (List UInt8 × Option (Nat × Nat × List UInt8)) ×
  (Nat × List (List UInt8 × Nat) × List (Nat × List UInt8)) ×
  List (List UInt8 × List (List UInt8 × Nat)) ×
  (Nat × List (List UInt8 × Nat) × List (Nat × List UInt8)) ×
  List (List UInt8 × (Nat × List (List UInt8 × Nat) × List (Nat × List UInt8))) ×
  List (List UInt8 × List UInt8) × List (List UInt8) ×
  List ((List UInt8 × List UInt8) × Nat)

private def observe (r : TxRevertible) : Observation :=
  (r.accountWrites.toList.map (fun (a, v) ↦ (addressBytes a, v.map accountValue)),
    orderValue addressBytes r.accountOrder,
    r.storageWrites.toList.map (fun (a, slots) ↦
      (addressBytes a, slots.toList.map (fun (k, v) ↦ (slotBytes k, v.toNat)))),
    orderValue addressBytes r.storageAddressOrder,
    r.storageSlotOrder.toList.map (fun (a, order) ↦
      (addressBytes a, orderValue slotBytes order)),
    r.codeWrites.toList.map (fun (h, code) ↦ (hashBytes h, (Bytes.ofByteArray code).toList)),
    r.storageClears.toList.map addressBytes,
    r.transient.toList.map (fun ((a, k), v) ↦ ((addressBytes a, slotBytes k), v.toNat)))

private def a : Address := Address.ofNat (2^152 + 256)
private def b : Address := Address.ofNat (2^159 + 255)
private def c : Address := Address.ofNat (2^160 - 1)
private def low : Bytes32 := FixedBytes.ofNat 0
private def high : Bytes32 := FixedBytes.ofNat (2^255 + 255)
private def h : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (2^248 + 256))
private def ab : List UInt8 := [1] ++ List.replicate 17 0 ++ [1, 0]
private def bb : List UInt8 := [128] ++ List.replicate 18 0 ++ [255]
private def cb : List UInt8 := List.replicate 20 255
private def lb : List UInt8 := List.replicate 32 0
private def hb : List UInt8 := [128] ++ List.replicate 30 0 ++ [255]
private def hashb : List UInt8 := [1] ++ List.replicate 29 0 ++ [1, 0]

-- Forward/reverse maps disagree, and counters are sparse, huge or too small.
private def accountIndex : WriteOrder Address :=
  ⟨2^300 + 17, ((∅ : Std.ExtTreeMap Address Nat).insert b 4).insert a 100,
    ((∅ : Std.ExtTreeMap Nat Address).insert 100 a).insert 7 b⟩
private def storageIndex : WriteOrder Address :=
  ⟨0, (∅ : Std.ExtTreeMap Address Nat).insert a 7,
    (∅ : Std.ExtTreeMap Nat Address).insert 4 b⟩
private def slotIndex : WriteOrder Bytes32 :=
  ⟨2^400 + 19, (∅ : Std.ExtTreeMap Bytes32 Nat).insert high 99,
    (∅ : Std.ExtTreeMap Nat Bytes32).insert 2 low⟩
private def sample : TxRevertible :=
  ⟨((∅ : Std.ExtTreeMap Address (Option Account)).insert b
      (some ⟨2^1024 + 17, U256.max, h⟩)).insert a none,
    accountIndex,
    ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert b
      (((∅ : Std.ExtTreeMap Bytes32 U256).insert high U256.max).insert low U256.zero))
      |>.insert a ∅,
    storageIndex,
    ((∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert c WriteOrder.empty)
      |>.insert a slotIndex,
    ((∅ : Std.ExtTreeMap Hash32 ByteArray).insert h
      [0, 128, 255, 0, 128, 255].toByteArray).insert
      (Hash32.ofBytes32 low) ByteArray.empty,
    ((∅ : Std.ExtTreeSet Address).insert c).insert b,
    ((∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert (b, low) U256.max)
      |>.insert (a, high) U256.zero⟩

private def expected : Observation :=
  ([(ab, none), (bb, some (2^1024 + 17, 2^256 - 1, hashb))],
    (2^300 + 17, [(ab, 100), (bb, 4)], [(7, bb), (100, ab)]),
    [(ab, []), (bb, [(lb, 0), (hb, 2^256 - 1)])],
    (0, [(ab, 7)], [(4, bb)]),
    [(ab, (2^400 + 19, [(hb, 99)], [(2, lb)])), (cb, (0, [], []))],
    [(lb, []), (hashb, [0, 128, 255, 0, 128, 255])],
    [bb, cb], [((ab, hb), 0), ((bb, lb), 2^256 - 1)])

-- The full eight-field tuple requires a larger structural equality expression.
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

-- Kernel-checked whole observations retain tombstones/zeros/empty inners, complete
-- repeated bytes, all raw index entries, independent clears and both transient keys.
private theorem complete_sample : observe sample = expected := by decide

private def emptySample : TxRevertible :=
  ⟨∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅⟩
private theorem complete_empty :
    observe emptySample = ([], (0, [], []), [], (0, [], []), [], [], [], []) := by decide

-- Retained parent and independent children; no copy/restore operation is supplied.
private def accountChild : TxRevertible :=
  { sample with accountWrites := sample.accountWrites.insert c none }
private def transientChild : TxRevertible :=
  { sample with transient := sample.transient.insert (a, low) (U256.ofNat 17) }
private def clearChild : TxRevertible :=
  { sample with storageClears := sample.storageClears.insert a }

private theorem retained_parent_siblings :
    observe sample = expected ∧
    observe accountChild = ([(ab, none),
      (bb, some (2^1024 + 17, 2^256 - 1, hashb)), (cb, none)], expected.2) ∧
    transientChild.transient.toList.map (fun ((addr, slot), v) ↦
      ((addressBytes addr, slotBytes slot), v.toNat)) =
      [((ab, lb), 17), ((ab, hb), 0), ((bb, lb), 2^256 - 1)] ∧
    clearChild.storageClears.toList.map addressBytes = [ab, bb, cb] := by decide

private theorem complete_transient_child :
    observe transientChild =
  ([(ab, none), (bb, some (2^1024 + 17, 2^256 - 1, hashb))],
    (2^300 + 17, [(ab, 100), (bb, 4)], [(7, bb), (100, ab)]),
    [(ab, []), (bb, [(lb, 0), (hb, 2^256 - 1)])],
    (0, [(ab, 7)], [(4, bb)]),
    [(ab, (2^400 + 19, [(hb, 99)], [(2, lb)])), (cb, (0, [], []))],
    [(lb, []), (hashb, [0, 128, 255, 0, 128, 255])],
    [bb, cb], [((ab, lb), 17), ((ab, hb), 0), ((bb, lb), 2^256 - 1)]) := by decide

private theorem complete_clear_child :
    observe clearChild =
  ([(ab, none), (bb, some (2^1024 + 17, 2^256 - 1, hashb))],
    (2^300 + 17, [(ab, 100), (bb, 4)], [(7, bb), (100, ab)]),
    [(ab, []), (bb, [(lb, 0), (hb, 2^256 - 1)])],
    (0, [(ab, 7)], [(4, bb)]),
    [(ab, (2^400 + 19, [(hb, 99)], [(2, lb)])), (cb, (0, [], []))],
    [(lb, []), (hashb, [0, 128, 255, 0, 128, 255])],
    [ab, bb, cb], [((ab, hb), 0), ((bb, lb), 2^256 - 1)]) := by decide

-- Every replacement has a distinct complete observation while the parent survives.
private theorem independent_field_controls :
    observe { sample with accountWrites := ∅ } ≠ expected ∧
    observe { sample with accountOrder := WriteOrder.empty } ≠ expected ∧
    observe { sample with storageWrites := ∅ } ≠ expected ∧
    observe { sample with storageAddressOrder := WriteOrder.empty } ≠ expected ∧
    observe { sample with storageSlotOrder := ∅ } ≠ expected ∧
    observe { sample with codeWrites := ∅ } ≠ expected ∧
    observe { sample with storageClears := ∅ } ≠ expected ∧
    observe { sample with transient := ∅ } ≠ expected := by decide

end STFSpec.Conformance.State.TxRevertibleCallerProofs
