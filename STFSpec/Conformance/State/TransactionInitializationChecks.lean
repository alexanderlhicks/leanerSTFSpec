/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Lean.Data.Json
import STFSpec.State

/-!
# Fresh transaction-state controls

Library `EthConformance`. Use the public State facade to check fresh defaults
over raw supplied block contexts and the exact class-free constructor.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.TransactionInitializationChecks

open STFSpec.Base STFSpec.State

private theorem complete {m : Type → Type} (b : BlockState m) :
    TxState.new b = ⟨b, ⟨∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅⟩,
      ⟨∅, ∅, ∅, ∅⟩⟩ := rfl

private theorem fresh_after_parent_update {m : Type → Type} (t : TxState m)
    (b : BlockState m) :
    (TxState.new b).rev = (TxState.new t.block).rev ∧
      (TxState.new b).obs = (TxState.new t.block).obs ∧
      (TxState.new b).block = b := ⟨rfl, rfl, rfl⟩

private def provider : PreState Id :=
  ⟨fun _ ↦ .ok none, fun _ _ ↦ .ok U256.zero, fun _ ↦ .ok ByteArray.empty,
    fun _ ↦ .ok (Hash32.ofBytes32 (FixedBytes.ofNat 23))⟩

private def observe (cursor : Option Nat) (salt : Nat) : Lean.Json :=
  let a := Address.ofNat salt
  let hash := Hash32.ofBytes32 (FixedBytes.ofNat salt)
  let b := BlockState.new provider ⟨hash, hash, hash, hash⟩
  let accountReads := b.accountReads.insert a
  let accountWrites := b.accountWrites.insert a none
  let ready := { b with accountReads := accountReads, accountWrites := accountWrites }
  let ready := { ready with oldestAncestorOffset := cursor }
  let t := TxState.new ready
  Lean.Json.mkObj [
    ("cursor", Lean.toJson t.block.oldestAncestorOffset),
    ("parentRead", Lean.toJson (t.block.accountReads.contains a)),
    ("parentTombstone", Lean.toJson (t.block.accountWrites[a]? == some none)),
    ("sizes", Lean.toJson [t.rev.accountWrites.size, t.rev.storageWrites.size,
      t.rev.codeWrites.size, t.rev.storageClears.size, t.rev.transient.size,
      t.obs.accountReads.size, t.obs.storageReads.size, t.obs.codeReads.size,
      t.obs.createdAccounts.size]),
    ("order", Lean.toJson [
      t.rev.accountOrder.next, t.rev.accountOrder.positions.size, t.rev.accountOrder.keysByPosition.size,
      t.rev.storageAddressOrder.next, t.rev.storageAddressOrder.positions.size,
      t.rev.storageAddressOrder.keysByPosition.size, t.rev.storageSlotOrder.size])
  ]

private def inputs : List (Option Nat × Nat) := [(none, 0), (some 0, 1),
  (some 256, 2 ^ 159 + 3), (some (2 ^ 256), 17)]

#guard inputs.all (fun (cursor, salt) ↦
  (observe cursor salt).compress ==
    (Lean.Json.mkObj [
      ("cursor", Lean.toJson cursor),
      ("parentRead", Lean.toJson true),
      ("parentTombstone", Lean.toJson true),
      ("sizes", Lean.toJson (List.replicate 9 (0 : Nat))),
      ("order", Lean.toJson (List.replicate 7 (0 : Nat)))
    ]).compress)

end STFSpec.Conformance.State.TransactionInitializationChecks
