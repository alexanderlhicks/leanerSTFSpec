/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Public logical-read-set clients

Library `EthConformance`: class-free clients use the two public iff laws in both
directions. Whole-field independence uses public record updates and those laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7/8.
-/

namespace STFSpec.Conformance.State.ReadSetsCallerProofs

open STFSpec.State STFSpec.Base

variable {m : Type → Type}

private def accountSignature : {m : Type → Type} → BlockState m → Address → Prop :=
  @BlockState.accountReadSet
private def storageSignature :
    {m : Type → Type} → BlockState m → (Address × Bytes32) → Prop :=
  @BlockState.storageReadSet
private theorem accountLawSignature : ∀ {m : Type → Type} (b : BlockState m) (a : Address),
    BlockState.accountReadSet b a ↔ a ∈ b.accountReads := @BlockState.accountReadSet_iff
private theorem storageLawSignature : ∀ {m : Type → Type} (b : BlockState m)
    (pair : Address × Bytes32), BlockState.storageReadSet b pair ↔ pair ∈ b.storageReads :=
  @BlockState.storageReadSet_iff

private theorem accountForward (b : BlockState m) (a : Address)
    (h : b.accountReadSet a) : a ∈ b.accountReads := (BlockState.accountReadSet_iff b a).mp h
private theorem accountBackward (b : BlockState m) (a : Address)
    (h : a ∈ b.accountReads) : b.accountReadSet a := (BlockState.accountReadSet_iff b a).mpr h
private theorem storageForward (b : BlockState m) (pair : Address × Bytes32)
    (h : b.storageReadSet pair) : pair ∈ b.storageReads :=
  (BlockState.storageReadSet_iff b pair).mp h
private theorem storageBackward (b : BlockState m) (pair : Address × Bytes32)
    (h : pair ∈ b.storageReads) : b.storageReadSet pair :=
  (BlockState.storageReadSet_iff b pair).mpr h

private def Contravariant (α : Type) : Type := α → Nat
#check_failure (inferInstance : Monad Contravariant)

private theorem noMonadAccount (b : BlockState Contravariant) (a : Address) :
    b.accountReadSet a ↔ a ∈ b.accountReads := BlockState.accountReadSet_iff b a
private theorem noMonadStorage (b : BlockState Contravariant) (pair : Address × Bytes32) :
    b.storageReadSet pair ↔ pair ∈ b.storageReads := BlockState.storageReadSet_iff b pair

private theorem accountField (b c : BlockState m) (h : b.accountReads = c.accountReads)
    (a : Address) : b.accountReadSet a ↔ c.accountReadSet a := by
  rw [BlockState.accountReadSet_iff, BlockState.accountReadSet_iff, h]
private theorem storageField (b c : BlockState m) (h : b.storageReads = c.storageReads)
    (pair : Address × Bytes32) : b.storageReadSet pair ↔ c.storageReadSet pair := by
  rw [BlockState.storageReadSet_iff, BlockState.storageReadSet_iff, h]

private theorem accountIndependent_preState (b : BlockState m) (x : PreState m)
    (key : Address) :
    ({ b with preState := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_preState (b : BlockState m) (x : PreState m)
    (key : Address × Bytes32) :
    ({ b with preState := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_consts (b : BlockState m) (x : HashConsts)
    (key : Address) :
    ({ b with consts := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_consts (b : BlockState m) (x : HashConsts)
    (key : Address × Bytes32) :
    ({ b with consts := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_accountWrites (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (key : Address) :
    ({ b with accountWrites := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_accountWrites (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (key : Address × Bytes32) :
    ({ b with accountWrites := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_accountOrder (b : BlockState m) (x : WriteOrder Address)
    (key : Address) :
    ({ b with accountOrder := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_accountOrder (b : BlockState m) (x : WriteOrder Address)
    (key : Address × Bytes32) :
    ({ b with accountOrder := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_storageWrites (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (key : Address) :
    ({ b with storageWrites := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_storageWrites (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (key : Address × Bytes32) :
    ({ b with storageWrites := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_storageAddressOrder (b : BlockState m) (x : WriteOrder Address)
    (key : Address) :
    ({ b with storageAddressOrder := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_storageAddressOrder (b : BlockState m) (x : WriteOrder Address)
    (key : Address × Bytes32) :
    ({ b with storageAddressOrder := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_storageSlotOrder (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (key : Address) :
    ({ b with storageSlotOrder := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_storageSlotOrder (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (key : Address × Bytes32) :
    ({ b with storageSlotOrder := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_codeWrites (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (key : Address) :
    ({ b with codeWrites := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_codeWrites (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (key : Address × Bytes32) :
    ({ b with codeWrites := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_storageClears (b : BlockState m) (x : Std.ExtTreeSet Address)
    (key : Address) :
    ({ b with storageClears := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_storageClears (b : BlockState m) (x : Std.ExtTreeSet Address)
    (key : Address × Bytes32) :
    ({ b with storageClears := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem storageIndependent_accountReads (b : BlockState m) (x : Std.HashSet Address)
    (key : Address × Bytes32) :
    ({ b with accountReads := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_storageReads (b : BlockState m) (x : Std.HashSet (Address × Bytes32))
    (key : Address) :
    ({ b with storageReads := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem accountIndependent_codeReads (b : BlockState m) (x : Std.HashSet (Address × Hash32))
    (key : Address) :
    ({ b with codeReads := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_codeReads (b : BlockState m) (x : Std.HashSet (Address × Hash32))
    (key : Address × Bytes32) :
    ({ b with codeReads := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

private theorem accountIndependent_oldestAncestorOffset (b : BlockState m) (x : Option Nat)
    (key : Address) :
    ({ b with oldestAncestorOffset := x } : BlockState m).accountReadSet key ↔ b.accountReadSet key :=
  accountField _ b rfl key

private theorem storageIndependent_oldestAncestorOffset (b : BlockState m) (x : Option Nat)
    (key : Address × Bytes32) :
    ({ b with oldestAncestorOffset := x } : BlockState m).storageReadSet key ↔ b.storageReadSet key :=
  storageField _ b rfl key

end STFSpec.Conformance.State.ReadSetsCallerProofs
