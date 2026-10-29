/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Std.Data.HashSet.Lemmas

/-!
# Raw block-state clients

Library `EthConformance`: private State-facade clients preserve complete arbitrary
provider functions and all thirteen supplied fields, without a class premise.
Public Base/Std laws supply key behavior; raw set equality is never inferred from membership.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.State.BlockStateCallerProofs

open STFSpec.State STFSpec.Base

variable {m : Type → Type}

private def exact_constructor :
    PreState m →
    HashConsts →
    Std.ExtTreeMap Address (Option Account) →
    WriteOrder Address →
    Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) →
    WriteOrder Address →
    Std.ExtTreeMap Address (WriteOrder Bytes32) →
    Std.ExtTreeMap Hash32 ByteArray →
    Std.ExtTreeSet Address →
    Std.HashSet Address →
    Std.HashSet (Address × Bytes32) →
    Std.HashSet (Address × Hash32) →
    Option Nat → BlockState m := @BlockState.mk m

private def exact_preState : BlockState m → PreState m := @BlockState.preState m

private def exact_consts : BlockState m → HashConsts := @BlockState.consts m

private def exact_accountWrites :
    BlockState m → Std.ExtTreeMap Address (Option Account) :=
  @BlockState.accountWrites m

private def exact_accountOrder : BlockState m → WriteOrder Address := @BlockState.accountOrder m

private def exact_storageWrites :
    BlockState m → Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  @BlockState.storageWrites m

private def exact_storageAddressOrder :
    BlockState m → WriteOrder Address :=
  @BlockState.storageAddressOrder m

private def exact_storageSlotOrder :
    BlockState m → Std.ExtTreeMap Address (WriteOrder Bytes32) :=
  @BlockState.storageSlotOrder m

private def exact_codeWrites :
    BlockState m → Std.ExtTreeMap Hash32 ByteArray :=
  @BlockState.codeWrites m

private def exact_storageClears :
    BlockState m → Std.ExtTreeSet Address :=
  @BlockState.storageClears m

private def exact_accountReads : BlockState m → Std.HashSet Address := @BlockState.accountReads m

private def exact_storageReads :
    BlockState m → Std.HashSet (Address × Bytes32) :=
  @BlockState.storageReads m

private def exact_codeReads :
    BlockState m → Std.HashSet (Address × Hash32) :=
  @BlockState.codeReads m

private def exact_oldestAncestorOffset :
    BlockState m → Option Nat :=
  @BlockState.oldestAncestorOffset m

private theorem supplied_constructor
    (preState : PreState m)
    (consts : HashConsts)
    (accountWrites : Std.ExtTreeMap Address (Option Account))
    (accountOrder : WriteOrder Address)
    (storageWrites : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (storageAddressOrder : WriteOrder Address)
    (storageSlotOrder : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (codeWrites : Std.ExtTreeMap Hash32 ByteArray)
    (storageClears : Std.ExtTreeSet Address)
    (accountReads : Std.HashSet Address)
    (storageReads : Std.HashSet (Address × Bytes32))
    (codeReads : Std.HashSet (Address × Hash32))
    (oldestAncestorOffset : Option Nat) :
    let b := BlockState.mk preState consts accountWrites accountOrder storageWrites
      storageAddressOrder storageSlotOrder codeWrites storageClears accountReads storageReads
      codeReads oldestAncestorOffset
    (b.preState, b.consts, b.accountWrites, b.accountOrder, b.storageWrites, b.storageAddressOrder,
      b.storageSlotOrder, b.codeWrites, b.storageClears, b.accountReads, b.storageReads,
      b.codeReads, b.oldestAncestorOffset) =
      (preState, consts, accountWrites, accountOrder, storageWrites, storageAddressOrder,
        storageSlotOrder, codeWrites, storageClears, accountReads, storageReads, codeReads,
        oldestAncestorOffset) := rfl

private theorem reconstruct (b : BlockState m) :
    BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
      b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears b.accountReads
      b.storageReads b.codeReads b.oldestAncestorOffset = b := rfl

private theorem whole_components (b c : BlockState m)
    (h0 : b.preState = c.preState)
    (h1 : b.consts = c.consts)
    (h2 : b.accountWrites = c.accountWrites)
    (h3 : b.accountOrder = c.accountOrder)
    (h4 : b.storageWrites = c.storageWrites)
    (h5 : b.storageAddressOrder = c.storageAddressOrder)
    (h6 : b.storageSlotOrder = c.storageSlotOrder)
    (h7 : b.codeWrites = c.codeWrites)
    (h8 : b.storageClears = c.storageClears)
    (h9 : b.accountReads = c.accountReads)
    (h10 : b.storageReads = c.storageReads)
    (h11 : b.codeReads = c.codeReads)
    (h12 : b.oldestAncestorOffset = c.oldestAncestorOffset) : b = c := by
  cases b
  cases c
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  cases h11
  cases h12
  rfl

private theorem replace_preState
    (b : BlockState m) (x : PreState m) :
    ({ b with preState := x } : BlockState m) =
      BlockState.mk x b.consts b.accountWrites b.accountOrder b.storageWrites b.storageAddressOrder
        b.storageSlotOrder b.codeWrites b.storageClears b.accountReads b.storageReads b.codeReads
        b.oldestAncestorOffset := rfl

private theorem replace_consts
    (b : BlockState m) (x : HashConsts) :
    ({ b with consts := x } : BlockState m) =
      BlockState.mk b.preState x b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears b.accountReads
        b.storageReads b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_accountWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account)) :
    ({ b with accountWrites := x } : BlockState m) =
      BlockState.mk b.preState b.consts x b.accountOrder b.storageWrites b.storageAddressOrder
        b.storageSlotOrder b.codeWrites b.storageClears b.accountReads b.storageReads b.codeReads
        b.oldestAncestorOffset := rfl

private theorem replace_accountOrder
    (b : BlockState m) (x : WriteOrder Address) :
    ({ b with accountOrder := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites x b.storageWrites b.storageAddressOrder
        b.storageSlotOrder b.codeWrites b.storageClears b.accountReads b.storageReads b.codeReads
        b.oldestAncestorOffset := rfl

private theorem replace_storageWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ b with storageWrites := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder x b.storageAddressOrder
        b.storageSlotOrder b.codeWrites b.storageClears b.accountReads b.storageReads b.codeReads
        b.oldestAncestorOffset := rfl

private theorem replace_storageAddressOrder
    (b : BlockState m) (x : WriteOrder Address) :
    ({ b with storageAddressOrder := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites x
        b.storageSlotOrder b.codeWrites b.storageClears b.accountReads b.storageReads b.codeReads
        b.oldestAncestorOffset := rfl

private theorem replace_storageSlotOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ b with storageSlotOrder := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder x b.codeWrites b.storageClears b.accountReads b.storageReads
        b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_codeWrites
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray) :
    ({ b with codeWrites := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder x b.storageClears b.accountReads b.storageReads
        b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_storageClears
    (b : BlockState m) (x : Std.ExtTreeSet Address) :
    ({ b with storageClears := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites x b.accountReads b.storageReads
        b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_accountReads
    (b : BlockState m) (x : Std.HashSet Address) :
    ({ b with accountReads := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears x b.storageReads
        b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_storageReads
    (b : BlockState m) (x : Std.HashSet (Address × Bytes32)) :
    ({ b with storageReads := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears b.accountReads x
        b.codeReads b.oldestAncestorOffset := rfl

private theorem replace_codeReads
    (b : BlockState m) (x : Std.HashSet (Address × Hash32)) :
    ({ b with codeReads := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears b.accountReads
        b.storageReads x b.oldestAncestorOffset := rfl

private theorem replace_oldestAncestorOffset
    (b : BlockState m) (x : Option Nat) :
    ({ b with oldestAncestorOffset := x } : BlockState m) =
      BlockState.mk b.preState b.consts b.accountWrites b.accountOrder b.storageWrites
        b.storageAddressOrder b.storageSlotOrder b.codeWrites b.storageClears b.accountReads
        b.storageReads b.codeReads x := rfl

private theorem commute_preState_consts
    (b : BlockState m) (x : PreState m)
    (y : HashConsts) :
    ({ { b with preState := x } with consts := y } : BlockState m) =
      { { b with consts := y } with preState := x } := rfl

private theorem commute_preState_accountWrites
    (b : BlockState m) (x : PreState m)
    (y : Std.ExtTreeMap Address (Option Account)) :
    ({ { b with preState := x } with accountWrites := y } : BlockState m) =
      { { b with accountWrites := y } with preState := x } := rfl

private theorem commute_preState_accountOrder
    (b : BlockState m) (x : PreState m)
    (y : WriteOrder Address) :
    ({ { b with preState := x } with accountOrder := y } : BlockState m) =
      { { b with accountOrder := y } with preState := x } := rfl

private theorem commute_preState_storageWrites
    (b : BlockState m) (x : PreState m)
    (y : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ { b with preState := x } with storageWrites := y } : BlockState m) =
      { { b with storageWrites := y } with preState := x } := rfl

private theorem commute_preState_storageAddressOrder
    (b : BlockState m) (x : PreState m)
    (y : WriteOrder Address) :
    ({ { b with preState := x } with storageAddressOrder := y } : BlockState m) =
      { { b with storageAddressOrder := y } with preState := x } := rfl

private theorem commute_preState_storageSlotOrder
    (b : BlockState m) (x : PreState m)
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with preState := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with preState := x } := rfl

private theorem commute_preState_codeWrites
    (b : BlockState m) (x : PreState m)
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with preState := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with preState := x } := rfl

private theorem commute_preState_storageClears
    (b : BlockState m) (x : PreState m)
    (y : Std.ExtTreeSet Address) :
    ({ { b with preState := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with preState := x } := rfl

private theorem commute_preState_accountReads
    (b : BlockState m) (x : PreState m)
    (y : Std.HashSet Address) :
    ({ { b with preState := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with preState := x } := rfl

private theorem commute_preState_storageReads
    (b : BlockState m) (x : PreState m)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with preState := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with preState := x } := rfl

private theorem commute_preState_codeReads
    (b : BlockState m) (x : PreState m)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with preState := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with preState := x } := rfl

private theorem commute_preState_oldestAncestorOffset
    (b : BlockState m) (x : PreState m)
    (y : Option Nat) :
    ({ { b with preState := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with preState := x } := rfl

private theorem commute_consts_accountWrites
    (b : BlockState m) (x : HashConsts)
    (y : Std.ExtTreeMap Address (Option Account)) :
    ({ { b with consts := x } with accountWrites := y } : BlockState m) =
      { { b with accountWrites := y } with consts := x } := rfl

private theorem commute_consts_accountOrder
    (b : BlockState m) (x : HashConsts)
    (y : WriteOrder Address) :
    ({ { b with consts := x } with accountOrder := y } : BlockState m) =
      { { b with accountOrder := y } with consts := x } := rfl

private theorem commute_consts_storageWrites
    (b : BlockState m) (x : HashConsts)
    (y : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ { b with consts := x } with storageWrites := y } : BlockState m) =
      { { b with storageWrites := y } with consts := x } := rfl

private theorem commute_consts_storageAddressOrder
    (b : BlockState m) (x : HashConsts)
    (y : WriteOrder Address) :
    ({ { b with consts := x } with storageAddressOrder := y } : BlockState m) =
      { { b with storageAddressOrder := y } with consts := x } := rfl

private theorem commute_consts_storageSlotOrder
    (b : BlockState m) (x : HashConsts)
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with consts := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with consts := x } := rfl

private theorem commute_consts_codeWrites
    (b : BlockState m) (x : HashConsts)
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with consts := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with consts := x } := rfl

private theorem commute_consts_storageClears
    (b : BlockState m) (x : HashConsts)
    (y : Std.ExtTreeSet Address) :
    ({ { b with consts := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with consts := x } := rfl

private theorem commute_consts_accountReads
    (b : BlockState m) (x : HashConsts)
    (y : Std.HashSet Address) :
    ({ { b with consts := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with consts := x } := rfl

private theorem commute_consts_storageReads
    (b : BlockState m) (x : HashConsts)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with consts := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with consts := x } := rfl

private theorem commute_consts_codeReads
    (b : BlockState m) (x : HashConsts)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with consts := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with consts := x } := rfl

private theorem commute_consts_oldestAncestorOffset
    (b : BlockState m) (x : HashConsts)
    (y : Option Nat) :
    ({ { b with consts := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with consts := x } := rfl

private theorem commute_accountWrites_accountOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : WriteOrder Address) :
    ({ { b with accountWrites := x } with accountOrder := y } : BlockState m) =
      { { b with accountOrder := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_storageWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ { b with accountWrites := x } with storageWrites := y } : BlockState m) =
      { { b with storageWrites := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_storageAddressOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : WriteOrder Address) :
    ({ { b with accountWrites := x } with storageAddressOrder := y } : BlockState m) =
      { { b with storageAddressOrder := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_storageSlotOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with accountWrites := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_codeWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with accountWrites := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_storageClears
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.ExtTreeSet Address) :
    ({ { b with accountWrites := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_accountReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.HashSet Address) :
    ({ { b with accountWrites := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_storageReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with accountWrites := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_codeReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with accountWrites := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with accountWrites := x } := rfl

private theorem commute_accountWrites_oldestAncestorOffset
    (b : BlockState m) (x : Std.ExtTreeMap Address (Option Account))
    (y : Option Nat) :
    ({ { b with accountWrites := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with accountWrites := x } := rfl

private theorem commute_accountOrder_storageWrites
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) :
    ({ { b with accountOrder := x } with storageWrites := y } : BlockState m) =
      { { b with storageWrites := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_storageAddressOrder
    (b : BlockState m) (x : WriteOrder Address)
    (y : WriteOrder Address) :
    ({ { b with accountOrder := x } with storageAddressOrder := y } : BlockState m) =
      { { b with storageAddressOrder := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_storageSlotOrder
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with accountOrder := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_codeWrites
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with accountOrder := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_storageClears
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeSet Address) :
    ({ { b with accountOrder := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_accountReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet Address) :
    ({ { b with accountOrder := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_storageReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with accountOrder := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_codeReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with accountOrder := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with accountOrder := x } := rfl

private theorem commute_accountOrder_oldestAncestorOffset
    (b : BlockState m) (x : WriteOrder Address)
    (y : Option Nat) :
    ({ { b with accountOrder := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with accountOrder := x } := rfl

private theorem commute_storageWrites_storageAddressOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : WriteOrder Address) :
    ({ { b with storageWrites := x } with storageAddressOrder := y } : BlockState m) =
      { { b with storageAddressOrder := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_storageSlotOrder
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with storageWrites := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_codeWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with storageWrites := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_storageClears
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.ExtTreeSet Address) :
    ({ { b with storageWrites := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_accountReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.HashSet Address) :
    ({ { b with storageWrites := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_storageReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with storageWrites := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_codeReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with storageWrites := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with storageWrites := x } := rfl

private theorem commute_storageWrites_oldestAncestorOffset
    (b : BlockState m) (x : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (y : Option Nat) :
    ({ { b with storageWrites := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with storageWrites := x } := rfl

private theorem commute_storageAddressOrder_storageSlotOrder
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ { b with storageAddressOrder := x } with storageSlotOrder := y } : BlockState m) =
      { { b with storageSlotOrder := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_codeWrites
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with storageAddressOrder := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_storageClears
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.ExtTreeSet Address) :
    ({ { b with storageAddressOrder := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_accountReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet Address) :
    ({ { b with storageAddressOrder := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_storageReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with storageAddressOrder := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_codeReads
    (b : BlockState m) (x : WriteOrder Address)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with storageAddressOrder := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with storageAddressOrder := x } := rfl

private theorem commute_storageAddressOrder_oldestAncestorOffset
    (b : BlockState m) (x : WriteOrder Address)
    (y : Option Nat) :
    ({ { b with storageAddressOrder := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with storageAddressOrder := x } := rfl

private theorem commute_storageSlotOrder_codeWrites
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Std.ExtTreeMap Hash32 ByteArray) :
    ({ { b with storageSlotOrder := x } with codeWrites := y } : BlockState m) =
      { { b with codeWrites := y } with storageSlotOrder := x } := rfl

private theorem commute_storageSlotOrder_storageClears
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Std.ExtTreeSet Address) :
    ({ { b with storageSlotOrder := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with storageSlotOrder := x } := rfl

private theorem commute_storageSlotOrder_accountReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Std.HashSet Address) :
    ({ { b with storageSlotOrder := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with storageSlotOrder := x } := rfl

private theorem commute_storageSlotOrder_storageReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with storageSlotOrder := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with storageSlotOrder := x } := rfl

private theorem commute_storageSlotOrder_codeReads
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with storageSlotOrder := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with storageSlotOrder := x } := rfl

private theorem commute_storageSlotOrder_oldestAncestorOffset
    (b : BlockState m) (x : Std.ExtTreeMap Address (WriteOrder Bytes32))
    (y : Option Nat) :
    ({ { b with storageSlotOrder := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with storageSlotOrder := x } := rfl

private theorem commute_codeWrites_storageClears
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (y : Std.ExtTreeSet Address) :
    ({ { b with codeWrites := x } with storageClears := y } : BlockState m) =
      { { b with storageClears := y } with codeWrites := x } := rfl

private theorem commute_codeWrites_accountReads
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (y : Std.HashSet Address) :
    ({ { b with codeWrites := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with codeWrites := x } := rfl

private theorem commute_codeWrites_storageReads
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with codeWrites := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with codeWrites := x } := rfl

private theorem commute_codeWrites_codeReads
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with codeWrites := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with codeWrites := x } := rfl

private theorem commute_codeWrites_oldestAncestorOffset
    (b : BlockState m) (x : Std.ExtTreeMap Hash32 ByteArray)
    (y : Option Nat) :
    ({ { b with codeWrites := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with codeWrites := x } := rfl

private theorem commute_storageClears_accountReads
    (b : BlockState m) (x : Std.ExtTreeSet Address)
    (y : Std.HashSet Address) :
    ({ { b with storageClears := x } with accountReads := y } : BlockState m) =
      { { b with accountReads := y } with storageClears := x } := rfl

private theorem commute_storageClears_storageReads
    (b : BlockState m) (x : Std.ExtTreeSet Address)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with storageClears := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with storageClears := x } := rfl

private theorem commute_storageClears_codeReads
    (b : BlockState m) (x : Std.ExtTreeSet Address)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with storageClears := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with storageClears := x } := rfl

private theorem commute_storageClears_oldestAncestorOffset
    (b : BlockState m) (x : Std.ExtTreeSet Address)
    (y : Option Nat) :
    ({ { b with storageClears := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with storageClears := x } := rfl

private theorem commute_accountReads_storageReads
    (b : BlockState m) (x : Std.HashSet Address)
    (y : Std.HashSet (Address × Bytes32)) :
    ({ { b with accountReads := x } with storageReads := y } : BlockState m) =
      { { b with storageReads := y } with accountReads := x } := rfl

private theorem commute_accountReads_codeReads
    (b : BlockState m) (x : Std.HashSet Address)
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with accountReads := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with accountReads := x } := rfl

private theorem commute_accountReads_oldestAncestorOffset
    (b : BlockState m) (x : Std.HashSet Address)
    (y : Option Nat) :
    ({ { b with accountReads := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with accountReads := x } := rfl

private theorem commute_storageReads_codeReads
    (b : BlockState m) (x : Std.HashSet (Address × Bytes32))
    (y : Std.HashSet (Address × Hash32)) :
    ({ { b with storageReads := x } with codeReads := y } : BlockState m) =
      { { b with codeReads := y } with storageReads := x } := rfl

private theorem commute_storageReads_oldestAncestorOffset
    (b : BlockState m) (x : Std.HashSet (Address × Bytes32))
    (y : Option Nat) :
    ({ { b with storageReads := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with storageReads := x } := rfl

private theorem commute_codeReads_oldestAncestorOffset
    (b : BlockState m) (x : Std.HashSet (Address × Hash32))
    (y : Option Nat) :
    ({ { b with codeReads := x } with oldestAncestorOffset := y } : BlockState m) =
      { { b with oldestAncestorOffset := y } with codeReads := x } := rfl

-- This contravariant constructor has no installed Monad instance.
private def Consumer (α : Type) : Type := α → Nat

private def no_monad (ps : PreState Consumer)
    (b : BlockState Consumer) : BlockState Consumer := { b with preState := ps }

private theorem no_monad_preserves (ps : PreState Consumer) (b : BlockState Consumer) :
    (no_monad ps b).preState = ps ∧
      (no_monad ps b).oldestAncestorOffset = b.oldestAncestorOffset := ⟨rfl, rfl⟩

private theorem full_provider (b : BlockState m) (ps : PreState m) :
    ({ b with preState := ps } : BlockState m).preState = ps := rfl

private theorem canonical_address : (inferInstance : Hashable Address) = Address.instHashable :=
    rfl
private theorem canonical_slot : (inferInstance : Hashable Bytes32) = Bytes32.instHashable := rfl
private theorem canonical_hash (h : Hash32) : hash h = Hash32.tableHashReference h :=
  Hash32.hash_eq_reference h
private theorem storage_product (x : Address × Bytes32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl
private theorem code_product (x : Address × Hash32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl

private theorem members {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (s t : Std.HashSet α) (key query : α) :
    (query ∈ s.insert key ↔ key = query ∨ query ∈ s) ∧
    (query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t) ∧
    (query ∈ (s.insert key).insert key ↔ query ∈ s.insert key) := by
  have hi : ∀ u : Std.HashSet α, query ∈ u.insert key ↔ key = query ∨ query ∈ u := by
    intro u
    simpa only [beq_iff_eq] using (Std.HashSet.mem_insert (m := u) (k := key) (a := query))
  exact ⟨hi s, Std.HashSet.mem_union_iff, by simp only [hi, or_self_left]⟩

private theorem account_members (b : BlockState m) (s : Std.HashSet Address) (k a : Address) :
    (a ∈ b.accountReads.insert k ↔ k = a ∨ a ∈ b.accountReads) ∧
    (a ∈ b.accountReads ∪ s ↔ a ∈ b.accountReads ∨ a ∈ s) ∧
    (a ∈ (b.accountReads.insert k).insert k ↔ a ∈ b.accountReads.insert k) :=
  members b.accountReads s k a
private theorem storage_members (b : BlockState m) (s : Std.HashSet (Address × Bytes32))
    (k a : Address × Bytes32) :
    (a ∈ b.storageReads.insert k ↔ k = a ∨ a ∈ b.storageReads) ∧
    (a ∈ b.storageReads ∪ s ↔ a ∈ b.storageReads ∨ a ∈ s) ∧
    (a ∈ (b.storageReads.insert k).insert k ↔ a ∈ b.storageReads.insert k) :=
  members b.storageReads s k a
private theorem code_members (b : BlockState m) (s : Std.HashSet (Address × Hash32))
    (k a : Address × Hash32) :
    (a ∈ b.codeReads.insert k ↔ k = a ∨ a ∈ b.codeReads) ∧
    (a ∈ b.codeReads ∪ s ↔ a ∈ b.codeReads ∨ a ∈ s) ∧
    (a ∈ (b.codeReads.insert k).insert k ↔ a ∈ b.codeReads.insert k) :=
  members b.codeReads s k a

private theorem reconstructed_account (b : BlockState m) (a : Address) :
    Address.ofNat a.toNat ∈ b.accountReads.insert a := by
  rw [Address.ofNat_toNat]
  exact Std.HashSet.mem_insert_self
private theorem reconstructed_storage (b : BlockState m) (a : Address) (k : Bytes32) :
    (Address.ofNat a.toNat, FixedBytes.ofNat k.toNat) ∈ b.storageReads.insert (a, k) := by
  rw [Address.ofNat_toNat, FixedBytes.ofNat_toNat]
  exact Std.HashSet.mem_insert_self
private theorem reconstructed_code (b : BlockState m) (a : Address) (h : Hash32) :
    (Address.ofNat a.toNat, Hash32.ofBytes32 h.toBytes32) ∈ b.codeReads.insert (a, h) := by
  rw [Address.ofNat_toNat, Hash32.ofBytes32_toBytes32]
  exact Std.HashSet.mem_insert_self

end STFSpec.Conformance.State.BlockStateCallerProofs
