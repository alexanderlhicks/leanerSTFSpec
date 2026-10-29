/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Raw mutable frame and persistent-set clients

Library `EthConformance`. Private generic clients use public record reduction,
Base ordering laws and Std set laws. Every field replacement retains all eight
unrelated fields; no global frame invariant or new public law is required.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.FrameCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem address_set_membership (a b : AddrSet) (x y : Address) :
    x ∉ (∅ : AddrSet) ∧
      (x ∈ a.insert y ↔ compare y x = .eq ∨ x ∈ a) ∧
      (x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b) := by
  exact ⟨Std.ExtTreeSet.not_mem_empty, Std.ExtTreeSet.mem_insert,
    Std.ExtTreeSet.mem_union_iff⟩

private theorem slot_set_membership (a b : SlotSet) (x y : Address × Bytes32) :
    x ∉ (∅ : SlotSet) ∧
      (x ∈ a.insert y ↔ compare y x = .eq ∨ x ∈ a) ∧
      (x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b) := by
  exact ⟨Std.ExtTreeSet.not_mem_empty, Std.ExtTreeSet.mem_insert,
    Std.ExtTreeSet.mem_union_iff⟩

private theorem address_lexical_order (x y : Address) :
    compare x y = compare x.toBytes.toList y.toBytes.toList := by
  exact Address.compare_toBytes x y

private theorem slot_lexical_order (x y : Address × Bytes32) :
    compare x y =
      (compare x.1.toBytes.toList y.1.toBytes.toList).then
        (compare x.2.toBytes.toList y.2.toBytes.toList) := by
  exact compare_address_slot_toBytes x y

private theorem supplied_constructor (pc : Nat)
    (stack : Stack)
    (memory : Memory)
    (gasMeter : GasMeter)
    (logs : LogRope)
    (accountsToDelete : AddrSet)
    (returnData : Bytes)
    (accessedAddresses : AddrSet)
    (accessedStorageKeys : SlotSet) :
    let f := Frame.mk pc stack memory gasMeter logs accountsToDelete
      returnData accessedAddresses accessedStorageKeys
    (f.pc, f.stack, f.memory, f.gasMeter, f.logs, f.accountsToDelete,
      f.returnData, f.accessedAddresses, f.accessedStorageKeys) =
      (pc, stack, memory, gasMeter, logs, accountsToDelete,
        returnData, accessedAddresses, accessedStorageKeys) := by
  rfl

private theorem reconstruct (f : Frame) :
    Frame.mk f.pc f.stack f.memory f.gasMeter f.logs f.accountsToDelete
      f.returnData f.accessedAddresses f.accessedStorageKeys = f := by
  rfl

private theorem replace_pc (f : Frame) (replacement : Nat) :
    ({ f with pc := replacement } : Frame) =
      Frame.mk replacement f.stack f.memory f.gasMeter
        f.logs f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_stack (f : Frame) (replacement : Stack) :
    ({ f with stack := replacement } : Frame) =
      Frame.mk f.pc replacement f.memory f.gasMeter
        f.logs f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_memory (f : Frame) (replacement : Memory) :
    ({ f with memory := replacement } : Frame) =
      Frame.mk f.pc f.stack replacement f.gasMeter
        f.logs f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_gas_meter (f : Frame) (replacement : GasMeter) :
    ({ f with gasMeter := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory replacement
        f.logs f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_logs (f : Frame) (replacement : LogRope) :
    ({ f with logs := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter
        replacement f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_accounts_to_delete (f : Frame) (replacement : AddrSet) :
    ({ f with accountsToDelete := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter
        f.logs replacement f.returnData f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_return_data (f : Frame) (replacement : Bytes) :
    ({ f with returnData := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter
        f.logs f.accountsToDelete replacement f.accessedAddresses f.accessedStorageKeys := by
  rfl

private theorem replace_accessed_addresses (f : Frame) (replacement : AddrSet) :
    ({ f with accessedAddresses := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter
        f.logs f.accountsToDelete f.returnData replacement f.accessedStorageKeys := by
  rfl

private theorem replace_accessed_storage_keys (f : Frame) (replacement : SlotSet) :
    ({ f with accessedStorageKeys := replacement } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter
        f.logs f.accountsToDelete f.returnData f.accessedAddresses replacement := by
  rfl

private theorem independent_effect_updates (f : Frame) (deleted warm : AddrSet)
    (slots : SlotSet) (returned : Bytes) (logs : LogRope) :
    ({ f with
      accountsToDelete := deleted
      accessedAddresses := warm
      accessedStorageKeys := slots
      returnData := returned
      logs := logs } : Frame) =
      Frame.mk f.pc f.stack f.memory f.gasMeter logs deleted returned warm slots := by
  rfl

end STFSpec.Conformance.Vm.Core.FrameCallerProofs
