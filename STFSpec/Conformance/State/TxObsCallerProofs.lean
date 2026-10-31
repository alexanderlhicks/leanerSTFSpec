/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Std.Data.HashSet.Lemmas

/-!
# Raw transaction observation clients

Library `EthConformance`: private whole-record clients quantify arbitrary actual raw sets.
Public Base equality/reconstruction and Std membership laws supply key behavior.
No bucket/storage unfolding, set extensionality, tracker or lifetime claim is used.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.State.TxObsCallerProofs

open STFSpec.State STFSpec.Base

private theorem supplied_constructor
    (accounts : Std.HashSet Address) (storage : Std.HashSet (Address × Bytes32))
    (code : Std.HashSet (Address × Hash32)) (created : Std.HashSet Address) :
    let t := TxObs.mk accounts storage code created
    (t.accountReads, t.storageReads, t.codeReads, t.createdAccounts) =
      (accounts, storage, code, created) := rfl

private theorem reconstruct (t : TxObs) :
    TxObs.mk t.accountReads t.storageReads t.codeReads t.createdAccounts = t := rfl

private theorem whole_components (t u : TxObs)
    (ha : t.accountReads = u.accountReads) (hs : t.storageReads = u.storageReads)
    (hc : t.codeReads = u.codeReads) (hn : t.createdAccounts = u.createdAccounts) :
    t = u := by
  cases t
  cases u
  cases ha
  cases hs
  cases hc
  cases hn
  rfl

private theorem replace_accountReads (t : TxObs) (replacement : Std.HashSet Address) :
    ({ t with accountReads := replacement } : TxObs) =
      TxObs.mk replacement t.storageReads t.codeReads t.createdAccounts := rfl

private theorem replace_storageReads (t : TxObs) (replacement : Std.HashSet (Address × Bytes32)) :
    ({ t with storageReads := replacement } : TxObs) =
      TxObs.mk t.accountReads replacement t.codeReads t.createdAccounts := rfl

private theorem replace_codeReads (t : TxObs) (replacement : Std.HashSet (Address × Hash32)) :
    ({ t with codeReads := replacement } : TxObs) =
      TxObs.mk t.accountReads t.storageReads replacement t.createdAccounts := rfl

private theorem replace_createdAccounts (t : TxObs) (replacement : Std.HashSet Address) :
    ({ t with createdAccounts := replacement } : TxObs) =
      TxObs.mk t.accountReads t.storageReads t.codeReads replacement := rfl

private theorem commute_accountReads_storageReads (t : TxObs)
    (x : Std.HashSet Address) (y : Std.HashSet (Address × Bytes32)) :
    ({ { t with accountReads := x } with storageReads := y } : TxObs) =
      { { t with storageReads := y } with accountReads := x } := rfl

private theorem commute_accountReads_codeReads (t : TxObs)
    (x : Std.HashSet Address) (y : Std.HashSet (Address × Hash32)) :
    ({ { t with accountReads := x } with codeReads := y } : TxObs) =
      { { t with codeReads := y } with accountReads := x } := rfl

private theorem commute_accountReads_createdAccounts (t : TxObs)
    (x : Std.HashSet Address) (y : Std.HashSet Address) :
    ({ { t with accountReads := x } with createdAccounts := y } : TxObs) =
      { { t with createdAccounts := y } with accountReads := x } := rfl

private theorem commute_storageReads_codeReads (t : TxObs)
    (x : Std.HashSet (Address × Bytes32)) (y : Std.HashSet (Address × Hash32)) :
    ({ { t with storageReads := x } with codeReads := y } : TxObs) =
      { { t with codeReads := y } with storageReads := x } := rfl

private theorem commute_storageReads_createdAccounts (t : TxObs)
    (x : Std.HashSet (Address × Bytes32)) (y : Std.HashSet Address) :
    ({ { t with storageReads := x } with createdAccounts := y } : TxObs) =
      { { t with createdAccounts := y } with storageReads := x } := rfl

private theorem commute_codeReads_createdAccounts (t : TxObs)
    (x : Std.HashSet (Address × Hash32)) (y : Std.HashSet Address) :
    ({ { t with codeReads := x } with createdAccounts := y } : TxObs) =
      { { t with createdAccounts := y } with codeReads := x } := rfl

private theorem address_dictionary :
    (inferInstance : Hashable Address) = Address.instHashable := rfl

private theorem slot_dictionary :
    (inferInstance : Hashable Bytes32) = Bytes32.instHashable := rfl

private theorem code_dictionary (h : Hash32) :
    hash h = Hash32.tableHashReference h := Hash32.hash_eq_reference h

private theorem storage_pair_dictionary (x : Address × Bytes32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl

private theorem code_pair_dictionary (x : Address × Hash32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl

private theorem set_members {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (s t : Std.HashSet α) (key query : α) :
    (query ∈ s.insert key ↔ key = query ∨ query ∈ s) ∧
    (query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t) ∧
    (query ∈ (s.insert key).insert key ↔ query ∈ s.insert key) := by
  have hi : ∀ (u : Std.HashSet α), query ∈ u.insert key ↔ key = query ∨ query ∈ u := by
    intro u
    simpa only [beq_iff_eq] using
      (Std.HashSet.mem_insert (m := u) (k := key) (a := query))
  exact ⟨hi s, Std.HashSet.mem_union_iff, by simp only [hi, or_self_left]⟩

private theorem members_accountReads (t : TxObs) (s : Std.HashSet Address)
    (key query : Address) :
    (query ∈ t.accountReads.insert key ↔ key = query ∨ query ∈ t.accountReads) ∧
    (query ∈ t.accountReads ∪ s ↔ query ∈ t.accountReads ∨ query ∈ s) ∧
    (query ∈ (t.accountReads.insert key).insert key ↔ query ∈ t.accountReads.insert key) :=
  set_members t.accountReads s key query

private theorem members_storageReads (t : TxObs) (s : Std.HashSet (Address × Bytes32))
    (key query : Address × Bytes32) :
    (query ∈ t.storageReads.insert key ↔ key = query ∨ query ∈ t.storageReads) ∧
    (query ∈ t.storageReads ∪ s ↔ query ∈ t.storageReads ∨ query ∈ s) ∧
    (query ∈ (t.storageReads.insert key).insert key ↔ query ∈ t.storageReads.insert key) :=
  set_members t.storageReads s key query

private theorem members_codeReads (t : TxObs) (s : Std.HashSet (Address × Hash32))
    (key query : Address × Hash32) :
    (query ∈ t.codeReads.insert key ↔ key = query ∨ query ∈ t.codeReads) ∧
    (query ∈ t.codeReads ∪ s ↔ query ∈ t.codeReads ∨ query ∈ s) ∧
    (query ∈ (t.codeReads.insert key).insert key ↔ query ∈ t.codeReads.insert key) :=
  set_members t.codeReads s key query

private theorem members_createdAccounts (t : TxObs) (s : Std.HashSet Address)
    (key query : Address) :
    (query ∈ t.createdAccounts.insert key ↔ key = query ∨ query ∈ t.createdAccounts) ∧
    (query ∈ t.createdAccounts ∪ s ↔ query ∈ t.createdAccounts ∨ query ∈ s) ∧
    (query ∈ (t.createdAccounts.insert key).insert key ↔
      query ∈ t.createdAccounts.insert key) :=
  set_members t.createdAccounts s key query

private theorem unequal_preserved {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (s : Std.HashSet α) (key query : α) (h : key ≠ query) :
    query ∈ s.insert key ↔ query ∈ s := by
  rw [(set_members s s key query).1, or_iff_right h]

private theorem reconstructed_accounts (t : TxObs) (a : Address) :
    Address.ofNat a.toNat ∈ t.accountReads.insert a ∧
    Address.ofNat a.toNat ∈ t.createdAccounts.insert a := by
  rw [Address.ofNat_toNat]
  exact ⟨Std.HashSet.mem_insert_self, Std.HashSet.mem_insert_self⟩

private theorem reconstructed_storage (t : TxObs) (a : Address) (k : Bytes32) :
    (Address.ofNat a.toNat, FixedBytes.ofNat k.toNat) ∈ t.storageReads.insert (a, k) := by
  rw [Address.ofNat_toNat, FixedBytes.ofNat_toNat]
  exact Std.HashSet.mem_insert_self

private theorem reconstructed_code (t : TxObs) (a : Address) (h : Hash32) :
    (Address.ofNat a.toNat, Hash32.ofBytes32 h.toBytes32) ∈ t.codeReads.insert (a, h) := by
  rw [Address.ofNat_toNat, Hash32.ofBytes32_toBytes32]
  exact Std.HashSet.mem_insert_self

private theorem independent_accounts (t : TxObs) (s : Std.HashSet Address) :
    ({ t with createdAccounts := s } : TxObs).accountReads = t.accountReads ∧
    ({ t with accountReads := s } : TxObs).createdAccounts = t.createdAccounts := ⟨rfl, rfl⟩

end STFSpec.Conformance.State.TxObsCallerProofs
