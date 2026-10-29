/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# Observation-key table-support public clients

Library `EthConformance`: private clients use complete public Base observers and
ordinary model equations, plus public Std membership and lookup laws.
No hash inequality, private fixed-byte field or bucket layout is a premise.

Spec guidance: `STFSpec/informal/modules/EthBase.md` (DECISIONS Q84).
-/

namespace STFSpec.Conformance.Base.ObservationHashCallerProofs

open STFSpec.Base

private theorem address_execution_model (x : Address) :
    Address.tableHash x = Address.tableHashReference x :=
  Address.tableHash_eq_reference x

private theorem address_canonical_model (x : Address) :
    hash x = Address.tableHashReference x := Address.hash_eq_reference x

private theorem address_numeric_congruence (x y : Address) (h : x.toNat = y.toNat) :
    hash x = hash y := congrArg hash (Address.toNat_inj.mp h)

private theorem address_byte_congruence (x y : Address) (h : x.toBytes = y.toBytes) :
    hash x = hash y := congrArg hash (Address.toBytes_inj.mp h)

private theorem address_reconstruct_hash (x : Address) :
    hash (Address.ofNat x.toNat : Address) = hash x := by
  rw [Address.ofNat_toNat]

private theorem slot_execution_model (x : Bytes32) :
    Bytes32.tableHash x = Bytes32.tableHashReference x :=
  Bytes32.tableHash_eq_reference x

private theorem slot_canonical_model (x : Bytes32) :
    hash x = Bytes32.tableHashReference x := Bytes32.hash_eq_reference x

private theorem slot_numeric_congruence (x y : Bytes32) (h : x.toNat = y.toNat) :
    hash x = hash y := congrArg hash (FixedBytes.toNat_inj.mp h)

private theorem slot_byte_congruence (x y : Bytes32) (h : x.toBytes = y.toBytes) :
    hash x = hash y := congrArg hash (FixedBytes.toBytes_inj.mp h)

private theorem slot_reconstruct_hash (x : Bytes32) :
    hash (FixedBytes.ofNat x.toNat : Bytes32) = hash x := by
  rw [FixedBytes.ofNat_toNat]

private theorem address_dictionary :
    (inferInstance : Hashable Address) = Address.instHashable := rfl

private theorem slot_dictionary :
    (inferInstance : Hashable (FixedBytes 32)) = Bytes32.instHashable := rfl

private theorem storage_pair_hash (x : Address × Bytes32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl

private theorem code_pair_hash (x : Address × Hash32) :
    hash x = mixHash (hash x.1) (hash x.2) := rfl

section StdClients

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α]

private theorem member_insert (s : Std.HashSet α) (key query : α) :
    query ∈ s.insert key ↔ key = query ∨ query ∈ s := by
  simpa only [beq_iff_eq] using (Std.HashSet.mem_insert (m := s) (k := key) (a := query))

private theorem member_union (s t : Std.HashSet α) (query : α) :
    query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t := Std.HashSet.mem_union_iff

private theorem duplicate_membership (s : Std.HashSet α) (key query : α) :
    query ∈ (s.insert key).insert key ↔ query ∈ s.insert key := by
  simp only [member_insert, or_self_left]

private theorem unequal_member (s : Std.HashSet α) (key query : α) (h : key ≠ query) :
    query ∈ s.insert key ↔ query ∈ s := by
  rw [member_insert, or_iff_right h]

private theorem lookup_insert [DecidableEq α] {β : Type} (db : Std.HashMap α β)
    (key query : α) (value : β) :
    (db.insert key value)[query]? = if key = query then some value else db[query]? := by
  simpa only [beq_iff_eq] using
    (Std.HashMap.getElem?_insert (m := db) (k := key) (a := query) (v := value))

private theorem lookup_overwrite {β : Type} (db : Std.HashMap α β)
    (key : α) (value latest : β) :
    ((db.insert key value).insert key latest)[key]? = some latest :=
  Std.HashMap.getElem?_insert_self

private theorem lookup_unequal [DecidableEq α] {β : Type} (db : Std.HashMap α β)
    (key query : α) (value : β) (h : key ≠ query) :
    (db.insert key value)[query]? = db[query]? := by
  rw [lookup_insert, ite_eq_right h]

end StdClients

private theorem account_sets (s t : Std.HashSet (Address)) (key query : Address)
    (h : key ≠ query) :
    (query ∈ s.insert key ↔ key = query ∨ query ∈ s) ∧
    (query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t) ∧
    (query ∈ (s.insert key).insert key ↔ query ∈ s.insert key) ∧
    (query ∈ s.insert key ↔ query ∈ s) :=
  ⟨member_insert s key query, member_union s t query,
    duplicate_membership s key query, unequal_member s key query h⟩

private theorem account_maps {β : Type} (db : Std.HashMap (Address) β)
    (key query : Address) (value latest : β) (h : key ≠ query) :
    ((db.insert key value)[query]? = if key = query then some value else db[query]?) ∧
    (((db.insert key value).insert key latest)[key]? = some latest) ∧
    ((db.insert key value)[query]? = db[query]?) :=
  ⟨lookup_insert db key query value, lookup_overwrite db key value latest,
    lookup_unequal db key query value h⟩

private theorem storage_sets (s t : Std.HashSet (Address × Bytes32)) (key query : Address × Bytes32)
    (h : key ≠ query) :
    (query ∈ s.insert key ↔ key = query ∨ query ∈ s) ∧
    (query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t) ∧
    (query ∈ (s.insert key).insert key ↔ query ∈ s.insert key) ∧
    (query ∈ s.insert key ↔ query ∈ s) :=
  ⟨member_insert s key query, member_union s t query,
    duplicate_membership s key query, unequal_member s key query h⟩

private theorem storage_maps {β : Type} (db : Std.HashMap (Address × Bytes32) β)
    (key query : Address × Bytes32) (value latest : β) (h : key ≠ query) :
    ((db.insert key value)[query]? = if key = query then some value else db[query]?) ∧
    (((db.insert key value).insert key latest)[key]? = some latest) ∧
    ((db.insert key value)[query]? = db[query]?) :=
  ⟨lookup_insert db key query value, lookup_overwrite db key value latest,
    lookup_unequal db key query value h⟩

private theorem code_sets (s t : Std.HashSet (Address × Hash32)) (key query : Address × Hash32)
    (h : key ≠ query) :
    (query ∈ s.insert key ↔ key = query ∨ query ∈ s) ∧
    (query ∈ s ∪ t ↔ query ∈ s ∨ query ∈ t) ∧
    (query ∈ (s.insert key).insert key ↔ query ∈ s.insert key) ∧
    (query ∈ s.insert key ↔ query ∈ s) :=
  ⟨member_insert s key query, member_union s t query,
    duplicate_membership s key query, unequal_member s key query h⟩

private theorem code_maps {β : Type} (db : Std.HashMap (Address × Hash32) β)
    (key query : Address × Hash32) (value latest : β) (h : key ≠ query) :
    ((db.insert key value)[query]? = if key = query then some value else db[query]?) ∧
    (((db.insert key value).insert key latest)[key]? = some latest) ∧
    ((db.insert key value)[query]? = db[query]?) :=
  ⟨lookup_insert db key query value, lookup_overwrite db key value latest,
    lookup_unequal db key query value h⟩

private theorem account_equal_bytes (s : Std.HashSet Address) (key query : Address)
    (h : key.toBytes = query.toBytes) : query ∈ s.insert key := by
  rw [Address.toBytes_inj.mp h]
  exact Std.HashSet.mem_insert_self

private theorem storage_equal_models (s : Std.HashSet (Address × Bytes32))
    (key query : Address × Bytes32)
    (ha : key.1.toNat = query.1.toNat) (hs : key.2.toBytes = query.2.toBytes) :
    query ∈ s.insert key := by
  have hk : key = query := Prod.ext (Address.toNat_inj.mp ha) (FixedBytes.toBytes_inj.mp hs)
  rw [hk]
  exact Std.HashSet.mem_insert_self

private theorem code_equal_models (s : Std.HashSet (Address × Hash32))
    (key query : Address × Hash32)
    (ha : key.1.toBytes = query.1.toBytes) (hh : key.2.toNat = query.2.toNat) :
    query ∈ s.insert key := by
  have hk : key = query := Prod.ext (Address.toBytes_inj.mp ha) (Hash32.toNat_inj.mp hh)
  rw [hk]
  exact Std.HashSet.mem_insert_self

end STFSpec.Conformance.Base.ObservationHashCallerProofs
