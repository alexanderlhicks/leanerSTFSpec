/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Public node database clients

Library `EthConformance`. These symbolic callers use exported model, query and
lookup laws without unfolding Hash32, table storage or construction internals.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C12, §7.
-/

namespace STFSpec.Conformance.Commit.NodeDBCallerProofs

open STFSpec.Base STFSpec.Hash STFSpec.Commit

/-- The Id table can supply the decoder's separate authentication premise. -/
theorem decoder_authentication (entries : Array ByteArray) :
    NodeDB.Authentic keccak256 (NodeDB.build (m := Id) entries) :=
  NodeDB.authentic_build_id entries

/-- Any recovered raw entry is authenticated under the concrete Id interpretation. -/
theorem recovered_preimage (entries : Array ByteArray) (h : Hash32) (b : ByteArray)
    (found : (NodeDB.build (m := Id) entries).map[h]? = some b) : keccak256 b = h :=
  decoder_authentication entries h b found

/-- Arbitrary oracle answers are retained; no concrete-answer promise is introduced. -/
theorem singleton_answer {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entry : ByteArray) (answer : Hash32)
    (query : KeccakQuery.keccak (m := m) entry = pure answer) :
    NodeDB.build (m := m) #[entry] =
      pure ⟨({} : Std.HashMap Hash32 ByteArray).insert answer entry⟩ := by
  rw [NodeDB.build_singleton, query]
  simp only [pure_bind]

/-- Colliding concrete-model keys overwrite while preserving authenticity. -/
theorem model_last_write (H : ByteArray → Hash32) (db : NodeDB)
    (a b : ByteArray) (same : H a = H b) :
    (NodeDB.model H [a, b] db).map[H a]? = some b := by
  rw [NodeDB.lookup_model]
  simp only [List.foldl_cons, List.foldl_nil, same, ite_true]

/-- A final query after a successful prefix installs its answer and raw bytes. -/
theorem append_answer {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : Array ByteArray) (entry : ByteArray) (db : NodeDB) (answer : Hash32)
    (hprefix : NodeDB.build (m := m) entries = pure db)
    (query : KeccakQuery.keccak (m := m) entry = pure answer) :
    NodeDB.build (m := m) (entries.push entry) = pure ⟨db.map.insert answer entry⟩ := by
  rw [NodeDB.build_push, hprefix, query]
  simp only [pure_bind]

/-- Public model lookup preserves every key that differs from the appended key. -/
theorem model_other (H : ByteArray → Hash32) (db : NodeDB)
    (entry : ByteArray) (query : Hash32) (different : H entry ≠ query) :
    (NodeDB.model H [entry] db).map[query]? = db.map[query]? := by
  rw [NodeDB.lookup_model]
  simp only [List.foldl_cons, List.foldl_nil, ite_eq_right different]

/-- Byte-reconstructed keys recover the same stored value under public Base equality. -/
theorem reconstructed_lookup (entries : Array ByteArray) (h query : Hash32)
    (same : h.toBytes = query.toBytes) :
    (NodeDB.build (m := Id) entries).map[h]? =
      (NodeDB.build (m := Id) entries).map[query]? := by
  rw [Hash32.toBytes_inj.mp same]

/-- The ordered reference supplies concatenation without a generic authentication premise. -/
theorem ordered_split {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (a b : Array ByteArray) : NodeDB.build (m := m) (a ++ b) = (do
      let db ← NodeDB.build a
      NodeDB.buildReference b.toList db) := NodeDB.build_append a b

/-- Added state preserves the database result and the consumer's own state. -/
theorem state_forwarding {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : Array ByteArray) (state : σ) :
    (NodeDB.build (m := StateT σ m) entries).run state =
      (do let db ← NodeDB.build (m := m) entries; pure (db, state)) := by
  rw [NodeDB.build_eq_reference, NodeDB.build_eq_reference]
  exact NodeDB.run_buildReference_stateT entries.toList ⟨{}⟩ state

/-- Added exceptions forward the same underlying ordered computation. -/
theorem exception_forwarding {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (entries : Array ByteArray) :
    (NodeDB.build (m := ExceptT ε m) entries).run =
      (do let db ← NodeDB.build (m := m) entries; pure (.ok db : Except ε NodeDB)) := by
  rw [NodeDB.build_eq_reference, NodeDB.build_eq_reference]
  exact NodeDB.run_buildReference_exceptT entries.toList ⟨{}⟩

end STFSpec.Conformance.Commit.NodeDBCallerProofs
