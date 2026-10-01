/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec
import Std.Data.HashMap.Lemmas

/-!
# Raw witness node database

Library `EthCommit`. The database is constructed in input order and subsequently
shared read-only by consumers. No RLP interpretation occurs during construction.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C12, §§5–7.
-/

namespace STFSpec.Commit

open STFSpec.Base STFSpec.Hash

/-- Raw witness preimages indexed by oracle answers; authenticity is a separate predicate. -/
structure NodeDB where
  /-- Consumers share this table read-only after construction. -/
  map : Std.HashMap Hash32 ByteArray

namespace NodeDB

/-- Every stored preimage hashes to its key under the supplied interpretation (D5/F4). -/
def Authentic (H : ByteArray → Hash32) (db : NodeDB) : Prop :=
  ∀ h b, db.map[h]? = some b → H b = h

/-- Legible ordered List reference, optionally extending an existing table.
Each query occurs before its insertion; arbitrary equal answers retain the last value. -/
def buildReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (entries : List ByteArray) (db : NodeDB) : m NodeDB :=
  entries.foldlM (fun db entry => do
    let h ← KeccakQuery.keccak entry
    pure ⟨db.map.insert h entry⟩) db

/-- Build the raw node database by querying each entry exactly once, in input order.
EELS `src/ethereum/forks/amsterdam/witness_state.py:37–42` at the pin.
Empty and malformed RLP preimages are accepted; no constants or decoding are consulted. -/
def build {m : Type → Type} [Monad m] [KeccakQuery m]
    (entries : Array ByteArray) : m NodeDB :=
  entries.foldlM (fun db entry => do
    let h ← KeccakQuery.keccak entry
    pure ⟨db.map.insert h entry⟩) ⟨{}⟩

/-- The runtime Array fold equals the ordered List reference on every oracle monad. -/
theorem build_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (entries : Array ByteArray) :
    build (m := m) entries = buildReference entries.toList ⟨{}⟩ := by
  simp only [build, buildReference, ← Array.foldlM_toList]

/-- Empty construction returns the empty table without querying. -/
theorem build_empty {m : Type → Type} [Monad m] [KeccakQuery m] :
    build (m := m) #[] = pure ⟨{}⟩ := by
  rw [build_eq_reference]
  rfl

/-- Reference expansion exposes the query before insertion and the remaining input. -/
theorem buildReference_cons {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entry : ByteArray) (entries : List ByteArray) (db : NodeDB) :
    buildReference (m := m) (entry :: entries) db = (do
      let h ← KeccakQuery.keccak entry
      buildReference entries ⟨db.map.insert h entry⟩) := by
  simp only [buildReference, List.foldlM_cons, bind_assoc, pure_bind]

/-- A singleton uses its supplied oracle answer verbatim. -/
theorem build_singleton {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entry : ByteArray) : build (m := m) #[entry] = (do
      let h ← KeccakQuery.keccak entry
      pure ⟨({} : Std.HashMap Hash32 ByteArray).insert h entry⟩) := by
  rw [build_eq_reference]
  simp only [buildReference, List.foldlM_cons, List.foldlM_nil, bind_pure]

/-- Concatenation finishes the first input before extending its table with the second. -/
theorem build_append {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries more : Array ByteArray) : build (m := m) (entries ++ more) = (do
      let db ← build entries
      buildReference more.toList db) := by
  simp only [build_eq_reference, Array.toList_append, buildReference, List.foldlM_append]

/-- Appending one entry queries after the prefix and overwrites any equal answer. -/
theorem build_push {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : Array ByteArray) (entry : ByteArray) :
    build (m := m) (entries.push entry) = (do
      let db ← build entries
      let h ← KeccakQuery.keccak entry
      pure ⟨db.map.insert h entry⟩) := by
  simp only [build_eq_reference, Array.toList_push, buildReference, List.foldlM_append,
    List.foldlM_cons, List.foldlM_nil, bind_pure]

/-- Pure finite-map model under a chosen hash interpretation; the last equal key wins. -/
def model (H : ByteArray → Hash32) (entries : List ByteArray) (db : NodeDB) : NodeDB :=
  entries.foldl (fun db entry => ⟨db.map.insert (H entry) entry⟩) db

/-- Id construction agrees with the pure model using the concrete Keccak interpretation. -/
theorem build_id_model (entries : Array ByteArray) :
    build (m := Id) entries = model keccak256 entries.toList ⟨{}⟩ := by
  rw [build_eq_reference]
  simp only [buildReference, model, List.foldl_eq_foldlM]
  rfl

/-- Public lookup after insertion depends only on actual Hash32 equality. -/
theorem lookup_insert (db : NodeDB) (h query : Hash32) (entry : ByteArray) :
    (db.map.insert h entry)[query]? = if h = query then some entry else db.map[query]? := by
  simpa only [beq_iff_eq] using
    (Std.HashMap.getElem?_insert (m := db.map) (k := h) (a := query) (v := entry))

/-- The full model lookup is the last matching preimage, or the existing lookup.
No injectivity, distinct-support-hash or table-distribution premise is required. -/
theorem lookup_model (H : ByteArray → Hash32) (entries : List ByteArray)
    (db : NodeDB) (query : Hash32) :
    (model H entries db).map[query]? = entries.foldl
      (fun value entry => if H entry = query then some entry else value) db.map[query]? := by
  induction entries generalizing db with
  | nil => rfl
  | cons entry entries ih =>
    simp only [model, List.foldl_cons] at *
    rw [ih, lookup_insert]

/-- A correctly keyed insertion preserves authenticity, even when it overwrites a collision. -/
theorem authentic_insert (H : ByteArray → Hash32) (db : NodeDB)
    (hauth : Authentic H db) (entry : ByteArray) :
    Authentic H ⟨db.map.insert (H entry) entry⟩ := by
  intro h b hlookup
  rw [lookup_insert] at hlookup
  split at hlookup
  next heq => exact Option.some.inj hlookup ▸ heq
  next => exact hauth h b hlookup

/-- Ordered concrete-model extension preserves authenticity without a collision assumption. -/
theorem authentic_model (H : ByteArray → Hash32) (entries : List ByteArray)
    (db : NodeDB) (hauth : Authentic H db) : Authentic H (model H entries db) := by
  induction entries generalizing db with
  | nil => exact hauth
  | cons entry entries ih =>
    exact ih ⟨db.map.insert (H entry) entry⟩ (authentic_insert H db hauth entry)

/-- Actual Id construction establishes the concrete C12 authenticity predicate. -/
theorem authentic_build_id (entries : Array ByteArray) :
    Authentic keccak256 (build (m := Id) entries) := by
  rw [build_id_model]
  apply authentic_model
  intro h b hlookup
  simp only [Std.HashMap.getElem?_empty] at hlookup
  contradiction

/-- Complete Id lookup exposes the input-order last-write model to consumers. -/
theorem lookup_build_id (entries : Array ByteArray) (query : Hash32) :
    (build (m := Id) entries).map[query]? = entries.toList.foldl
      (fun value entry => if keccak256 entry = query then some entry else value) none := by
  rw [build_id_model, lookup_model]
  simp only [Std.HashMap.getElem?_empty]

/-- Building through an added state layer forwards the oracle and preserves that state. -/
theorem run_buildReference_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : List ByteArray) (db : NodeDB) (s : σ) :
    (buildReference (m := StateT σ m) entries db).run s =
      (do let result ← buildReference (m := m) entries db; pure (result, s)) := by
  induction entries generalizing db with
  | nil => simp [buildReference]
  | cons entry entries ih =>
    simp only [buildReference_cons, KeccakQuery.keccak_stateT]
    simp [ih]

/-- Building through an added exception layer forwards the underlying computation. -/
theorem run_buildReference_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : List ByteArray) (db : NodeDB) :
    (buildReference (m := ExceptT ε m) entries db).run =
      (do let result ← buildReference (m := m) entries db;
          pure (.ok result : Except ε NodeDB)) := by
  induction entries generalizing db with
  | nil => simp [buildReference]
  | cons entry entries ih =>
    simp only [buildReference_cons, KeccakQuery.keccak_exceptT,
      ExceptT.run_bind, ExceptT.run_lift, bind_map_left, ih]
    simp only [bind_assoc]

/-- A failing next query prevents both its insertion and every remaining query. -/
theorem run_buildReference_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (entry : ByteArray) (entries : List ByteArray) (db : NodeDB) (error : ε)
    (hquery : KeccakQuery.keccak (m := ExceptT ε m) entry =
      ExceptT.mk (pure (.error error))) :
    (buildReference (m := ExceptT ε m) (entry :: entries) db).run =
      pure (.error error) := by
  rw [buildReference_cons, hquery]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

end NodeDB
end STFSpec.Commit
