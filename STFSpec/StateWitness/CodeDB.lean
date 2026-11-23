/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.NodeDB

/-!
# Witness code database

Library `EthStateWitness`. The database indexes raw witness bytecode by the oracle's
answers. Spec guidance: `STFSpec/informal/modules/EthStateWitness.md` W1, §§5–7.
-/

namespace STFSpec.StateWitness

open STFSpec.Base STFSpec.Hash

/-- Witness bytecode indexed by hash. -/
structure CodeDB where
  /-- Consumers share this table read-only after construction. -/
  map : Std.HashMap Hash32 ByteArray

namespace CodeDB

/-- Every stored byte string hashes to its key under the supplied interpretation (F4). -/
def Authentic (H : ByteArray → Hash32) (db : CodeDB) : Prop :=
  ∀ h code, db.map[h]? = some code → H code = h

private def insertCode {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : CodeDB) (code : ByteArray) : m CodeDB := do
  let hash ← KeccakQuery.keccak code
  pure ⟨db.map.insert hash code⟩

/-- Query each complete byte string once in input order. The last equal answer wins.
Implements `src/ethereum/forks/amsterdam/witness_state.py:33–35` at the pin. -/
def build {m : Type → Type} [Monad m] [KeccakQuery m]
    (codes : Array ByteArray) : m CodeDB :=
  codes.foldlM insertCode ⟨{}⟩

private def buildReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (codes : List ByteArray) (db : CodeDB) : m CodeDB :=
  codes.foldlM insertCode db

private theorem build_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (codes : Array ByteArray) : build (m := m) codes = buildReference codes.toList ⟨{}⟩ := by
  simp only [build, buildReference, ← Array.foldlM_toList]

private theorem reference_id_map_eq_model (codes : List ByteArray) (db : CodeDB) :
    (buildReference (m := Id) codes db).map =
      (Commit.NodeDB.model keccak256 codes ⟨db.map⟩).map := by
  induction codes generalizing db with
  | nil => rfl
  | cons code codes ih =>
    change (buildReference (m := Id) codes ⟨db.map.insert (keccak256 code) code⟩).map =
      (Commit.NodeDB.model keccak256 codes ⟨db.map.insert (keccak256 code) code⟩).map
    exact ih ⟨db.map.insert (keccak256 code) code⟩

private theorem authentic_build_id (codes : Array ByteArray) :
    Authentic keccak256 (build (m := Id) codes) := by
  rw [build_eq_reference]
  intro hash code found
  rw [reference_id_map_eq_model] at found
  have empty : Commit.NodeDB.Authentic keccak256 ⟨{}⟩ := by
    intro key entry lookup
    simp only [Std.HashMap.getElem?_empty] at lookup
    contradiction
  exact Commit.NodeDB.authentic_model keccak256 codes.toList ⟨{}⟩ empty hash code found

private theorem lookup_build_id (codes : Array ByteArray) (key : Hash32) :
    (build (m := Id) codes).map[key]? = codes.toList.foldl
      (fun previous code ↦ if keccak256 code = key then some code else previous) none := by
  rw [build_eq_reference, reference_id_map_eq_model, Commit.NodeDB.lookup_model,
    Std.HashMap.getElem?_empty]

end CodeDB
end STFSpec.StateWitness
