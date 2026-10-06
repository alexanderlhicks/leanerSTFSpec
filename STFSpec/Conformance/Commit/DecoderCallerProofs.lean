/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Generic decoder public-import clients

Library `EthConformance`. These ordinary private clients use only the five public
decoder declarations. Plain Monad equations retain bind shape; simplification of
the wrapper requires LawfulMonad. Arbitrary full roots, supplied flags, typed
errors and underlying effects remain visible.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C13–C17/Q55.
-/

namespace STFSpec.Conformance.Commit.DecoderCallerProofs
open STFSpec.Base STFSpec.Hash STFSpec.Commit

private theorem empty_plain {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) :
    decodeRoot (m := m) emptyRoot db emptyRoot = pure (.ok none) :=
  decodeRoot_empty emptyRoot db

private theorem missing_plain {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (hne : r ≠ emptyRoot)
    (hmissing : db.map[r]? = none) :
    decodeRoot (m := m) emptyRoot db r = pure (.error (.missingRoot r)) :=
  decodeRoot_missing emptyRoot db r hne hmissing

private theorem wrapper_plain {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured = (do
      let result ← decodeRoot emptyRoot db r
      pure (result.map (fun root => IncrementalMPT.mk secured root))) :=
  decodeWitnessToMpt_eq emptyRoot db r secured

private theorem wrapper_full_root {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) (root : Ref)
    (hroot : decodeRoot (m := m) emptyRoot db r = pure (.ok root)) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured =
      pure (.ok (IncrementalMPT.mk secured root)) := by
  rw [decodeWitnessToMpt_eq, hroot]
  simp only [pure_bind, Except.map]

private theorem wrapper_typed_error {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) (error : TrieError)
    (hroot : decodeRoot (m := m) emptyRoot db r = pure (.error error)) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured = pure (.error error) := by
  rw [decodeWitnessToMpt_eq, hroot]
  simp only [pure_bind, Except.map]

private theorem wrapper_underlying_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) (error : ε)
    (hroot : decodeRoot (m := ExceptT ε m) emptyRoot db r =
      ExceptT.mk (pure (.error error))) :
    (decodeWitnessToMpt (m := ExceptT ε m) emptyRoot db r secured).run =
      pure (.error error) := by
  rw [decodeWitnessToMpt_eq, hroot]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

private theorem empty_added_state {m : Type → Type} {σ : Type}
    [Monad m] [KeccakQuery m] (emptyRoot : Hash32) (db : NodeDB) (state : σ) :
    (decodeRoot (m := StateT σ m) emptyRoot db emptyRoot).run state =
      pure (.ok none, state) := by
  rw [decodeRoot_empty]
  rfl

private theorem empty_added_exception {m : Type → Type} {ε : Type}
    [Monad m] [KeccakQuery m] (emptyRoot : Hash32) (db : NodeDB) :
    (decodeRoot (m := ExceptT ε m) emptyRoot db emptyRoot).run =
      pure (.ok (.ok none)) := by
  rw [decodeRoot_empty]
  rfl

end STFSpec.Conformance.Commit.DecoderCallerProofs
