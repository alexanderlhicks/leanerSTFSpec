/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Generic decoder public-import clients

Library `EthConformance`. These ordinary private clients use only the public
decoder declarations and the public Q90 secured-path check. Plain Monad equations
retain bind shape; simplification of the wrapper requires LawfulMonad. Arbitrary
full roots, supplied flags, typed errors and underlying effects remain visible.
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
      pure (result.bind (fun root =>
        if secured && !securedPathsOk root securedTrieKeyNibbles then
          .error (.malformed .securedPathLength)
        else .ok (IncrementalMPT.mk secured root)))) :=
  decodeWitnessToMpt_eq emptyRoot db r secured

private theorem wrapper_full_root {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) (root : Ref)
    (hroot : decodeRoot (m := m) emptyRoot db r = pure (.ok root))
    (hpaths : secured = false ∨ securedPathsOk root securedTrieKeyNibbles = true) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured =
      pure (.ok (IncrementalMPT.mk secured root)) := by
  rw [decodeWitnessToMpt_eq, hroot]
  rcases hpaths with h | h <;>
    simp only [pure_bind, Except.bind, h, Bool.false_and, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]

private theorem wrapper_secured_path_failure {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (root : Ref)
    (hroot : decodeRoot (m := m) emptyRoot db r = pure (.ok root))
    (hpaths : securedPathsOk root securedTrieKeyNibbles = false) :
    decodeWitnessToMpt (m := m) emptyRoot db r true =
      pure (.error (.malformed .securedPathLength)) := by
  rw [decodeWitnessToMpt_eq, hroot]
  simp only [pure_bind, Except.bind, hpaths, Bool.not_false, Bool.and_self, ↓reduceIte]

private theorem wrapper_typed_error {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot r : Hash32) (db : NodeDB) (secured : Bool) (error : TrieError)
    (hroot : decodeRoot (m := m) emptyRoot db r = pure (.error error)) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured = pure (.error error) := by
  rw [decodeWitnessToMpt_eq, hroot]
  simp only [pure_bind, Except.bind]

/- Q90 shape clients through the public equations alone. -/
private theorem secured_leaf_exact (path : Nibbles) (value : ByteArray) (enc : Enc) :
    securedPathsOk (some (.leaf path value enc)) securedTrieKeyNibbles =
      (path.size == 64) := by
  rw [securedPathsOk_leaf]
  rfl

private theorem secured_stub_skipped (h : Hash32) (remaining : Nat) :
    securedPathsOk (some (.hashed h)) remaining = true :=
  securedPathsOk_hashed h remaining

private theorem secured_branch_exhausted (children : Array Ref) (value : ByteArray)
    (enc : Enc) : securedPathsOk (some (.branch children value enc)) 0 = false := by
  rw [securedPathsOk_branch]
  rfl

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
