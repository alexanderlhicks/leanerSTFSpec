/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.State.StateError
import STFSpec.State.Structural

/-!
# STFSpec.StateFull

The full-state carrier stores a mathematical state with the supplied structural
well-formedness and code authenticity proofs.

Library `EthStateFull`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3).
Spec guidance: `STFSpec/informal/modules/EthStateFull.md`.
-/

namespace STFSpec.StateFull

open STFSpec.Base STFSpec.State STFSpec.StateCommit

/-- Mathematical carrier for the account, storage and code maps of EELS
`src/ethereum/state_mpt.py:34–47`, with the supplied invariant proofs. -/
structure FullState where
  /-- The complete supplied mathematical state. -/
  σ : MathState
  /-- Structural well-formedness of the supplied state. -/
  wf : MathState.WF σ
  /-- Authenticity of every entry in the supplied raw code table. -/
  codeAuthentic : CodeAuthentic σ

/-- Package the supplied state and its two invariant proofs (FS1). -/
def FullState.ofMath (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
    FullState :=
  {
    σ := σ
    wf := hwf
    codeAuthentic := hc
  }

private def storageWrite (a : Address) (k : Bytes32) (v : U256) : BlockDiff where
  accountChanges := ∅
  accountOrder := []
  storageChanges := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v)
  storageAddressOrder := []
  storageSlotOrder := ∅
  codeChanges := ∅
  storageClears := ∅

private theorem storageWrite_structural (σ : MathState) (a : Address) (k : Bytes32)
    (v : U256) (present : σ.account? a ≠ none) :
    BlockDiff.StructuralPremises σ (storageWrite a k v) := by
  refine ⟨?_, ?_⟩
  · intro address deletion
    simp [storageWrite] at deletion
  · intro address touched
    have same : address = a := by
      by_cases equal : address = a
      · exact equal
      · simp [storageWrite, Ne.symm equal] at touched
    subst address
    simpa [MathState.apply_account?_eq, storageWrite] using present

private theorem storageWrite_code (σ : MathState) (a : Address) (k : Bytes32) (v : U256) :
    (σ.apply (storageWrite a k v)).code = σ.code :=
  MathState.apply_code_of_no_changes _ _ rfl

private def writePresentStorage (s : FullState) (a : Address) (k : Bytes32) (v : U256)
    (present : s.σ.account? a ≠ none) : FullState :=
  FullState.ofMath (s.σ.apply (storageWrite a k v))
    (MathState.wf_apply_of_structuralPremises _ _ s.wf (storageWrite_structural _ _ _ _ present))
    (by
      intro hash code found
      rw [storageWrite_code] at found
      exact s.codeAuthentic hash code found)

/-- Check that the account exists, then write the slot or erase it at zero.
Remove the touched storage map when it is empty. The absence error carries no
state. EELS `src/ethereum/state_mpt.py:187–206`. -/
def FullState.setStorage (s : FullState) (a : Address) (k : Bytes32) (v : U256) :
    Except StateError FullState :=
  if missing : s.σ.account? a = none then .error .storageOnMissingAccount
  else .ok (writePresentStorage s a k v missing)

private theorem storageWrite_option (σ : MathState) (a : Address) (k : Bytes32) (v : U256) :
    (σ.apply (storageWrite a k v)).storage[a]? =
      let old := (σ.storage[a]?).getD ∅
      let changed := if v = U256.zero then old.erase k else old.insert k v
      if changed.isEmpty then none else some changed := by
  have single : ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v).toList = [(k, v)] := rfl
  rw [MathState.apply_storage_lookup]
  simp [storageWrite, Std.ExtTreeMap.foldl_eq_foldl_toList, single]

private theorem setStorage_fields (s : FullState) (a : Address) (k : Bytes32) (v : U256) :
    (s.setStorage a k v).map FullState.σ =
      if s.σ.account? a = none then .error .storageOnMissingAccount
      else .ok (s.σ.apply (storageWrite a k v)) := by
  by_cases missing : s.σ.account? a = none
  · simp only [FullState.setStorage, dite_eq_left missing, ite_eq_left missing, Except.map]
  · simp only [FullState.setStorage, dite_eq_right missing, ite_eq_right missing, Except.map,
      writePresentStorage, FullState.ofMath]

private theorem setStorage_retains (s next : FullState) (a : Address) (k : Bytes32) (v : U256)
    (success : s.setStorage a k v = .ok next) :
    s.σ.account? a ≠ none ∧ next.σ.accounts = s.σ.accounts ∧ next.σ.code = s.σ.code ∧
      (∀ b, b ≠ a → next.σ.storage[b]? = s.σ.storage[b]?) ∧
      next.σ.storage[a]? =
        let old := (s.σ.storage[a]?).getD ∅
        let changed := if v = U256.zero then old.erase k else old.insert k v
        if changed.isEmpty then none else some changed := by
  have result := setStorage_fields s a k v
  rw [success] at result
  change Except.ok next.σ = _ at result
  by_cases missing : s.σ.account? a = none
  · rw [ite_eq_left missing] at result
    cases result
  · rw [ite_eq_right missing] at result
    have shape := Except.ok.inj result
    rw [shape]
    refine ⟨missing, MathState.apply_accounts_of_no_changes _ _ rfl, storageWrite_code _ _ _ _,
      ?_, storageWrite_option _ _ _ _⟩
    intro b different
    apply MathState.apply_storage_of_untouched
    · simp [storageWrite, Ne.symm different]
    · simp [storageWrite]

end STFSpec.StateFull
