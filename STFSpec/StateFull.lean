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

open STFSpec.Base STFSpec.State STFSpec.StateCommit STFSpec.Hash

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

/-- Set the selected account and package the supplied structural proof (FS6).
Storage and the authentic code table retain their complete contents.
EELS `src/ethereum/state_mpt.py:174–184` at the pin. -/
def FullState.setAccount (s : FullState) (a : Address) (acc : Option Account)
    (h : MathState.WF (s.σ.setAccount a acc)) : FullState :=
  FullState.ofMath (s.σ.setAccount a acc) h s.codeAuthentic

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

private def insertCode (σ : MathState) (digest : Hash32) (code : ByteArray) : MathState :=
  { σ with code := σ.code.insert digest code }

private theorem insertCode_wf (σ : MathState) (digest : Hash32) (code : ByteArray)
    (wf : MathState.WF σ) : MathState.WF (insertCode σ digest code) := wf

private theorem insertCode_authentic (σ : MathState) (digest : Hash32) (code : ByteArray)
    (authentic : CodeAuthentic σ)
    (proof : Id.run (KeccakQuery.keccak (m := Id) code) = digest) :
    CodeAuthentic (insertCode σ digest code) := by
  intro queried bytes stored
  change (σ.code.insert digest code)[queried]? = some bytes at stored
  simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] at stored
  by_cases equal : digest = queried
  · simp only [ite_eq_left equal] at stored
    have exactBytes := Option.some.inj stored
    subst bytes
    exact proof.trans equal
  · simp only [ite_eq_right equal] at stored
    exact authentic queried bytes stored

/-- Bind the certified code digest. Keep the original state at the supplied
reserved hash and install the full bytes at any certified nonreserved digest.
EELS `src/ethereum/state_mpt.py:164–171` at the pin. -/
def FullState.storeCode {m : Type → Type} [Monad m] [KeccakQuery m]
    (s : FullState) (consts : HashConsts) (code : ByteArray)
    (answer : m {h : Hash32 //
      h ≠ consts.emptyCodeHash → Id.run (KeccakQuery.keccak (m := Id) code) = h})
    (observes : Subtype.val <$> answer = KeccakQuery.keccak (m := m) code) :
    m (Hash32 × FullState) := do
  let _ := observes
  let digest ← answer
  if skip : digest.val = consts.emptyCodeHash then
    pure (digest.val, s)
  else
    pure (digest.val, FullState.ofMath (insertCode s.σ digest.val code)
      (insertCode_wf s.σ digest.val code s.wf)
      (insertCode_authentic s.σ digest.val code s.codeAuthentic (digest.property skip)))

/-- Project the complete action to its digest and raw state at the supplied query. -/
theorem FullState.storeCode_project {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (s : FullState) (consts : HashConsts) (code : ByteArray)
    (answer : m {h : Hash32 //
      h ≠ consts.emptyCodeHash → Id.run (KeccakQuery.keccak (m := Id) code) = h})
    (observes : Subtype.val <$> answer = KeccakQuery.keccak (m := m) code) :
    (fun result : Hash32 × FullState ↦ (result.1, result.2.σ)) <$>
        s.storeCode consts code answer observes =
      (do
        let h ← KeccakQuery.keccak (m := m) code
        pure (h, if h = consts.emptyCodeHash then s.σ
          else {s.σ with code := s.σ.code.insert h code})) := by
  dsimp only [FullState.storeCode]
  rw [← observes]
  simp only [map_bind, bind_map_left]
  apply congrArg (fun next : {h : Hash32 // h ≠ consts.emptyCodeHash →
    Id.run (KeccakQuery.keccak (m := Id) code) = h} → m (Hash32 × MathState) ↦ answer >>= next)
  funext digest
  by_cases skip : digest.val = consts.emptyCodeHash <;>
    simp only [skip, dite_true, dite_false, ite_true, ite_false, map_pure,
      FullState.ofMath, insertCode]

end STFSpec.StateFull
