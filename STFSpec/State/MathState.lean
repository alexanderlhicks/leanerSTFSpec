/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import Std.Data.ExtTreeMap

/-!
# Raw mathematical state and defaulted observers

Library `EthState`: three finite maps with total observers and a separate structural `WF`.
Raw states retain zero slots, empty inner maps, orphan storage and hidden reserved code.
Code authenticity, completeness, providers, mutation and commitments are separate contracts.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State

open Base

/-- Raw finite state model for the account, storage and code lookup contracts. -/
structure MathState where
  /-- Present accounts, including present empty accounts. -/
  accounts : Std.ExtTreeMap Address Account
  /-- Raw per-address slot maps, without normalization. -/
  storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  /-- Raw code bytes, including entries hidden by the supplied reserved hash. -/
  code : Std.ExtTreeMap Hash32 ByteArray

namespace MathState

/-- Construction preserves the account map. -/
theorem accounts_mk (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).accounts = accounts := rfl

/-- Construction preserves the entire nested storage map. -/
theorem storage_mk (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).storage = storage := rfl

/-- Construction preserves the entire raw code map. -/
theorem code_mk (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).code = code := rfl

/-- Reconstruction from all three raw fields returns the state. -/
theorem eta (σ : MathState) : MathState.mk σ.accounts σ.storage σ.code = σ := by
  cases σ
  rfl

/-- Equality of all raw fields determines the state. -/
theorem ext {σ τ : MathState} (ha : σ.accounts = τ.accounts)
    (hs : σ.storage = τ.storage) (hc : σ.code = τ.code) : σ = τ := by
  cases σ
  cases τ
  cases ha
  cases hs
  cases hc
  rfl

/-- Raw lookups determine the state, retaining whole optional inner maps and all code hashes. -/
theorem ext_lookup {σ τ : MathState}
    (ha : ∀ a : Address, σ.accounts[a]? = τ.accounts[a]?)
    (hs : ∀ a : Address, σ.storage[a]? = τ.storage[a]?)
    (hc : ∀ h : Hash32, σ.code[h]? = τ.code[h]?) : σ = τ :=
  ext (Std.ExtTreeMap.ext_getElem? ha) (Std.ExtTreeMap.ext_getElem? hs)
    (Std.ExtTreeMap.ext_getElem? hc)

/-- Optional account lookup; EELS `src/ethereum/state_mpt.py:59–66`. -/
def account? (σ : MathState) (a : Address) : Option Account := σ.accounts[a]?

/-- Storage lookup defaults either missing layer to zero;
EELS `src/ethereum/state_mpt.py:67–80`. -/
def storageAt (σ : MathState) (a : Address) (k : Bytes32) : U256 :=
  ((σ.storage[a]?).bind (fun slots ↦ slots[k]?)).getD U256.zero

section

variable (σ : MathState) (consts : HashConsts)
local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash

/-- Mathematical optional code lookup with the caller's reserved-hash bypass;
EELS `src/ethereum/state_mpt.py:49–57` and `src/ethereum/forks/amsterdam/witness_state.py:205–213`.
The mathematical `none` is distinct from the provider's missing-code error. -/
def code? (h : Hash32) : Option ByteArray :=
  if h = EMPTY_CODE_HASH then some ByteArray.empty else σ.code[h]?

end

/-- Account observation is exactly the raw optional lookup. -/
theorem account?_eq_lookup (σ : MathState) (a : Address) :
    σ.account? a = σ.accounts[a]? := rfl

/-- Storage observation is exactly the two optional lookups and zero default. -/
theorem storageAt_eq_lookup (σ : MathState) (a : Address) (k : Bytes32) :
    σ.storageAt a k =
      ((σ.storage[a]?).bind (fun slots ↦ slots[k]?)).getD U256.zero := rfl

/-- Absent address storage returns zero. -/
theorem storageAt_of_storage_none (σ : MathState) (a : Address) (k : Bytes32)
    (hs : σ.storage[a]? = none) : σ.storageAt a k = U256.zero := by
  simp [storageAt, hs]

/-- An absent slot in a present raw inner map returns zero. -/
theorem storageAt_of_slot_none (σ : MathState) (a : Address) (k : Bytes32)
    (slots : Std.ExtTreeMap Bytes32 U256) (hs : σ.storage[a]? = some slots)
    (hk : slots[k]? = none) : σ.storageAt a k = U256.zero := by
  simp [storageAt, hs, hk]

/-- A present raw slot returns its exact value, including zero. -/
theorem storageAt_of_slot_some (σ : MathState) (a : Address) (k : Bytes32)
    (slots : Std.ExtTreeMap Bytes32 U256) (v : U256) (hs : σ.storage[a]? = some slots)
    (hk : slots[k]? = some v) : σ.storageAt a k = v := by
  simp [storageAt, hs, hk]

/-- The supplied reserved hash always returns empty bytes. -/
theorem code?_empty (σ : MathState) (consts : HashConsts) :
    σ.code? consts consts.emptyCodeHash = some ByteArray.empty := by
  simp [code?]

/-- Every other hash returns its raw optional code lookup. -/
theorem code?_of_ne (σ : MathState) (consts : HashConsts) (h : Hash32)
    (hh : h ≠ consts.emptyCodeHash) : σ.code? consts h = σ.code[h]? := by
  simp [code?, hh]

/-- Only the supplied empty-code hash field affects the observer. -/
theorem code?_congr_consts (σ : MathState) (consts : HashConsts) (h : Hash32)
    (other : HashConsts) (hc : consts.emptyCodeHash = other.emptyCodeHash) :
    σ.code? consts h = σ.code? other h := by
  simp only [code?, hc]

/-- Structural storage invariant only: nonzero slots, nonempty inners and present accounts. -/
def WF (σ : MathState) : Prop :=
  (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
    σ.storage[a]? = some slots →
    ∀ (k : Bytes32) (v : U256), slots[k]? = some v → v ≠ U256.zero) ∧
  (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
    σ.storage[a]? = some slots → slots.isEmpty = false) ∧
  (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
    σ.storage[a]? = some slots → σ.accounts[a]?.isSome = true)

/-- `WF` is exactly its three structural clauses, with no code or account-value condition. -/
theorem wf_iff (σ : MathState) : WF σ ↔
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots →
      ∀ (k : Bytes32) (v : U256), slots[k]? = some v → v ≠ U256.zero) ∧
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots → slots.isEmpty = false) ∧
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots → σ.accounts[a]?.isSome = true) := Iff.rfl

/-- Three empty raw maps are structurally well formed. -/
theorem wf_empty : WF (MathState.mk ∅ ∅ ∅) := by
  simp [WF]

/-- Every stored value in a well-formed state is nonzero. -/
theorem wf_storage_value_ne_zero (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (k : Bytes32) (v : U256)
    (hw : WF σ) (hs : σ.storage[a]? = some slots) (hk : slots[k]? = some v) :
    v ≠ U256.zero := hw.1 a slots hs k v hk

/-- Every stored inner map in a well-formed state is nonempty. -/
theorem wf_storage_nonempty (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (hw : WF σ) (hs : σ.storage[a]? = some slots) :
    slots.isEmpty = false := hw.2.1 a slots hs

/-- Every storage address in a well-formed state has an account. -/
theorem wf_storage_account_present (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (hw : WF σ) (hs : σ.storage[a]? = some slots) :
    σ.account? a ≠ none := by
  have hp := hw.2.2 a slots hs
  intro hn
  rw [← account?_eq_lookup, hn] at hp
  contradiction

/-- An absent account has zero storage under the structural invariant. -/
theorem storageAt_zero_of_account_none (σ : MathState) (a : Address) (k : Bytes32)
    (hw : WF σ) (ha : σ.account? a = none) : σ.storageAt a k = U256.zero := by
  cases hs : σ.storage[a]? with
  | none => exact storageAt_of_storage_none σ a k hs
  | some slots => exact False.elim (wf_storage_account_present σ a slots hw hs ha)

/-- Under `WF`, observing zero means the slot is absent in every present inner map. -/
theorem storageAt_zero_iff (σ : MathState) (a : Address) (k : Bytes32) (hw : WF σ) :
    σ.storageAt a k = U256.zero ↔
      ∀ slots : Std.ExtTreeMap Bytes32 U256, σ.storage[a]? = some slots → slots[k]? = none := by
  constructor
  · intro hz slots hs
    cases hk : slots[k]? with
    | none => rfl
    | some v =>
      rw [storageAt_of_slot_some σ a k slots v hs hk] at hz
      exact False.elim (wf_storage_value_ne_zero σ a slots k v hw hs hk hz)
  · intro hn
    cases hs : σ.storage[a]? with
    | none => exact storageAt_of_storage_none σ a k hs
    | some slots => exact storageAt_of_slot_none σ a k slots hs (hn slots hs)

/-- Under `WF`, an address has raw storage exactly when some observed slot is nonzero. -/
theorem storage_present_iff_exists_nonzero (σ : MathState) (a : Address) (hw : WF σ) :
    σ.storage[a]?.isSome = true ↔ ∃ k : Bytes32, σ.storageAt a k ≠ U256.zero := by
  constructor
  · intro hp
    cases hs : σ.storage[a]? with
    | none => simp [hs] at hp
    | some slots =>
      apply Classical.byContradiction
      intro hn
      have he : slots = ∅ := Std.ExtTreeMap.ext_getElem? (fun k ↦ by
        cases hk : slots[k]? with
        | none => simp
        | some v =>
          apply False.elim
          apply hn
          exact ⟨k, by
            rw [storageAt_of_slot_some σ a k slots v hs hk]
            exact wf_storage_value_ne_zero σ a slots k v hw hs hk⟩)
      have hne := wf_storage_nonempty σ a slots hw hs
      simp [he] at hne
  · intro ⟨k, hk⟩
    cases hs : σ.storage[a]? with
    | none => exact False.elim (hk (storageAt_of_storage_none σ a k hs))
    | some slots => rfl

end MathState

end STFSpec.State
