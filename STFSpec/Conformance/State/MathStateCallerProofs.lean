/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.MathState

/-!
# MathState public-law clients

Library `EthConformance`: arbitrary public maps, accounts, bytes, keys and constants.
Each client uses a public theorem; it never unfolds Base or Std representation internals.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.MathStateCallerProofs

open STFSpec.Base STFSpec.State MathState

example (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).accounts = accounts :=
  MathState.accounts_mk accounts storage code

example (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).storage = storage :=
  MathState.storage_mk accounts storage code

example (accounts : Std.ExtTreeMap Address Account)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    (MathState.mk accounts storage code).code = code :=
  MathState.code_mk accounts storage code

example (σ : MathState) : MathState.mk σ.accounts σ.storage σ.code = σ :=
  MathState.eta σ

example {σ τ : MathState} (ha : σ.accounts = τ.accounts)
    (hs : σ.storage = τ.storage) (hc : σ.code = τ.code) : σ = τ :=
  MathState.ext ha hs hc

example {σ τ : MathState}
    (ha : ∀ a : Address, σ.accounts[a]? = τ.accounts[a]?)
    (hs : ∀ a : Address, σ.storage[a]? = τ.storage[a]?)
    (hc : ∀ h : Hash32, σ.code[h]? = τ.code[h]?) : σ = τ :=
  MathState.ext_lookup ha hs hc

example (σ : MathState) (a : Address) :
    σ.account? a = σ.accounts[a]? :=
  MathState.account?_eq_lookup σ a

example (σ : MathState) (a : Address) (k : Bytes32) :
    σ.storageAt a k =
      ((σ.storage[a]?).bind (fun slots ↦ slots[k]?)).getD U256.zero :=
  MathState.storageAt_eq_lookup σ a k

example (σ : MathState) (a : Address) (k : Bytes32)
    (hs : σ.storage[a]? = none) : σ.storageAt a k = U256.zero :=
  MathState.storageAt_of_storage_none σ a k hs

example (σ : MathState) (a : Address) (k : Bytes32)
    (slots : Std.ExtTreeMap Bytes32 U256) (hs : σ.storage[a]? = some slots)
    (hk : slots[k]? = none) : σ.storageAt a k = U256.zero :=
  MathState.storageAt_of_slot_none σ a k slots hs hk

example (σ : MathState) (a : Address) (k : Bytes32)
    (slots : Std.ExtTreeMap Bytes32 U256) (v : U256) (hs : σ.storage[a]? = some slots)
    (hk : slots[k]? = some v) : σ.storageAt a k = v :=
  MathState.storageAt_of_slot_some σ a k slots v hs hk

example (σ : MathState) (consts : HashConsts) :
    σ.code? consts consts.emptyCodeHash = some ByteArray.empty :=
  MathState.code?_empty σ consts

example (σ : MathState) (consts : HashConsts) (h : Hash32)
    (hh : h ≠ consts.emptyCodeHash) : σ.code? consts h = σ.code[h]? :=
  MathState.code?_of_ne σ consts h hh

example (σ : MathState) (consts : HashConsts) (h : Hash32)
    (other : HashConsts) (hc : consts.emptyCodeHash = other.emptyCodeHash) :
    σ.code? consts h = σ.code? other h :=
  MathState.code?_congr_consts σ consts h other hc

example (σ : MathState) : WF σ ↔
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots →
      ∀ (k : Bytes32) (v : U256), slots[k]? = some v → v ≠ U256.zero) ∧
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots → slots.isEmpty = false) ∧
    (∀ (a : Address) (slots : Std.ExtTreeMap Bytes32 U256),
      σ.storage[a]? = some slots → σ.accounts[a]?.isSome = true) :=
  MathState.wf_iff σ

example : WF (MathState.mk ∅ ∅ ∅) :=
  MathState.wf_empty

example (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (k : Bytes32) (v : U256)
    (hw : WF σ) (hs : σ.storage[a]? = some slots) (hk : slots[k]? = some v) :
    v ≠ U256.zero :=
  MathState.wf_storage_value_ne_zero σ a slots k v hw hs hk

example (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (hw : WF σ) (hs : σ.storage[a]? = some slots) :
    slots.isEmpty = false :=
  MathState.wf_storage_nonempty σ a slots hw hs

example (σ : MathState) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (hw : WF σ) (hs : σ.storage[a]? = some slots) :
    σ.account? a ≠ none :=
  MathState.wf_storage_account_present σ a slots hw hs

example (σ : MathState) (a : Address) (k : Bytes32)
    (hw : WF σ) (ha : σ.account? a = none) : σ.storageAt a k = U256.zero :=
  MathState.storageAt_zero_of_account_none σ a k hw ha

example (σ : MathState) (a : Address) (k : Bytes32) (hw : WF σ) :
    σ.storageAt a k = U256.zero ↔
      ∀ slots : Std.ExtTreeMap Bytes32 U256, σ.storage[a]? = some slots → slots[k]? = none :=
  MathState.storageAt_zero_iff σ a k hw

example (σ : MathState) (a : Address) (hw : WF σ) :
    σ.storage[a]?.isSome = true ↔ ∃ k : Bytes32, σ.storageAt a k ≠ U256.zero :=
  MathState.storage_present_iff_exists_nonzero σ a hw

end STFSpec.Conformance.State.MathStateCallerProofs
