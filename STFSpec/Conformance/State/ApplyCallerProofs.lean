/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Apply

/-!
# Public mathematical apply law callers

Library `EthConformance`: eighteen arbitrary-input proof-only callers of the public state laws.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.ApplyCallerProofs

open STFSpec.Base STFSpec.State

/-- Account changes preserve exact optional replacements. -/
theorem apply_accounts_lookup_caller (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).accounts[a]? =
      match d.accountChanges[a]? with
      | Option.none => σ.accounts[a]?
      | Option.some replacement => replacement :=
  MathState.apply_accounts_lookup σ d a

/-- Account observation reflects the exact change or original value. -/
theorem apply_account?_eq_caller (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).account? a =
      match d.accountChanges[a]? with
      | Option.none => σ.account? a
      | Option.some replacement => replacement :=
  MathState.apply_account?_eq σ d a

/-- Storage lookup preserves clear-before-write and local pruning. -/
theorem apply_storage_lookup_caller (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).storage[a]? =
      match d.storageChanges[a]? with
      | Option.none => if a ∈ d.storageClears then none else σ.storage[a]?
      | Option.some writes =>
        let out := writes.foldl (fun out k v ↦
          if v = U256.zero then out.erase k else out.insert k v)
          ((if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅)
        if out.isEmpty then none else some out :=
  MathState.apply_storage_lookup σ d a

/-- Raw code changes replace complete bytes at every hash. -/
theorem apply_code_lookup_caller (σ : MathState) (d : BlockDiff) (h : Hash32) :
    (σ.apply d).code[h]? =
      match d.codeChanges[h]? with
      | Option.none => σ.code[h]?
      | Option.some bytes => some bytes :=
  MathState.apply_code_lookup σ d h

/-- Code observation retains the supplied reserved-hash bypass. -/
theorem apply_code?_eq_caller (σ : MathState) (d : BlockDiff) (consts : HashConsts) (h : Hash32) :
    (σ.apply d).code? consts h =
      if h = consts.emptyCodeHash then some ByteArray.empty else
        match d.codeChanges[h]? with
        | Option.none => σ.code[h]?
        | Option.some bytes => some bytes :=
  MathState.apply_code?_eq σ d consts h

/-- Visible storage prefers writes, then clears, then the original value. -/
theorem apply_storageAt_eq_caller (σ : MathState) (d : BlockDiff) (a : Address) (k : Bytes32) :
    (σ.apply d).storageAt a k =
      match (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) with
      | none => if a ∈ d.storageClears then U256.zero else σ.storageAt a k
      | some value => value :=
  MathState.apply_storageAt_eq σ d a k

/-- No account changes preserve the complete account map. -/
theorem apply_accounts_of_no_changes_caller (σ : MathState) (d : BlockDiff)
    (hac : d.accountChanges = ∅) : (σ.apply d).accounts = σ.accounts :=
  MathState.apply_accounts_of_no_changes σ d hac

/-- No writes or clears preserve the complete storage map. -/
theorem apply_storage_of_no_changes_caller (σ : MathState) (d : BlockDiff)
    (hsc : d.storageChanges = ∅) (hcl : d.storageClears = ∅) :
    (σ.apply d).storage = σ.storage :=
  MathState.apply_storage_of_no_changes σ d hsc hcl

/-- No code changes preserve the complete code map. -/
theorem apply_code_of_no_changes_caller (σ : MathState) (d : BlockDiff)
    (hcc : d.codeChanges = ∅) : (σ.apply d).code = σ.code :=
  MathState.apply_code_of_no_changes σ d hcc

/-- No effect fields preserve the exact raw state. -/
theorem apply_of_no_changes_caller (σ : MathState) (d : BlockDiff)
    (hac : d.accountChanges = ∅) (hsc : d.storageChanges = ∅)
    (hcc : d.codeChanges = ∅) (hcl : d.storageClears = ∅) : σ.apply d = σ :=
  MathState.apply_of_no_changes σ d hac hsc hcc hcl

/-- Equal effect fields give equal states despite metadata differences. -/
theorem apply_congr_effects_caller (σ : MathState) (d e : BlockDiff)
    (hac : d.accountChanges = e.accountChanges) (hsc : d.storageChanges = e.storageChanges)
    (hcc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    σ.apply d = σ.apply e :=
  MathState.apply_congr_effects σ d e hac hsc hcc hcl

/-- Untouched addresses retain their complete optional storage maps. -/
theorem apply_storage_of_untouched_caller (σ : MathState) (d : BlockDiff) (a : Address)
    (hsc : d.storageChanges[a]? = none) (hcl : a ∉ d.storageClears) :
    (σ.apply d).storage[a]? = σ.storage[a]? :=
  MathState.apply_storage_of_untouched σ d a hsc hcl

/-- Account deletion alone preserves untouched storage. -/
theorem apply_storage_of_deleted_account_without_clear_caller (σ : MathState) (d : BlockDiff)
    (a : Address) (hac : d.accountChanges[a]? = some none)
    (hsc : d.storageChanges[a]? = none) (hcl : a ∉ d.storageClears) :
    (σ.apply d).account? a = none ∧ (σ.apply d).storage[a]? = σ.storage[a]? :=
  MathState.apply_storage_of_deleted_account_without_clear σ d a hac hsc hcl

/-- A clear without writes removes the complete storage entry. -/
theorem apply_storage_of_clear_no_writes_caller (σ : MathState) (d : BlockDiff) (a : Address)
    (hcl : a ∈ d.storageClears) (hsc : d.storageChanges[a]? = none) :
    (σ.apply d).storage[a]? = none :=
  MathState.apply_storage_of_clear_no_writes σ d a hcl hsc

/-- Empty writes prune an actually empty post-clear base. -/
theorem apply_storage_of_empty_writes_caller (σ : MathState) (d : BlockDiff) (a : Address)
    (hsc : d.storageChanges[a]? = some (∅ : Std.ExtTreeMap Bytes32 U256 compare)) :
    (σ.apply d).storage[a]? =
      let base := (if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅
      if base.isEmpty then none else some base :=
  MathState.apply_storage_of_empty_writes σ d a hsc

/-- An explicit zero write removes its raw slot. -/
theorem apply_storage_slot_of_write_zero_caller (σ : MathState) (d : BlockDiff)
    (a : Address) (k : Bytes32)
    (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = some U256.zero) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) = none :=
  MathState.apply_storage_slot_of_write_zero σ d a k hq

/-- A nonzero write stores its exact value. -/
theorem apply_storage_slot_of_write_ne_zero_caller (σ : MathState) (d : BlockDiff)
    (a : Address) (k : Bytes32) (v : U256)
    (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = some v)
    (hv : v ≠ U256.zero) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) = some v :=
  MathState.apply_storage_slot_of_write_ne_zero σ d a k v hq hv

/-- Unwritten slots retain their raw value unless cleared. -/
theorem apply_storage_slot_of_no_write_caller (σ : MathState) (d : BlockDiff) (a : Address)
    (k : Bytes32) (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = none) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) =
      if a ∈ d.storageClears then none else (σ.storage[a]?).bind (fun slots ↦ slots[k]?) :=
  MathState.apply_storage_slot_of_no_write σ d a k hq

end STFSpec.Conformance.ApplyCallerProofs
