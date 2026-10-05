/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeSet

/-!
# Raw block diff values

Library `EthState`: four EELS effect fields (`src/ethereum/state.py:61–89`)
and three supplied B1 order metadata fields. All finite raw fields remain exact;
this record establishes no well-formedness, history, application or clear order.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State

open Base

/-- Raw block effects and supplied replay metadata, without validation or normalization. -/
structure BlockDiff where
  /-- No entry means no change; stored `none` deletes; stored Account replaces. -/
  accountChanges : Std.ExtTreeMap Address (Option Account)
  /-- Supplied account order, retaining every occurrence. -/
  accountOrder : List Address
  /-- Supplied slot changes, retaining explicit zero writes and empty inner maps. -/
  storageChanges : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  /-- Supplied storage-address order, retaining every occurrence. -/
  storageAddressOrder : List Address
  /-- Supplied per-address slot lists, retaining empty/duplicate/mismatched entries. -/
  storageSlotOrder : Std.ExtTreeMap Address (List Bytes32)
  /-- Arbitrary complete code bytes, without hash authenticity or reserved-hash filtering. -/
  codeChanges : Std.ExtTreeMap Hash32 ByteArray
  /-- Storage clear membership only; it supplies no clear traversal order. -/
  storageClears : Std.ExtTreeSet Address

namespace BlockDiff

variable (ac : Std.ExtTreeMap Address (Option Account)) (ao : List Address)
variable (sc : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
variable (sa : List Address) (so : Std.ExtTreeMap Address (List Bytes32))
variable (cc : Std.ExtTreeMap Hash32 ByteArray) (cl : Std.ExtTreeSet Address)

/-- Construction preserves the complete `accountChanges` field. -/
theorem accountChanges_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).accountChanges = ac := rfl

/-- Construction preserves the complete `accountOrder` field. -/
theorem accountOrder_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).accountOrder = ao := rfl

/-- Construction preserves the complete `storageChanges` field. -/
theorem storageChanges_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).storageChanges = sc := rfl

/-- Construction preserves the complete `storageAddressOrder` field. -/
theorem storageAddressOrder_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).storageAddressOrder = sa := rfl

/-- Construction preserves the complete `storageSlotOrder` field. -/
theorem storageSlotOrder_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).storageSlotOrder = so := rfl

/-- Construction preserves the complete `codeChanges` field. -/
theorem codeChanges_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).codeChanges = cc := rfl

/-- Construction preserves the complete `storageClears` field. -/
theorem storageClears_mk :
    (BlockDiff.mk ac ao sc sa so cc cl).storageClears = cl := rfl

/-- Reconstruction from all seven raw fields returns the diff. -/
theorem eta (d : BlockDiff) :
    BlockDiff.mk d.accountChanges d.accountOrder d.storageChanges d.storageAddressOrder
      d.storageSlotOrder d.codeChanges d.storageClears = d := by
  cases d
  rfl

/-- Equality of every complete raw field determines the diff. -/
theorem ext {d e : BlockDiff}
    (hac : d.accountChanges = e.accountChanges) (hao : d.accountOrder = e.accountOrder)
    (hsc : d.storageChanges = e.storageChanges)
    (hsa : d.storageAddressOrder = e.storageAddressOrder)
    (hso : d.storageSlotOrder = e.storageSlotOrder)
    (hcc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) : d = e := by
  cases d
  cases e
  cases hac
  cases hao
  cases hsc
  cases hsa
  cases hso
  cases hcc
  cases hcl
  rfl

/-- Whole optional map/list lookups, exact global lists and clear membership determine the diff. -/
theorem ext_lookup {d e : BlockDiff}
    (hac : ∀ a : Address, d.accountChanges[a]? = e.accountChanges[a]?)
    (hao : d.accountOrder = e.accountOrder)
    (hsc : ∀ a : Address, d.storageChanges[a]? = e.storageChanges[a]?)
    (hsa : d.storageAddressOrder = e.storageAddressOrder)
    (hso : ∀ a : Address, d.storageSlotOrder[a]? = e.storageSlotOrder[a]?)
    (hcc : ∀ h : Hash32, d.codeChanges[h]? = e.codeChanges[h]?)
    (hcl : ∀ a : Address, a ∈ d.storageClears ↔ a ∈ e.storageClears) : d = e :=
  ext (Std.ExtTreeMap.ext_getElem? hac) hao (Std.ExtTreeMap.ext_getElem? hsc) hsa
    (Std.ExtTreeMap.ext_getElem? hso) (Std.ExtTreeMap.ext_getElem? hcc)
    (Std.ExtTreeSet.ext_mem hcl)

/-- Constructor lookup retains the whole optional `accountChanges` payload. -/
theorem accountChanges_mk_lookup (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).accountChanges[a]? = ac[a]? := rfl

/-- Constructor lookup retains the whole optional `storageChanges` payload. -/
theorem storageChanges_mk_lookup (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).storageChanges[a]? = sc[a]? := rfl

/-- Constructor lookup retains the whole optional `storageSlotOrder` payload. -/
theorem storageSlotOrder_mk_lookup (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).storageSlotOrder[a]? = so[a]? := rfl

/-- Constructor lookup retains the whole optional `codeChanges` payload. -/
theorem codeChanges_mk_lookup (h : Hash32) :
    (BlockDiff.mk ac ao sc sa so cc cl).codeChanges[h]? = cc[h]? := rfl

/-- Constructor clear membership is exactly the supplied set membership. -/
theorem storageClears_mk_mem (a : Address) :
    a ∈ (BlockDiff.mk ac ao sc sa so cc cl).storageClears ↔ a ∈ cl := Iff.rfl

end BlockDiff

end STFSpec.State
