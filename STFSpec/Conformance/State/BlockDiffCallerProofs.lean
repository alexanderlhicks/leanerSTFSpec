/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockDiff

/-!
# Arbitrary complete-field BlockDiff callers

Library `EthConformance`: named symbolic clients for all fifteen public laws.
Clients use public owner/Std equations, without payload representation unfolding.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.BlockDiffCallerProofs

open STFSpec.Base STFSpec.State

variable (ac : Std.ExtTreeMap Address (Option Account)) (ao : List Address)
variable (sc : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
variable (sa : List Address) (so : Std.ExtTreeMap Address (List Bytes32))
variable (cc : Std.ExtTreeMap Hash32 ByteArray) (cl : Std.ExtTreeSet Address)

/-- Arbitrary public caller of `accountChanges_mk`. -/
theorem accountChanges_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).accountChanges = ac :=
  BlockDiff.accountChanges_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `accountOrder_mk`. -/
theorem accountOrder_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).accountOrder = ao :=
  BlockDiff.accountOrder_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `storageChanges_mk`. -/
theorem storageChanges_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).storageChanges = sc :=
  BlockDiff.storageChanges_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `storageAddressOrder_mk`. -/
theorem storageAddressOrder_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).storageAddressOrder = sa :=
  BlockDiff.storageAddressOrder_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `storageSlotOrder_mk`. -/
theorem storageSlotOrder_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).storageSlotOrder = so :=
  BlockDiff.storageSlotOrder_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `codeChanges_mk`. -/
theorem codeChanges_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).codeChanges = cc :=
  BlockDiff.codeChanges_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `storageClears_mk`. -/
theorem storageClears_mk_client :
    (BlockDiff.mk ac ao sc sa so cc cl).storageClears = cl :=
  BlockDiff.storageClears_mk ac ao sc sa so cc cl

/-- Arbitrary public caller of `eta`. -/
theorem eta_client (d : BlockDiff) :
    BlockDiff.mk d.accountChanges d.accountOrder d.storageChanges d.storageAddressOrder
      d.storageSlotOrder d.codeChanges d.storageClears = d :=
  BlockDiff.eta d

/-- Arbitrary public caller of `ext`. -/
theorem ext_client {d e : BlockDiff}
    (hac : d.accountChanges = e.accountChanges) (hao : d.accountOrder = e.accountOrder)
    (hsc : d.storageChanges = e.storageChanges)
    (hsa : d.storageAddressOrder = e.storageAddressOrder)
    (hso : d.storageSlotOrder = e.storageSlotOrder)
    (hcc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    d = e :=
  BlockDiff.ext hac hao hsc hsa hso hcc hcl

/-- Arbitrary public caller of `ext_lookup`. -/
theorem ext_lookup_client {d e : BlockDiff}
    (hac : ∀ a : Address, d.accountChanges[a]? = e.accountChanges[a]?)
    (hao : d.accountOrder = e.accountOrder)
    (hsc : ∀ a : Address, d.storageChanges[a]? = e.storageChanges[a]?)
    (hsa : d.storageAddressOrder = e.storageAddressOrder)
    (hso : ∀ a : Address, d.storageSlotOrder[a]? = e.storageSlotOrder[a]?)
    (hcc : ∀ h : Hash32, d.codeChanges[h]? = e.codeChanges[h]?)
    (hcl : ∀ a : Address, a ∈ d.storageClears ↔ a ∈ e.storageClears) :
    d = e :=
  BlockDiff.ext_lookup hac hao hsc hsa hso hcc hcl

/-- Arbitrary public caller of `accountChanges_mk_lookup`. -/
theorem accountChanges_mk_lookup_client (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).accountChanges[a]? = ac[a]? :=
  BlockDiff.accountChanges_mk_lookup ac ao sc sa so cc cl a

/-- Arbitrary public caller of `storageChanges_mk_lookup`. -/
theorem storageChanges_mk_lookup_client (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).storageChanges[a]? = sc[a]? :=
  BlockDiff.storageChanges_mk_lookup ac ao sc sa so cc cl a

/-- Arbitrary public caller of `storageSlotOrder_mk_lookup`. -/
theorem storageSlotOrder_mk_lookup_client (a : Address) :
    (BlockDiff.mk ac ao sc sa so cc cl).storageSlotOrder[a]? = so[a]? :=
  BlockDiff.storageSlotOrder_mk_lookup ac ao sc sa so cc cl a

/-- Arbitrary public caller of `codeChanges_mk_lookup`. -/
theorem codeChanges_mk_lookup_client (h : Hash32) :
    (BlockDiff.mk ac ao sc sa so cc cl).codeChanges[h]? = cc[h]? :=
  BlockDiff.codeChanges_mk_lookup ac ao sc sa so cc cl h

/-- Arbitrary public caller of `storageClears_mk_mem`. -/
theorem storageClears_mk_mem_client (a : Address) :
    a ∈ (BlockDiff.mk ac ao sc sa so cc cl).storageClears ↔ a ∈ cl :=
  BlockDiff.storageClears_mk_mem ac ao sc sa so cc cl a

end STFSpec.Conformance.State.BlockDiffCallerProofs
