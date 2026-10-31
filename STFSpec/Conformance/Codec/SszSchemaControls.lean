/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Explicit SSZ dictionary controls

Library `EthConformance`. Two private dictionaries on the same carrier deliberately
have false validity and broken inverses. Complete bytes and roots follow solely
through public wrapper/provider equations. These are metadata controls, not actual
certified schema instances; no instance declaration or source claim is supplied.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private abbrev narrow : SszSchema Nat where
  type := .uint 1
  fieldNames := ["narrow"]
  valid := fun _ ↦ False
  toValue := fun a ↦ .uint (a % 256)
  ofValue? := fun _ ↦ none

private abbrev wide : SszSchema Nat where
  type := .uint 2
  fieldNames := ["wide"]
  valid := fun _ ↦ False
  toValue := fun a ↦ .uint (a % 65536)
  ofValue? := fun _ ↦ none

private theorem narrow_serializable (a : Nat) :
    Ssz.Serializable narrow.type (narrow.toValue a) := by
  apply (Ssz.serializable_iff _ _).mpr
  exact ⟨by decide, Nat.mod_lt _ (by decide)⟩

private theorem wide_serializable (a : Nat) :
    Ssz.Serializable wide.type (wide.toValue a) := by
  apply (Ssz.serializable_iff _ _).mpr
  exact ⟨by decide, Nat.mod_lt _ (by decide)⟩

private theorem narrow_rootable (a : Nat) :
    Ssz.Rootable narrow.type (narrow.toValue a) := by
  apply (Ssz.rootable_iff _ _).mpr
  exact ⟨by decide, Nat.mod_lt _ (by decide)⟩

private theorem wide_rootable (a : Nat) :
    Ssz.Rootable wide.type (wide.toValue a) := by
  apply (Ssz.rootable_iff _ _).mpr
  exact ⟨by decide, Nat.mod_lt _ (by decide)⟩

private theorem metadata_uncertified (a : Nat) :
    ¬ narrow.valid a ∧ narrow.ofValue? (narrow.toValue a) ≠ some a ∧
      ¬ wide.valid a ∧ wide.ofValue? (wide.toValue a) ≠ some a := by
  change (¬ False) ∧ (none : Option Nat) ≠ some a ∧ (¬ False) ∧
    (none : Option Nat) ≠ some a
  simp

private theorem narrow_bytes (a : Nat) :
    (@SszSchema.encodeBytes Nat narrow a (narrow_serializable a)).data.toList =
      [UInt8.ofNat (a % 256)] := by
  rw [@SszSchema.encodeBytes_eq Nat narrow]
  change (Ssz.encode (.uint 1) (.uint (a % 256)) (narrow_serializable a)).data.toList = _
  simpa using Ssz.encode_eq (.uint 1) (.uint (a % 256)) (narrow_serializable a)

private theorem narrow_root (a : Nat) :
    @SszSchema.hashTreeRoot Nat narrow a (narrow_rootable a) =
      (Base.FixedBytes.ofLeNat (a % 256) : Base.Bytes32) := by
  rw [@SszSchema.hashTreeRoot_eq Nat narrow]
  exact Ssz.hashTreeRoot_eq (.uint 1) (.uint (a % 256)) (narrow_rootable a)

private theorem wide_root (a : Nat) :
    @SszSchema.hashTreeRoot Nat wide a (wide_rootable a) =
      (Base.FixedBytes.ofLeNat (a % 65536) : Base.Bytes32) := by
  rw [@SszSchema.hashTreeRoot_eq Nat wide]
  exact Ssz.hashTreeRoot_eq (.uint 2) (.uint (a % 65536)) (wide_rootable a)

private theorem same_carrier_different_bytes :
    (@SszSchema.encodeBytes Nat narrow 258 (narrow_serializable 258)).data.toList = [2] ∧
      (@SszSchema.encodeBytes Nat wide 258 (wide_serializable 258)).data.toList = [2, 1] ∧
      (@SszSchema.encodeBytes Nat wide 513 (wide_serializable 513)).data.toList = [1, 2] := by
  refine ⟨narrow_bytes 258, ?_, ?_⟩
  · rw [@SszSchema.encodeBytes_eq Nat wide]
    exact Ssz.encode_eq (.uint 2) (.uint 258) (wide_serializable 258)
  · rw [@SszSchema.encodeBytes_eq Nat wide]
    exact Ssz.encode_eq (.uint 2) (.uint 513) (wide_serializable 513)

private theorem same_carrier_different_root_bytes :
    (@SszSchema.hashTreeRoot Nat narrow 258 (narrow_rootable 258)).toBytes.toList =
        [2] ++ List.replicate 31 0 ∧
      (@SszSchema.hashTreeRoot Nat wide 258 (wide_rootable 258)).toBytes.toList =
        [2, 1] ++ List.replicate 30 0 ∧
      (@SszSchema.hashTreeRoot Nat wide 513 (wide_rootable 513)).toBytes.toList =
        [1, 2] ++ List.replicate 30 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [narrow_root, wide_root]
    rw [Base.FixedBytes.toBytes_ofLeNat]
    decide

end STFSpec.Conformance.Codec
