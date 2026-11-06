/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete witness wire controls

Library `EthConformance`. Twenty-five source-free mathematical cases compare all 7159
expected bytes through the actual dictionary and independently proved local Serializable
premises. Expected inputs and bytes were frozen and independently compared before this
implementation. These controls establish no source-host or guest correspondence.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionWitnessSszWireControls

open STFSpec.Stateless STFSpec.Codec

private abbrev schema := ExecutionWitness.instSszSchema

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem members_support (bs : List ByteArray) (limit : Nat)
    (h : ∀ b ∈ bs, b.size ≤ limit) :
    ∀ v ∈ bs.map SszValue.bytes, Ssz.Serializable (.byteList limit) v := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  exact (Ssz.serializable_iff (.byteList limit) (.bytes b)).mpr (h b hb)

-- empty-triple
private def case00 : ExecutionWitness := ⟨#[], #[], #[]⟩
private theorem case00_support : Ssz.Serializable schema.type (schema.toValue case00) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case00.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case00.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case00.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case00]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case00] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case00_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0]⟩
#guard (SszSchema.encodeBytes case00 case00_support).data.toList == case00_expected.data.toList

-- state-one-empty
private def case01 : ExecutionWitness := ⟨#[⟨#[]⟩], #[], #[]⟩
private theorem case01_support : Ssz.Serializable schema.type (schema.toValue case01) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case01.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case01.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case01.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case01]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case01] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case01_expected : ByteArray := ⟨#[12, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 4, 0, 0, 0]⟩
#guard (SszSchema.encodeBytes case01 case01_support).data.toList == case01_expected.data.toList

-- codes-one-empty
private def case02 : ExecutionWitness := ⟨#[], #[⟨#[]⟩], #[]⟩
private theorem case02_support : Ssz.Serializable schema.type (schema.toValue case02) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case02.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case02.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case02.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case02]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case02] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case02_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 16, 0, 0, 0, 4, 0, 0, 0]⟩
#guard (SszSchema.encodeBytes case02 case02_support).data.toList == case02_expected.data.toList

-- headers-one-empty
private def case03 : ExecutionWitness := ⟨#[], #[], #[⟨#[]⟩]⟩
private theorem case03_support : Ssz.Serializable schema.type (schema.toValue case03) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case03.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case03.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case03.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case03]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case03] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case03_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0]⟩
#guard (SszSchema.encodeBytes case03 case03_support).data.toList == case03_expected.data.toList

-- repeated-empties
private def case04 : ExecutionWitness := ⟨#[⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩], #[⟨#[]⟩, ⟨#[]⟩], #[⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩]⟩
private theorem case04_support : Ssz.Serializable schema.type (schema.toValue case04) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case04.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case04.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case04.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case04]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case04] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case04_expected : ByteArray := ⟨#[12, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 12, 0, 0, 0,
  12, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 16, 0,
  0, 0]⟩
#guard (SszSchema.encodeBytes case04 case04_support).data.toList == case04_expected.data.toList

-- asymmetric
private def case05 : ExecutionWitness := ⟨#[⟨#[1]⟩, ⟨#[2, 3]⟩], #[⟨#[255]⟩], #[⟨#[170]⟩, ⟨#[]⟩]⟩
private theorem case05_support : Ssz.Serializable schema.type (schema.toValue case05) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case05.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case05.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case05.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case05]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case05] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case05_expected : ByteArray := ⟨#[12, 0, 0, 0, 23, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0,
  9, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 255, 8, 0, 0, 0, 9, 0, 0, 0, 170]⟩
#guard (SszSchema.encodeBytes case05 case05_support).data.toList == case05_expected.data.toList

-- distinct-nonzero
private def case06 : ExecutionWitness := ⟨#[⟨#[7, 19]⟩, ⟨#[31]⟩], #[⟨#[43, 59, 71]⟩], #[⟨#[83]⟩,
  ⟨#[97, 109]⟩]⟩
private theorem case06_support : Ssz.Serializable schema.type (schema.toValue case06) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case06.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case06.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case06.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case06]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case06] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case06_expected : ByteArray := ⟨#[12, 0, 0, 0, 23, 0, 0, 0, 30, 0, 0, 0, 8, 0, 0, 0,
  10, 0, 0, 0, 7, 19, 31, 4, 0, 0, 0, 43, 59, 71, 8, 0, 0, 0, 9, 0, 0, 0, 83, 97, 109]⟩
#guard (SszSchema.encodeBytes case06 case06_support).data.toList == case06_expected.data.toList

-- duplicate-members
private def case07 : ExecutionWitness := ⟨#[⟨#[8, 9]⟩, ⟨#[8, 9]⟩], #[⟨#[21]⟩, ⟨#[21]⟩, ⟨#[21]⟩],
  #[⟨#[34, 35]⟩, ⟨#[34, 35]⟩]⟩
private theorem case07_support : Ssz.Serializable schema.type (schema.toValue case07) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case07.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case07.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case07.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case07]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case07] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case07_expected : ByteArray := ⟨#[12, 0, 0, 0, 24, 0, 0, 0, 39, 0, 0, 0, 8, 0, 0, 0,
  10, 0, 0, 0, 8, 9, 8, 9, 12, 0, 0, 0, 13, 0, 0, 0, 14, 0, 0, 0, 21, 21, 21, 8, 0, 0, 0, 10, 0,
  0, 0, 34, 35, 34, 35]⟩
#guard (SszSchema.encodeBytes case07 case07_support).data.toList == case07_expected.data.toList

-- state-permutation-before
private def case08 : ExecutionWitness := ⟨#[⟨#[10]⟩, ⟨#[20, 21]⟩, ⟨#[]⟩], #[⟨#[30]⟩], #[⟨#[40]⟩]⟩
private theorem case08_support : Ssz.Serializable schema.type (schema.toValue case08) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case08.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case08.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case08.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case08]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case08] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case08_expected : ByteArray := ⟨#[12, 0, 0, 0, 27, 0, 0, 0, 32, 0, 0, 0, 12, 0, 0, 0,
  13, 0, 0, 0, 15, 0, 0, 0, 10, 20, 21, 4, 0, 0, 0, 30, 4, 0, 0, 0, 40]⟩
#guard (SszSchema.encodeBytes case08 case08_support).data.toList == case08_expected.data.toList

-- state-permutation-after
private def case09 : ExecutionWitness := ⟨#[⟨#[]⟩, ⟨#[20, 21]⟩, ⟨#[10]⟩], #[⟨#[30]⟩], #[⟨#[40]⟩]⟩
private theorem case09_support : Ssz.Serializable schema.type (schema.toValue case09) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case09.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case09.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case09.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case09]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case09] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case09_expected : ByteArray := ⟨#[12, 0, 0, 0, 27, 0, 0, 0, 32, 0, 0, 0, 12, 0, 0, 0,
  12, 0, 0, 0, 14, 0, 0, 0, 20, 21, 10, 4, 0, 0, 0, 30, 4, 0, 0, 0, 40]⟩
#guard (SszSchema.encodeBytes case09 case09_support).data.toList == case09_expected.data.toList

-- codes-permutation-before
private def case10 : ExecutionWitness := ⟨#[⟨#[10]⟩], #[⟨#[30]⟩, ⟨#[31, 32]⟩, ⟨#[]⟩], #[⟨#[40]⟩]⟩
private theorem case10_support : Ssz.Serializable schema.type (schema.toValue case10) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case10.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case10.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case10.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case10]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case10] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case10_expected : ByteArray := ⟨#[12, 0, 0, 0, 17, 0, 0, 0, 32, 0, 0, 0, 4, 0, 0, 0,
  10, 12, 0, 0, 0, 13, 0, 0, 0, 15, 0, 0, 0, 30, 31, 32, 4, 0, 0, 0, 40]⟩
#guard (SszSchema.encodeBytes case10 case10_support).data.toList == case10_expected.data.toList

-- codes-permutation-after
private def case11 : ExecutionWitness := ⟨#[⟨#[10]⟩], #[⟨#[]⟩, ⟨#[31, 32]⟩, ⟨#[30]⟩], #[⟨#[40]⟩]⟩
private theorem case11_support : Ssz.Serializable schema.type (schema.toValue case11) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case11.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case11.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case11.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case11]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case11] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case11_expected : ByteArray := ⟨#[12, 0, 0, 0, 17, 0, 0, 0, 32, 0, 0, 0, 4, 0, 0, 0,
  10, 12, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0, 31, 32, 30, 4, 0, 0, 0, 40]⟩
#guard (SszSchema.encodeBytes case11 case11_support).data.toList == case11_expected.data.toList

-- headers-permutation-before
private def case12 : ExecutionWitness := ⟨#[⟨#[10]⟩], #[⟨#[30]⟩], #[⟨#[40]⟩, ⟨#[41, 42]⟩, ⟨#[]⟩]⟩
private theorem case12_support : Ssz.Serializable schema.type (schema.toValue case12) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case12.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case12.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case12.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case12]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case12] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case12_expected : ByteArray := ⟨#[12, 0, 0, 0, 17, 0, 0, 0, 22, 0, 0, 0, 4, 0, 0, 0,
  10, 4, 0, 0, 0, 30, 12, 0, 0, 0, 13, 0, 0, 0, 15, 0, 0, 0, 40, 41, 42]⟩
#guard (SszSchema.encodeBytes case12 case12_support).data.toList == case12_expected.data.toList

-- headers-permutation-after
private def case13 : ExecutionWitness := ⟨#[⟨#[10]⟩], #[⟨#[30]⟩], #[⟨#[]⟩, ⟨#[41, 42]⟩, ⟨#[40]⟩]⟩
private theorem case13_support : Ssz.Serializable schema.type (schema.toValue case13) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case13.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case13.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case13.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case13]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case13] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case13_expected : ByteArray := ⟨#[12, 0, 0, 0, 17, 0, 0, 0, 22, 0, 0, 0, 4, 0, 0, 0,
  10, 4, 0, 0, 0, 30, 12, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0, 41, 42, 40]⟩
#guard (SszSchema.encodeBytes case13 case13_support).data.toList == case13_expected.data.toList

-- embedded-zero-and-255
private def case14 : ExecutionWitness := ⟨#[⟨#[0, 255, 0]⟩, ⟨#[255, 0]⟩], #[⟨#[255, 0, 127,
  255]⟩], #[⟨#[0]⟩, ⟨#[255]⟩, ⟨#[]⟩]⟩
private theorem case14_support : Ssz.Serializable schema.type (schema.toValue case14) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case14.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case14.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case14.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case14]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case14] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case14_expected : ByteArray := ⟨#[12, 0, 0, 0, 25, 0, 0, 0, 33, 0, 0, 0, 8, 0, 0, 0,
  11, 0, 0, 0, 0, 255, 0, 255, 0, 4, 0, 0, 0, 255, 0, 127, 255, 12, 0, 0, 0, 13, 0, 0, 0, 14, 0,
  0, 0, 0, 255]⟩
#guard (SszSchema.encodeBytes case14 case14_support).data.toList == case14_expected.data.toList

-- all-byte-values-state
private def case15 : ExecutionWitness := ⟨#[⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38,
  39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62,
  63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
  87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
  109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
  128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
  147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165,
  166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
  185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
  204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
  223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
  242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]⟩], #[], #[]⟩
private theorem case15_support : Ssz.Serializable schema.type (schema.toValue case15) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case15.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case15.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case15.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case15]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case15] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case15_expected : ByteArray := ⟨#[12, 0, 0, 0, 16, 1, 0, 0, 16, 1, 0, 0, 4, 0, 0, 0,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
  136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
  155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
  174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
  193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
  250, 251, 252, 253, 254, 255]⟩
#guard (SszSchema.encodeBytes case15 case15_support).data.toList == case15_expected.data.toList

-- all-byte-values-codes
private def case16 : ExecutionWitness := ⟨#[], #[⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
  14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
  38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
  62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
  108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126,
  127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
  146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164,
  165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183,
  184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
  203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221,
  222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
  241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]⟩], #[]⟩
private theorem case16_support : Ssz.Serializable schema.type (schema.toValue case16) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case16.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case16.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case16.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case16]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case16] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case16_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 16, 1, 0, 0, 4, 0, 0, 0,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
  136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
  155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
  174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
  193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
  250, 251, 252, 253, 254, 255]⟩
#guard (SszSchema.encodeBytes case16 case16_support).data.toList == case16_expected.data.toList

-- all-byte-values-headers
private def case17 : ExecutionWitness := ⟨#[], #[], #[⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
  13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
  37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
  61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
  85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
  107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
  126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
  145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
  164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182,
  183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
  202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220,
  221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
  240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]⟩]⟩
private theorem case17_support : Ssz.Serializable schema.type (schema.toValue case17) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case17.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case17.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case17.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case17]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case17] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case17_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
  136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
  155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
  174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
  193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
  250, 251, 252, 253, 254, 255]⟩
#guard (SszSchema.encodeBytes case17 case17_support).data.toList == case17_expected.data.toList

-- headers-255-empty
private def case18 : ExecutionWitness := ⟨#[], #[], #[⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩]⟩
private theorem case18_support : Ssz.Serializable schema.type (schema.toValue case18) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case18.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case18.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case18.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case18]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case18] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case18_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3,
  0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252,
  3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0,
  252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0,
  0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0, 252, 3, 0, 0]⟩
#guard (SszSchema.encodeBytes case18 case18_support).data.toList == case18_expected.data.toList

-- headers-256-last-marker
private def case19 : ExecutionWitness := ⟨#[], #[], #[⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[165]⟩]⟩
private theorem case19_support : Ssz.Serializable schema.type (schema.toValue case19) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case19.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case19.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case19.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case19]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case19] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case19_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 165]⟩
#guard (SszSchema.encodeBytes case19 case19_support).data.toList == case19_expected.data.toList

-- state-257-empty
private def case20 : ExecutionWitness := ⟨#[⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩], #[], #[]⟩
private theorem case20_support : Ssz.Serializable schema.type (schema.toValue case20) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case20.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case20.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case20.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case20]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case20] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case20_expected : ByteArray := ⟨#[12, 0, 0, 0, 16, 4, 0, 0, 16, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0]⟩
#guard (SszSchema.encodeBytes case20 case20_support).data.toList == case20_expected.data.toList

-- codes-257-last-marker
private def case21 : ExecutionWitness := ⟨#[], #[⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩,
  ⟨#[]⟩, ⟨#[]⟩, ⟨#[90]⟩], #[]⟩
private theorem case21_support : Ssz.Serializable schema.type (schema.toValue case21) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case21.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case21.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case21.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case21]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case21] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case21_expected : ByteArray := ⟨#[12, 0, 0, 0, 12, 0, 0, 0, 17, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0,
  90]⟩
#guard (SszSchema.encodeBytes case21 case21_support).data.toList == case21_expected.data.toList

-- empty-adjacent-payload
private def case22 : ExecutionWitness := ⟨#[⟨#[]⟩, ⟨#[1, 0]⟩, ⟨#[]⟩, ⟨#[255]⟩, ⟨#[]⟩], #[⟨#[]⟩,
  ⟨#[2]⟩, ⟨#[]⟩], #[⟨#[]⟩, ⟨#[3, 0]⟩, ⟨#[]⟩]⟩
private theorem case22_support : Ssz.Serializable schema.type (schema.toValue case22) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case22.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case22.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case22.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case22]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case22] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case22_expected : ByteArray := ⟨#[12, 0, 0, 0, 35, 0, 0, 0, 48, 0, 0, 0, 20, 0, 0, 0,
  20, 0, 0, 0, 22, 0, 0, 0, 22, 0, 0, 0, 23, 0, 0, 0, 1, 0, 255, 12, 0, 0, 0, 12, 0, 0, 0, 13, 0,
  0, 0, 2, 12, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0, 3, 0]⟩
#guard (SszSchema.encodeBytes case22 case22_support).data.toList == case22_expected.data.toList

-- length-transition-255-256
private def case23 : ExecutionWitness := ⟨#[⟨#[17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17]⟩, ⟨#[18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18]⟩], #[⟨#[19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]⟩, ⟨#[20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20]⟩], #[⟨#[21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21]⟩, ⟨#[22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22]⟩]⟩
private theorem case23_support : Ssz.Serializable schema.type (schema.toValue case23) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case23.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case23.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case23.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case23]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case23] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case23_expected : ByteArray := ⟨#[12, 0, 0, 0, 19, 2, 0, 0, 26, 4, 0, 0, 8, 0, 0, 0,
  7, 1, 0, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 8, 0, 0, 0, 7, 1, 0, 0, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 8,
  0, 0, 0, 7, 1, 0, 0, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22]⟩
#guard (SszSchema.encodeBytes case23 case23_support).data.toList == case23_expected.data.toList

-- unequal-members
private def case24 : ExecutionWitness := ⟨#[⟨#[1, 2, 3, 4, 5]⟩, ⟨#[]⟩, ⟨#[6]⟩], #[⟨#[7, 8]⟩, ⟨#[9,
  10, 11, 12]⟩], #[⟨#[13, 14, 15]⟩, ⟨#[16]⟩]⟩
private theorem case24_support : Ssz.Serializable schema.type (schema.toValue case24) := by
  have h_state : Ssz.Serializable (.progressiveList (.byteList maxBytesPerWitnessNode)) (.list
    (case24.state.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_codes : Ssz.Serializable (.progressiveList (.byteList maxBytesPerCode)) (.list
    (case24.codes.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨members_support _ _ (by decide), by decide⟩
  have h_headers : Ssz.Serializable (.list (.byteList maxBytesPerHeader) maxWitnessHeaders) (.list
    (case24.headers.toList.map SszValue.bytes)) := by
    apply (Ssz.serializable_iff _ _).mpr
    exact ⟨by decide, members_support _ _ (by decide), by decide⟩
  dsimp only [SszSchema.type, SszSchema.toValue, schema, ExecutionWitness.instSszSchema, case24]
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa [case24] using (show _ ∧ _ ∧ _ from ⟨h_state, h_codes, h_headers⟩)
private def case24_expected : ByteArray := ⟨#[12, 0, 0, 0, 30, 0, 0, 0, 44, 0, 0, 0, 12, 0, 0, 0,
  17, 0, 0, 0, 17, 0, 0, 0, 1, 2, 3, 4, 5, 6, 8, 0, 0, 0, 10, 0, 0, 0, 7, 8, 9, 10, 11, 12, 8, 0,
  0, 0, 11, 0, 0, 0, 13, 14, 15, 16]⟩
#guard (SszSchema.encodeBytes case24 case24_support).data.toList == case24_expected.data.toList

end STFSpec.Conformance.Stateless.ExecutionWitnessSszWireControls
