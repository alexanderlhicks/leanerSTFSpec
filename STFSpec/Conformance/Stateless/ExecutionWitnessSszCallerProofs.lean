/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual witness schema clients

Library `EthConformance`. Private clients consume the named dictionary and complete
certificates through the public Stateless facade, on arbitrary whole arrays and values.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionWitnessSszCallerProofs

open STFSpec.Stateless STFSpec.Codec

private abbrev actual : SszSchema ExecutionWitness := ExecutionWitness.instSszSchema

private theorem descriptor : actual.type = .container [
    .progressiveList (.byteList 1024), .progressiveList (.byteList 65536),
    .list (.byteList 1024) 256] := rfl

private theorem names : actual.fieldNames = ["state", "codes", "headers"] := rfl

private theorem limits :
    maxBytesPerWitnessNode = STFSpec.Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE ∧
    maxBytesPerCode = STFSpec.Fork.Amsterdam.MAX_BYTES_PER_CODE ∧
    maxBytesPerHeader = STFSpec.Fork.Amsterdam.MAX_BYTES_PER_HEADER ∧
    maxWitnessHeaders = STFSpec.Fork.Amsterdam.MAX_WITNESS_HEADERS := ⟨rfl, rfl, rfl, rfl⟩

private theorem wf : actual.type.WellFormed := ExecutionWitness.ssz_type_wellFormed

private theorem forward : ∀ a : ExecutionWitness, actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) :=
  ExecutionWitness.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : ExecutionWitness),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := ExecutionWitness.ssz_toValue_ofValue

private theorem full_forward (state codes headers : Array ByteArray) :
    actual.toValue (ExecutionWitness.mk state codes headers) = .container [
      .list (state.toList.map SszValue.bytes), .list (codes.toList.map SszValue.bytes),
      .list (headers.toList.map SszValue.bytes)] := rfl

private theorem full_recovery (state codes headers : Array ByteArray)
    (h : actual.valid ⟨state, codes, headers⟩) :
    actual.ofValue? (.container [
      .list (state.toList.map SszValue.bytes), .list (codes.toList.map SszValue.bytes),
      .list (headers.toList.map SszValue.bytes)]) = some ⟨state, codes, headers⟩ :=
  (forward _ h).1

private theorem recovered_reforward (v : SszValue) (a : ExecutionWitness)
    (ht : SszValue.WellTyped actual.type v) (ha : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, ha⟩

private theorem image_countRecoverable (a : ExecutionWitness) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue, ExecutionWitness.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _), SszType.fixedSize?_eq (.byteList _)]

end STFSpec.Conformance.Stateless.ExecutionWitnessSszCallerProofs
