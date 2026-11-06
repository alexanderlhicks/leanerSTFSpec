/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.ExecutionWitness
import STFSpec.Stateless.WireLimits
import STFSpec.Codec.SszSchema
import STFSpec.Codec.SszWellFormed
import STFSpec.Codec.SszWellTyped
import Init.Data.Array.Lemmas

/-!
# Execution witness SSZ schema

Library `EthStateless`. The actual witness dictionary preserves complete ordered byte
payloads. Its three certificates concern payload typing and adapter inversion, separately
from serialization, roots, source-host admission and guest execution.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless.ExecutionWitness

open Codec

private def byteMembers? : List SszValue → Option (List ByteArray)
  | [] => some []
  | .bytes b :: rest => do
      let bs ← byteMembers? rest
      pure (b :: bs)
  | _ => none

private def fromValue? : SszValue → Option ExecutionWitness
  | .container [.list state, .list codes, .list headers] => do
      let state ← byteMembers? state
      let codes ← byteMembers? codes
      let headers ← byteMembers? headers
      pure ⟨state.toArray, codes.toArray, headers.toArray⟩
  | _ => none

/-- Actual witness metadata from EELS `src/ethereum/forks/amsterdam/stateless.py:41–69`
and `src/ethereum/utils/ssz.py:174–320` at the pin. Only payload bounds enter validity;
state and code counts, operation support and source-host construction remain separate. -/
instance instSszSchema : SszSchema ExecutionWitness where
  type := .container [
    .progressiveList (.byteList maxBytesPerWitnessNode),
    .progressiveList (.byteList maxBytesPerCode),
    .list (.byteList maxBytesPerHeader) maxWitnessHeaders]
  fieldNames := ["state", "codes", "headers"]
  valid a :=
    (∀ b ∈ a.state.toList, b.size ≤ maxBytesPerWitnessNode) ∧
    (∀ b ∈ a.codes.toList, b.size ≤ maxBytesPerCode) ∧
    a.headers.size ≤ maxWitnessHeaders ∧
    (∀ b ∈ a.headers.toList, b.size ≤ maxBytesPerHeader)
  toValue a := .container [
    .list (a.state.toList.map SszValue.bytes),
    .list (a.codes.toList.map SszValue.bytes),
    .list (a.headers.toList.map SszValue.bytes)]
  ofValue? := fromValue?

private theorem byteMembers?_map (bs : List ByteArray) :
    byteMembers? (bs.map SszValue.bytes) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [byteMembers?, ih]

private theorem byteMembers?_preserves (xs : List SszValue) (bs : List ByteArray)
    (h : byteMembers? xs = some bs) : bs.map SszValue.bytes = xs := by
  induction xs generalizing bs with
  | nil => simpa [byteMembers?] using h.symm
  | cons x xs ih =>
    cases x <;> try contradiction
    rename_i b
    cases hr : byteMembers? xs with
    | none => simp [byteMembers?, hr] at h
    | some rest =>
      simp [byteMembers?, hr] at h
      subst bs
      simp only [List.map_cons, ih rest hr]

private theorem fromValue?_roundtrip (a : ExecutionWitness) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, byteMembers?_map]

private theorem fromValue?_preserves (v : SszValue) (a : ExecutionWitness)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next state codes headers =>
    cases hs : byteMembers? state with
    | none => simp [hs] at h
    | some sb =>
      cases hc : byteMembers? codes with
      | none => simp [hs, hc] at h
      | some cb =>
        cases hh : byteMembers? headers with
        | none => simp [hs, hc, hh] at h
        | some hb =>
          simp [hs, hc, hh] at h
          subst a
          dsimp only [SszSchema.toValue, instSszSchema]
          simp only [byteMembers?_preserves state sb hs, byteMembers?_preserves codes cb hc,
            byteMembers?_preserves headers hb hh]
  next => contradiction

private theorem typed_forward_iff (a : ExecutionWitness) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) ↔
      instSszSchema.valid a := by
  dsimp only [SszSchema.type, SszSchema.toValue, SszSchema.valid, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), Array.length_toList]

/-- The actual witness descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.progressiveList _), SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff (.byteList _)]

/-- Every payload-valid witness round trips completely and has a well-typed image (Q81).
This certificate supplies no serialization or root support. -/
theorem ssz_ofValue_toValue (a : ExecutionWitness) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  ⟨fromValue?_roundtrip a, (typed_forward_iff a).mpr h⟩

/-- Successful reconstruction of a well-typed value preserves the entire value and
satisfies precisely the payload bounds (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : ExecutionWitness)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v := by
  have he := fromValue?_preserves v a h.2
  exact ⟨(typed_forward_iff a).mp (he.symm ▸ h.1), he⟩

end STFSpec.Stateless.ExecutionWitness
