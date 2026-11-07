/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.PayloadSsz
import STFSpec.Stateless.ExecutionRequestsSsz

/-!
# New-payload request SSZ schema

Library `EthStateless`. The ordinary four-field container delegates complete child
models and inverses to the actual payload and execution-request dictionaries.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless.NewPayloadRequest

open Base Codec

private def hashes? : List SszValue → Option (List VersionedHash)
  | [] => some []
  | .bytes b :: vs => do
      let a ← Hash32.ofBytes? (Bytes.ofByteArray b)
      let rest ← hashes? vs
      pure (a :: rest)
  | _ => none

private def fromValue? : SszValue → Option NewPayloadRequest
  | .container [payload, .list hashes, .bytes root, requests] => do
      let payload ← ExecutionPayload.instSszSchema.ofValue? payload
      let hashes ← hashes? hashes
      let root ← Hash32.ofBytes? (Bytes.ofByteArray root)
      let requests ← ExecutionRequests.instSszSchema.ofValue? requests
      pure ⟨payload, hashes.toArray, root, requests⟩
  | _ => none

/-- Actual ordinary request metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:78–96` and
`src/ethereum/utils/ssz.py:174–320`. Validity composes the actual child predicates. -/
instance instSszSchema : SszSchema NewPayloadRequest where
  type := .container [ExecutionPayload.instSszSchema.type,
    .progressiveList (.byteVector 32), .byteVector 32, ExecutionRequests.instSszSchema.type]
  fieldNames := ["execution_payload", "versioned_hashes", "parent_beacon_block_root",
    "execution_requests"]
  valid a := ExecutionPayload.instSszSchema.valid a.executionPayload ∧
    ExecutionRequests.instSszSchema.valid a.executionRequests
  toValue a := .container [ExecutionPayload.instSszSchema.toValue a.executionPayload,
    .list (a.versionedHashes.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
    .bytes a.parentBeaconBlockRoot.toBytes.toByteArray,
    ExecutionRequests.instSszSchema.toValue a.executionRequests]
  ofValue? := fromValue?

private theorem hashes?_forward (hs : List VersionedHash) :
    hashes? (hs.map (fun h ↦ .bytes h.toBytes.toByteArray)) = some hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    simp [hashes?, Bytes.ofByteArray_toByteArray, Hash32.ofBytes?_toBytes, ih]

private theorem hashes?_preserves (vs : List SszValue) (hs : List VersionedHash)
    (h : hashes? vs = some hs) :
    hs.map (fun h ↦ SszValue.bytes h.toBytes.toByteArray) = vs := by
  induction vs generalizing hs with
  | nil => simpa [hashes?] using h.symm
  | cons v vs ih =>
    cases v <;> try contradiction
    rename_i b
    simp only [hashes?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rest, hr, he⟩ := h
    subst hs
    have ea := (Hash32.ofBytes?_eq_some_iff).mp ha
    simp only [List.map_cons, ea.2, Bytes.toByteArray_ofByteArray, ih rest hr]

/-- The actual ordinary descriptor and both actual children are well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  apply (SszType.wellFormed_iff _).mpr
  refine ⟨by decide, ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ExecutionPayload.ssz_type_wellFormed
  · exact (SszType.wellFormed_iff _).mpr True.intro
  · exact True.intro
  · exact ExecutionRequests.ssz_type_wellFormed

/-- Every wire-valid request reconstructs completely and has its declared type (Q81). -/
theorem ssz_ofValue_toValue (a : NewPayloadRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  have hp := ExecutionPayload.ssz_ofValue_toValue a.executionPayload h.1
  have hr := ExecutionRequests.ssz_ofValue_toValue a.executionRequests h.2
  constructor
  · change fromValue? (.container [ExecutionPayload.instSszSchema.toValue a.executionPayload,
      .list (a.versionedHashes.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
      .bytes a.parentBeaconBlockRoot.toBytes.toByteArray,
      ExecutionRequests.instSszSchema.toValue a.executionRequests]) = some a
    simp only [fromValue?]
    rw [hp.1]
    simp only [bind, Option.bind_some, hashes?_forward, Bytes.ofByteArray_toByteArray,
      Hash32.ofBytes?_toBytes]
    rw [hr.1]
    cases a
    simp
  · apply (SszValue.wellTyped_iff _ _).mpr
    refine ⟨rfl, ?_⟩
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp]
    refine ⟨hp.2, ?_, ?_, hr.2, by simp⟩
    · apply (SszValue.wellTyped_iff _ _).mpr
      intro v hv
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
      exact (SszValue.wellTyped_iff _ _).mpr
        (by simpa only [Bytes.size_toByteArray] using (Hash32.size_toBytes x))
    · exact (SszValue.wellTyped_iff _ _).mpr
        (by simpa only [Bytes.size_toByteArray] using (Hash32.size_toBytes
          a.parentBeaconBlockRoot))

/-- Typed successful reconstruction retains actual child validity and the whole model.
Both actual child reverse certificates receive independently derived WT and success. -/
theorem ssz_toValue_ofValue (v : SszValue) (a : NewPayloadRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v := by
  have ht := h.1
  have hs := h.2
  change fromValue? v = some a at hs
  unfold fromValue? at hs
  split at hs
  next payload hashes root requests =>
    change SszValue.WellTyped (.container [ExecutionPayload.instSszSchema.type,
      .progressiveList (.byteVector 32), .byteVector 32, ExecutionRequests.instSszSchema.type])
      (.container [payload, .list hashes, .bytes root, requests]) at ht
    have typed : SszValue.WellTyped ExecutionPayload.instSszSchema.type payload ∧
        SszValue.WellTyped (.progressiveList (.byteVector 32)) (.list hashes) ∧
        SszValue.WellTyped (.byteVector 32) (.bytes root) ∧
        SszValue.WellTyped ExecutionRequests.instSszSchema.type requests := by
      simpa [SszValue.wellTyped_iff (.container _) (.container _)] using ht
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hs
    obtain ⟨payload', hp, hashes', hh, root', hb, requests', hr, he⟩ := hs
    cases he
    have ep := ExecutionPayload.ssz_toValue_ofValue payload payload' ⟨typed.1, hp⟩
    have er := ExecutionRequests.ssz_toValue_ofValue requests requests' ⟨typed.2.2.2, hr⟩
    have eh := hashes?_preserves hashes hashes' hh
    have eb := (Hash32.ofBytes?_eq_some_iff).mp hb
    refine ⟨⟨ep.1, er.1⟩, ?_⟩
    change SszValue.container [ExecutionPayload.instSszSchema.toValue payload',
      .list (hashes'.toArray.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
      .bytes root'.toBytes.toByteArray, ExecutionRequests.instSszSchema.toValue requests'] = _
    simp only [ep.2, er.2, eh, eb.2, Bytes.toByteArray_ofByteArray]
  next => contradiction

end STFSpec.Stateless.NewPayloadRequest
