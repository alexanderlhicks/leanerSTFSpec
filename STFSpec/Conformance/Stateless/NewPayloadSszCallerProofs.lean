/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual new-payload request schema clients

Library `EthConformance`. Private facade clients preserve actual provider identities,
complete models and the exact three certificates. Count recovery and layout remain
separate from wire validity, operation support and source-host correspondence.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.NewPayloadSszCallerProofs

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

private abbrev actual : SszSchema NewPayloadRequest := NewPayloadRequest.instSszSchema

private theorem inferred : (inferInstance : SszSchema NewPayloadRequest) = actual := rfl

private theorem descriptor : actual.type = .container [ExecutionPayload.instSszSchema.type,
    .progressiveList (.byteVector 32), .byteVector 32,
    ExecutionRequests.instSszSchema.type] := rfl

private theorem names : actual.fieldNames = ["execution_payload", "versioned_hashes",
    "parent_beacon_block_root", "execution_requests"] := rfl

private theorem validity (a : NewPayloadRequest) : actual.valid a ↔
    ExecutionPayload.instSszSchema.valid a.executionPayload ∧
      ExecutionRequests.instSszSchema.valid a.executionRequests := Iff.rfl

private theorem validity_bound (a : NewPayloadRequest) : actual.valid a ↔
    a.executionPayload.extraData.size ≤ STFSpec.Fork.Amsterdam.MAX_EXTRA_DATA_BYTES := by
  change (a.executionPayload.extraData.size ≤
    STFSpec.Fork.Amsterdam.MAX_EXTRA_DATA_BYTES ∧ True) ↔ _
  simp only [and_true]

private theorem complete_model (a : NewPayloadRequest) : actual.toValue a = .container [
    ExecutionPayload.instSszSchema.toValue a.executionPayload,
    .list (a.versionedHashes.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
    .bytes a.parentBeaconBlockRoot.toBytes.toByteArray,
    ExecutionRequests.instSszSchema.toValue a.executionRequests] := rfl

private theorem wf : actual.type.WellFormed := NewPayloadRequest.ssz_type_wellFormed

private theorem forward : ∀ a : NewPayloadRequest, actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) := NewPayloadRequest.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : NewPayloadRequest),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := NewPayloadRequest.ssz_toValue_ofValue

private theorem arbitrary_construction (p : ExecutionPayload) (hs : Array VersionedHash)
    (r : Hash32) (rs : ExecutionRequests)
    (hp : ExecutionPayload.instSszSchema.valid p)
    (hr : ExecutionRequests.instSszSchema.valid rs) :
    actual.ofValue? (.container [ExecutionPayload.instSszSchema.toValue p,
      .list (hs.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
      .bytes r.toBytes.toByteArray, ExecutionRequests.instSszSchema.toValue rs]) =
      some (NewPayloadRequest.mk p hs r rs) ∧
    SszValue.WellTyped actual.type (actual.toValue (NewPayloadRequest.mk p hs r rs)) :=
  forward (NewPayloadRequest.mk p hs r rs) ⟨hp, hr⟩

private theorem recovered_reforward (v : SszValue) (a : NewPayloadRequest)
    (ht : SszValue.WellTyped actual.type v) (hs : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, hs⟩

private theorem whole_recovery (a : NewPayloadRequest) (hv : actual.valid a) :
    (actual.ofValue? (actual.toValue a)).map (fun b ↦
      (b.executionPayload, b.versionedHashes, b.parentBeaconBlockRoot, b.executionRequests)) =
      some (a.executionPayload, a.versionedHashes, a.parentBeaconBlockRoot,
        a.executionRequests) := by
  rw [(forward a hv).1]
  rfl

private theorem head_slots :
    (match actual.type with
    | .container fs => fs.map (fun f ↦ f.fixedSize?.getD 4)
    | _ => []) = [4, 4, 32, 4] := by decide

private theorem head_size : ([4, 4, 32, 4] : List Nat).sum = 44 := by decide

private theorem emitted_starts (p h r : Nat) :
    (([ExecutionPayload.instSszSchema.type, .progressiveList (.byteVector 32),
      .byteVector 32, ExecutionRequests.instSszSchema.type].zip [p, 32 * h, 32, r]).foldl
      (fun (s : Nat × List Nat) q ↦ match q.1.fixedSize? with
        | some _ => s
        | none => (s.1 + q.2, s.2 ++ [s.1])) (44, [])).2 =
      [44, 44 + p, 44 + p + 32 * h] := rfl

private theorem count_recovery (a : NewPayloadRequest) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue, NewPayloadRequest.instSszSchema,
    ExecutionPayload.instSszSchema, ExecutionRequests.instSszSchema,
    DepositRequest.instSszSchema, WithdrawalRequest.instSszSchema,
    ConsolidationRequest.instSszSchema, BuilderDepositRequest.instSszSchema,
    BuilderExitRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff (.progressiveByteList) (.bytes _),
    SszType.fixedSize?_eq (.progressiveByteList), SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _)]

end STFSpec.Conformance.Stateless.NewPayloadSszCallerProofs
