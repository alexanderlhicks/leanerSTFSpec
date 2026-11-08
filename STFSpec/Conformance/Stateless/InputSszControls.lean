/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Stateless input inverse boundaries

Library `EthConformance`. Private controls separate complete inverse reconstruction
from validity and payload typing, including both actual child failure boundaries.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.InputSszControls

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

set_option maxRecDepth 16384

private abbrev schema := StatelessInput.instSszSchema

private def filled (n : Nat) : ByteArray := ⟨Array.replicate n 255⟩

private def payloadFields : List SszValue := [
  .bytes (filled 32), .bytes (filled 20), .bytes (filled 32), .bytes (filled 32),
  .bytes (filled 256), .bytes (filled 32), .uint 0, .uint 0, .uint 0, .uint 0,
  .bytes (filled 0), .uint 0, .bytes (filled 32), .list [], .list [], .uint 0,
  .uint 0, .bytes (filled 0), .uint 0]

private def requests : SszValue := .container [.list [], .list [], .list [], .list [], .list []]

private def request (extra : Nat := 0) : SszValue := .container [
  .container (payloadFields.set 10 (.bytes (filled extra))), .list [], .bytes (filled 32),
  requests]

private def witness (n c h count : Nat) : SszValue := .container [
  .list [.bytes (filled n)], .list [.bytes (filled c)],
  .list (List.replicate count (.bytes (filled h)))]

private def fields : List SszValue := [request, witness 0 0 0 0, .uint 0]

private def fails (v : SszValue) : Bool := (schema.ofValue? v).isNone

private def tags : List SszValue :=
  [.uint 0, .bool false, .bytes (filled 0), .list [], .container []]

#guard (schema.ofValue? (.container fields)).isSome
#guard (tags.take 4).all fails
#guard (List.range 3).all fun n ↦ fails (.container (fields.take n))
#guard fails (.container (fields ++ [.uint 0]))
#guard fails (.container (fields ++ [.uint 0, .uint 0]))
#guard (List.range 3).all fun i ↦ tags.all fun v ↦
  match i, v with
  | 0, .container _ | 1, .container _ | 2, .uint _ => true
  | _, _ => fails (.container (fields.set i v))

#guard fails (.container (fields.set 0 (.container [])))
#guard fails (.container (fields.set 1 (.container [])))
#guard fails (.container (fields.set 0 (.container [.container [], .list [],
  .bytes (filled 32), requests])))
#guard fails (.container (fields.set 1 (.container [.list [.uint 0], .list [], .list []])))
#guard fails (.container [witness 0 0 0 0, request, .uint 0])
#guard fails (.container [request, request, .uint 0])
#guard fails (.container [witness 0 0 0 0, witness 0 0 0 0, .uint 0])

private def chainControl (n : Nat) : Bool :=
  match schema.ofValue? (.container (fields.set 2 (.uint n))) with
  | none => n ≥ 2 ^ 64
  | some a => n < 2 ^ 64 && a.chainId.toNat == n

#guard [0, 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 128].all chainControl

private def valid (a : StatelessInput) : Bool :=
  a.newPayloadRequest.executionPayload.extraData.size ≤ maxExtraDataBytes &&
  a.witness.state.toList.all (fun b ↦ b.size ≤ maxBytesPerWitnessNode) &&
  a.witness.codes.toList.all (fun b ↦ b.size ≤ maxBytesPerCode) &&
  a.witness.headers.size ≤ maxWitnessHeaders &&
  a.witness.headers.toList.all (fun b ↦ b.size ≤ maxBytesPerHeader)

private theorem valid_iff (a : StatelessInput) : valid a = true ↔ schema.valid a := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  dsimp only [schema, SszSchema.valid, StatelessInput.instSszSchema,
    NewPayloadRequest.instSszSchema, ExecutionPayload.instSszSchema,
    ExecutionRequests.instSszSchema, ExecutionWitness.instSszSchema]
  simp only [and_true, and_assoc]

private theorem outer_witness_typed (r w : SszValue) (c : Nat)
    (h : SszValue.WellTyped schema.type (.container [r, w, .uint c])) :
    SszValue.WellTyped ExecutionWitness.instSszSchema.type w := by
  change SszValue.WellTyped (.container [NewPayloadRequest.instSszSchema.type,
    ExecutionWitness.instSszSchema.type, .uint 8]) (.container [r, w, .uint c]) at h
  have ht : SszValue.WellTyped NewPayloadRequest.instSszSchema.type r ∧
      SszValue.WellTyped ExecutionWitness.instSszSchema.type w ∧
      SszValue.WellTyped (.uint 8) (.uint c) := by
    simpa [SszValue.wellTyped_iff (.container _) (.container _)] using h
  exact ht.2.1

private theorem outer_request_typed (r w : SszValue) (c : Nat)
    (h : SszValue.WellTyped schema.type (.container [r, w, .uint c])) :
    SszValue.WellTyped NewPayloadRequest.instSszSchema.type r := by
  change SszValue.WellTyped (.container [NewPayloadRequest.instSszSchema.type,
    ExecutionWitness.instSszSchema.type, .uint 8]) (.container [r, w, .uint c]) at h
  have ht : SszValue.WellTyped NewPayloadRequest.instSszSchema.type r ∧
      SszValue.WellTyped ExecutionWitness.instSszSchema.type w ∧
      SszValue.WellTyped (.uint 8) (.uint c) := by
    simpa [SszValue.wellTyped_iff (.container _) (.container _)] using h
  exact ht.1

private theorem over_node_not_typed : ¬ SszValue.WellTyped schema.type
    (.container [request, witness 1025 0 0 0, .uint 0]) := by
  intro h
  have hw := outer_witness_typed _ _ _ h
  dsimp only [SszSchema.type, ExecutionWitness.instSszSchema, witness] at hw
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), filled, ByteArray.size,
    maxBytesPerWitnessNode, STFSpec.Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE] at hw

private theorem over_code_not_typed : ¬ SszValue.WellTyped schema.type
    (.container [request, witness 0 65537 0 0, .uint 0]) := by
  intro h
  have hw := outer_witness_typed _ _ _ h
  dsimp only [SszSchema.type, ExecutionWitness.instSszSchema, witness] at hw
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), filled, ByteArray.size,
    maxBytesPerCode, STFSpec.Fork.Amsterdam.MAX_BYTES_PER_CODE] at hw

private theorem over_header_not_typed : ¬ SszValue.WellTyped schema.type
    (.container [request, witness 0 0 1025 1, .uint 0]) := by
  intro h
  have hw := outer_witness_typed _ _ _ h
  dsimp only [SszSchema.type, ExecutionWitness.instSszSchema, witness] at hw
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), filled, ByteArray.size,
    maxBytesPerHeader, STFSpec.Fork.Amsterdam.MAX_BYTES_PER_HEADER] at hw

private theorem over_count_not_typed : ¬ SszValue.WellTyped schema.type
    (.container [request, witness 0 0 0 257, .uint 0]) := by
  intro h
  have hw := outer_witness_typed _ _ _ h
  dsimp only [SszSchema.type, ExecutionWitness.instSszSchema, witness] at hw
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.list _ _) (.list _), maxWitnessHeaders,
    STFSpec.Fork.Amsterdam.MAX_WITNESS_HEADERS] at hw

private theorem extra_data33_not_typed : ¬ SszValue.WellTyped schema.type
    (.container [request 33, witness 0 0 0 0, .uint 0]) := by
  intro h
  have hr := outer_request_typed _ _ _ h
  dsimp only [SszSchema.type, NewPayloadRequest.instSszSchema,
    ExecutionPayload.instSszSchema, request, payloadFields] at hr
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), filled, ByteArray.size,
    maxExtraDataBytes, STFSpec.Fork.Amsterdam.MAX_EXTRA_DATA_BYTES] at hr

-- Shape-only witness inverse completion retains over-limit contents. The actual
-- validity result is compared separately; no public off-WT completion is inferred.
private def limitControl (extra n c h count : Nat) (expected : Bool) : Bool :=
  let v := SszValue.container [request extra, witness n c h count, .uint (2 ^ 64 - 1)]
  match schema.ofValue? v with
  | none => false
  | some a =>
      valid a == expected &&
      a.newPayloadRequest.executionPayload.extraData.data.toList == (filled extra).data.toList &&
      a.witness.state.toList.map (fun b ↦ b.data.toList) == [(filled n).data.toList] &&
      a.witness.codes.toList.map (fun b ↦ b.data.toList) == [(filled c).data.toList] &&
      a.witness.headers.toList.map (fun b ↦ b.data.toList) ==
        List.replicate count (filled h).data.toList &&
      (schema.ofValue? (schema.toValue a)).isSome

#guard limitControl 0 0 0 0 0 true
#guard limitControl 32 1024 65536 1024 256 true
#guard limitControl 33 0 0 0 0 false
#guard limitControl 0 1025 0 0 0 false
#guard limitControl 0 0 65537 0 0 false
#guard limitControl 0 0 0 1025 1 false
#guard limitControl 0 0 0 0 257 false
#guard limitControl 33 1025 65537 1025 257 false

end STFSpec.Conformance.Stateless.InputSszControls
