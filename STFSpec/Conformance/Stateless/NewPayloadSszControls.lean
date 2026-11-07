/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# New-payload request inverse boundary controls

Library `EthConformance`. Private finite controls cover complete outer shape, opaque
hash/root contents, every malformed hash position and delegated child failures.
Extra-data 33 distinguishes inverse completion from wire validity and typing.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.NewPayloadSszControls

open STFSpec.Stateless STFSpec.Codec

private abbrev schema := NewPayloadRequest.instSszSchema

private def filled (n : Nat) (b : UInt8 := 0) : ByteArray := ⟨Array.replicate n b⟩

private def payloadFields : List SszValue := [
  .bytes (filled 32), .bytes (filled 20), .bytes (filled 32), .bytes (filled 32),
  .bytes (filled 256), .bytes (filled 32), .uint 0, .uint 0, .uint 0, .uint 0,
  .bytes (filled 0), .uint 0, .bytes (filled 32), .list [], .list [], .uint 0,
  .uint 0, .bytes (filled 0), .uint 0]

private def requests : SszValue := .container [.list [], .list [], .list [], .list [], .list []]

private def fields : List SszValue :=
  [.container payloadFields, .list [], .bytes (filled 32), requests]

private def fails (v : SszValue) : Bool := (schema.ofValue? v).isNone

private def tags : List SszValue :=
  [.uint 0, .bool false, .bytes (filled 0), .list [], .container []]

#guard (schema.ofValue? (.container fields)).isSome
#guard (tags.take 4).all fails
#guard (List.range 4).all fun n ↦ fails (.container (fields.take n))
#guard fails (.container (fields ++ [.uint 0]))

#guard (List.range 4).all fun i ↦ tags.all fun v ↦
  match fields[i]?, v with
  | some (.container _), .container _ | some (.list _), .list _ |
    some (.bytes _), .bytes _ => true
  | _, _ => fails (.container (fields.set i v))

#guard [0, 31, 33].all fun n ↦ [0, 255].all fun b ↦
  fails (.container (fields.set 2 (.bytes (filled n b))))

private def goodHash : SszValue := .bytes (filled 32)

private def malformedHashes : List SszValue :=
  tags.filter (fun v ↦ match v with | .bytes _ => false | _ => true) ++
    [.bytes (filled 0), .bytes (filled 31), .bytes (filled 33),
      .bytes (filled 31 255), .bytes (filled 33 255)]

#guard (List.range 3).all fun i ↦ malformedHashes.all fun bad ↦
  fails (.container (fields.set 1 (.list ((List.replicate 3 goodHash).set i bad))))
#guard fails (.container (fields.set 1 (.list [goodHash, .uint 0, .bytes (filled 33)])))

-- Failure of either actual child reaches the parent without a surrogate inverse.
#guard fails (.container (fields.set 0 (.container [])))
#guard fails (.container (fields.set 3 (.container [])))
#guard fails (.container (fields.set 0 (.container (payloadFields.set 0 (.bytes (filled 31))))))
#guard fails (.container (fields.set 3 (.container [.list [.container []],
  .list [], .list [], .list [], .list []])))

mutual
  private def sameValue : SszValue → SszValue → Bool
    | .uint n, .uint m => n == m
    | .bool b, .bool c => b == c
    | .bytes b, .bytes c => b.data.toList == c.data.toList
    | .list xs, .list ys | .container xs, .container ys => sameValues xs ys
    | _, _ => false
  private def sameValues : List SszValue → List SszValue → Bool
    | [], [] => true
    | x :: xs, y :: ys => sameValue x y && sameValues xs ys
    | _, _ => false
end

private def preserves (v : SszValue) : Bool :=
  match schema.ofValue? v with
  | some a => sameValue (schema.toValue a) v
  | none => false

private def opaqueHashes : List SszValue :=
  [.bytes (filled 32), .bytes (filled 32 255),
    .bytes ((List.range 32).map UInt8.ofNat).toByteArray,
    .bytes (((List.range 32).reverse).map UInt8.ofNat).toByteArray]

#guard [[], opaqueHashes, opaqueHashes.reverse, opaqueHashes ++ opaqueHashes].all fun hs ↦
  opaqueHashes.all fun root ↦ preserves (.container [.container payloadFields,
    .list hs, root, requests])

private def extraDataControl (n : Nat) : Bool :=
  let v := SszValue.container (fields.set 0
    (.container (payloadFields.set 10 (.bytes (filled n 255)))))
  match schema.ofValue? v with
  | none => false
  | some a =>
      letI : Decidable (schema.valid a) := by
        change Decidable (a.executionPayload.extraData.size ≤ maxExtraDataBytes ∧ True)
        infer_instance
      sameValue (schema.toValue a) v &&
      a.executionPayload.extraData.data.toList == (filled n 255).data.toList &&
      decide (schema.valid a) == (n ≤ 32) &&
      (schema.ofValue? (schema.toValue a)).isSome

#guard [0, 32, 33].all extraDataControl

private theorem extraData33_not_typed : ¬ SszValue.WellTyped schema.type
    (.container (fields.set 0
      (.container (payloadFields.set 10 (.bytes (filled 33)))))) := by
  dsimp only [schema, SszSchema.type, NewPayloadRequest.instSszSchema,
    ExecutionPayload.instSszSchema, fields, payloadFields]
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    SszValue.wellTyped_iff (.byteList _) (.bytes _), filled, ByteArray.size,
    maxExtraDataBytes, STFSpec.Fork.Amsterdam.MAX_EXTRA_DATA_BYTES]

end STFSpec.Conformance.Stateless.NewPayloadSszControls
