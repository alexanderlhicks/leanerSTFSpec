/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Payload inverse boundary controls

Library `EthConformance`. Private controls exercise every positional tag, exact arity,
fixed-byte width, scalar range and malformed nested member. Extra-data 33 checks
raw retention and the chosen private completion without a public rejection promise.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.PayloadSszControls

open STFSpec.Stateless STFSpec.Codec

private abbrev schema := ExecutionPayload.instSszSchema

private def filled (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

private def fields : List SszValue := [
  .bytes (filled 32), .bytes (filled 20), .bytes (filled 32), .bytes (filled 32),
  .bytes (filled 256), .bytes (filled 32), .uint 0, .uint 0, .uint 0, .uint 0,
  .bytes (filled 0), .uint 0, .bytes (filled 32), .list [], .list [], .uint 0,
  .uint 0, .bytes (filled 0), .uint 0]

private def fails (v : SszValue) : Bool := (schema.ofValue? v).isNone

#guard (schema.ofValue? (.container fields)).isSome
#guard ([SszValue.uint 0, .bool false, .bytes (filled 0), .list []].all fails)
#guard ((List.range 19).all fun n ↦ fails (.container (fields.take n)))
#guard fails (.container (fields ++ [.uint 0]))

private def wrongTags : List SszValue :=
  [.uint 0, .bool false, .bytes (filled 0), .list [], .container []]

-- Each field is tested against all incompatible tags, without dropping siblings.
#guard (List.range 19).all fun i ↦ wrongTags.all fun v ↦
  match fields[i]?, v with
  | some (.bytes _), .bytes _ | some (.uint _), .uint _ | some (.list _), .list _ => true
  | _, _ => fails (.container (fields.set i v))

#guard ([(0, 32), (1, 20), (2, 32), (3, 32), (4, 256), (5, 32), (12, 32)]).all
  fun (i, width) ↦ [0, width - 1, width + 1].all fun n ↦
    fails (.container (fields.set i (.bytes (filled n))))

#guard ([6, 7, 8, 9, 15, 16, 18].all fun i ↦
  fails (.container (fields.set i (.uint (2 ^ 64)))))
#guard fails (.container (fields.set 11 (.uint (2 ^ 256))))
#guard ([6, 7, 8, 9, 15, 16, 18].all fun i ↦
  (schema.ofValue? (.container (fields.set i (.uint (2 ^ 64 - 1))))).isSome)
#guard (schema.ofValue? (.container (fields.set 11 (.uint (2 ^ 256 - 1))))).isSome

private def malformed : List SszValue :=
  [.uint 0, .bool false, .list [], .container [], .bytes (filled 0)]

#guard (malformed.take 4).all fun v ↦
  fails (.container (fields.set 13 (.list [.bytes (filled 0), v, .bytes (filled 1)])))
#guard malformed.all fun v ↦
  fails (.container (fields.set 14 (.list [v])))
#guard fails (.container (fields.set 14 (.list [
  .container [.uint (2 ^ 64), .uint 0, .bytes (filled 20), .uint 0]])))
#guard fails (.container (fields.set 14 (.list [
  .container [.uint 0, .uint 0, .bytes (filled 19), .uint 0]])))

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

private def extraDataControl (n : Nat) : Bool :=
  match schema.ofValue? (.container (fields.set 10 (.bytes (filled n)))) with
  | none => false
  | some a =>
      sameValue (schema.toValue a) (.container (fields.set 10 (.bytes (filled n)))) &&
      a.extraData.data.toList == (filled n).data.toList &&
      decide (a.extraData.size ≤ maxExtraDataBytes) == (n ≤ 32) &&
      (schema.ofValue? (schema.toValue a)).isSome

#guard [0, 32, 33].all extraDataControl

end STFSpec.Conformance.Stateless.PayloadSszControls
