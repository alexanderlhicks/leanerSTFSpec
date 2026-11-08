/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Whole witness schema controls

Library `EthConformance`. Private complete observations cover payload limits, ordered
bytes, independent siblings and malformed shapes. Overbound reconstruction checks the
chosen private shape-only implementation, without adding a public off-typing policy.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionWitnessSszControls

open STFSpec.Stateless STFSpec.Codec

private abbrev schema := ExecutionWitness.instSszSchema

private def valid? (a : ExecutionWitness) : Bool :=
  @decide (schema.valid a) (by
    change Decidable ((∀ b ∈ a.state.toList, b.size ≤ maxBytesPerWitnessNode) ∧
      (∀ b ∈ a.codes.toList, b.size ≤ maxBytesPerCode) ∧
      a.headers.size ≤ maxWitnessHeaders ∧
      (∀ b ∈ a.headers.toList, b.size ≤ maxBytesPerHeader))
    infer_instance)

private def observe (a : ExecutionWitness) :=
  (a.state.toList.map (fun b ↦ b.data.toList), a.codes.toList.map (fun b ↦ b.data.toList),
    a.headers.toList.map (fun b ↦ b.data.toList))

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

private def roundtrip? (a : ExecutionWitness) : Bool :=
  match schema.ofValue? (schema.toValue a) with
  | some b => observe b == observe a && sameValue (schema.toValue b) (schema.toValue a)
  | none => false

private def mixed : ExecutionWitness :=
  ⟨#[⟨#[0, 255, 1]⟩, ⟨#[]⟩, ⟨#[0, 255, 1]⟩],
    #[⟨#[128, 0]⟩, ⟨#[255]⟩], #[⟨#[5, 4]⟩, ⟨#[]⟩, ⟨#[4, 5]⟩]⟩

#guard valid? mixed && roundtrip? mixed
#guard sameValue (schema.toValue mixed) (.container [
  .list [.bytes ⟨#[0, 255, 1]⟩, .bytes ⟨#[]⟩, .bytes ⟨#[0, 255, 1]⟩],
  .list [.bytes ⟨#[128, 0]⟩, .bytes ⟨#[255]⟩],
  .list [.bytes ⟨#[5, 4]⟩, .bytes ⟨#[]⟩, .bytes ⟨#[4, 5]⟩]])
#guard (schema.ofValue? (schema.toValue mixed)).map observe ==
  some ([[0, 255, 1], [], [0, 255, 1]], [[128, 0], [255]], [[5, 4], [], [4, 5]])
#guard roundtrip? ⟨#[], #[], #[]⟩
#guard roundtrip? { mixed with state := #[⟨#[255, 0]⟩] }
#guard roundtrip? { mixed with codes := #[⟨#[]⟩, ⟨#[0, 255]⟩, ⟨#[0, 255]⟩] }
#guard roundtrip? { mixed with headers := #[⟨#[1]⟩, ⟨#[2]⟩] }

private def filled (n : Nat) : ByteArray := ⟨Array.replicate n 255⟩

-- Every boundary retains all bytes and siblings, including the overbound raw case.
#guard ([1023, 1024, 1025].map fun n ↦
  let a := { mixed with state := #[filled n] }
  (valid? a, roundtrip? a)) == [(true, true), (true, true), (false, true)]
#guard ([1023, 1024, 1025].map fun n ↦
  let a := { mixed with headers := #[filled n] }
  (valid? a, roundtrip? a)) == [(true, true), (true, true), (false, true)]
#guard ([65535, 65536, 65537].map fun n ↦
  let a := { mixed with codes := #[filled n] }
  (valid? a, roundtrip? a)) == [(true, true), (true, true), (false, true)]
#guard ([255, 256, 257].map fun n ↦
  let a := { mixed with headers := Array.replicate n ⟨#[0, 255]⟩ }
  (valid? a, roundtrip? a)) == [(true, true), (true, true), (false, true)]
private def many : ExecutionWitness := { mixed with
  state := Array.replicate 257 ⟨#[0, 255]⟩
  codes := Array.replicate 257 ⟨#[255, 0]⟩ }
#guard valid? many
#guard roundtrip? many

private def fails (v : SszValue) : Bool := (schema.ofValue? v).isNone

#guard ([SszValue.uint 0, .bool false, .bytes ⟨#[]⟩, .list []].all fails)
#guard ([SszValue.container [], .container [.list []], .container [.list [], .list []],
  .container [.list [], .list [], .list [], .list []]].all fails)
private def wrongFields : List SszValue := [.uint 0, .bool false, .bytes ⟨#[]⟩, .container []]
#guard wrongFields.all fun v ↦
  fails (.container [v, .list [], .list []]) &&
  fails (.container [.list [], v, .list []]) &&
  fails (.container [.list [], .list [], v])

private def malformedMembers : List (List SszValue) :=
  [[.uint 0, .bytes ⟨#[0, 255]⟩, .bytes ⟨#[]⟩],
    [.bytes ⟨#[0, 255]⟩, .bool false, .bytes ⟨#[]⟩],
    [.bytes ⟨#[0, 255]⟩, .bytes ⟨#[]⟩, .list []],
    [.bytes ⟨#[0, 255]⟩, .container [], .bytes ⟨#[]⟩]]

#guard malformedMembers.all fun xs ↦
  fails (.container [.list xs, .list [.bytes ⟨#[1]⟩], .list [.bytes ⟨#[2]⟩]]) &&
  fails (.container [.list [.bytes ⟨#[1]⟩], .list xs, .list [.bytes ⟨#[2]⟩]]) &&
  fails (.container [.list [.bytes ⟨#[1]⟩], .list [.bytes ⟨#[2]⟩], .list xs])

end STFSpec.Conformance.Stateless.ExecutionWitnessSszControls
