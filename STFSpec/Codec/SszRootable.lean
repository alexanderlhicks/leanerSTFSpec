/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszModel

/-!
# Local SSZ root support

Library `EthCodec`. Declared sizes and actual recursive payloads supply the local
root-support domain (Q78), without global well-formedness of unused composite
schemas. Source interpretation: `src/ethereum/utils/ssz.py:179–325` and
eth-remerkleable 0.1.31 `basic.py`, `complex.py`, `byte_arrays.py`, `progressive.py`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

-- Basic classification reads the width even when an actual list has no elements.
private def basicSupported : SszType → Prop
  | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
  | .bool => True
  | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
    .progressiveByteList | .container _ | .progressiveContainer _ _ => True

mutual
  private def rootable : SszType → SszValue → Prop
    | .uint w, .uint n => w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w)
    | .bool, .bool _ => True
    | .byteVector n, .bytes b => b.size = n
    | .byteList limit, .bytes b => b.size ≤ limit ∧ b.size < 2 ^ 256
    | .list elem limit, .list xs =>
        xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧
        rootableValues elem xs ∧ basicSupported elem
    | .progressiveList elem, .list xs =>
        xs.length < 2 ^ 256 ∧ rootableValues elem xs ∧ basicSupported elem
    | .progressiveByteList, .bytes b => b.size < 2 ^ 256
    | .container fields, .container xs => fields ≠ [] ∧ rootableFields fields xs
    | .progressiveContainer mask fields, .container xs =>
        mask.getLast? = some true ∧ mask.length ≤ 256 ∧
        (mask.filter id).length = fields.length ∧ rootableFields fields xs
    | _, _ => False
  private def rootableValues (elem : SszType) : List SszValue → Prop
    | [] => True
    | x :: xs => rootable elem x ∧ rootableValues elem xs
  private def rootableFields : List SszType → List SszValue → Prop
    | [], [] => True
    | field :: fields, x :: xs => rootable field x ∧ rootableFields fields xs
    | _, _ => False
end

/-- Local declared/source-shaped root support (Q78), on all raw descriptor/value
pairs. Actual nested counts fit uint256; unused composite schemas need no global
WF. This supplies neither source class admission nor a root result or decoder bridge. -/
def Ssz.Rootable (t : SszType) (v : SszValue) : Prop := rootable t v

private theorem rootableValues_iff (elem : SszType) (xs : List SszValue) :
    rootableValues elem xs ↔ ∀ x ∈ xs, Ssz.Rootable elem x := by
  induction xs with
  | nil => simp only [rootableValues, List.not_mem_nil, false_implies, implies_true]
  | cons x xs ih =>
    simp only [rootableValues, ih, List.mem_cons, forall_eq_or_imp, Ssz.Rootable]

private theorem rootableFields_iff (fields : List SszType) (xs : List SszValue) :
    rootableFields fields xs ↔ fields.length = xs.length ∧
      ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2 := by
  induction fields generalizing xs with
  | nil => cases xs <;> simp [rootableFields]
  | cons field fields ih =>
    cases xs with
    | nil => simp [rootableFields]
    | cons x xs =>
      simp only [rootableFields, ih, List.length_cons, Nat.succ.injEq, List.zip_cons_cons,
        List.mem_cons, forall_eq_or_imp, Ssz.Rootable]
      exact and_left_comm

/-- Complete local support equation, including every unmatched tag, exact positional
arity, actual recursive counts and the basic classifier even for empty lists.
Nameless mask support does not assert source class admission at capacity 256. -/
theorem Ssz.rootable_iff (t : SszType) (v : SszValue) :
    Ssz.Rootable t v ↔
      match t, v with
      | .uint w, .uint n =>
          w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w)
      | .bool, .bool _ => True
      | .byteVector n, .bytes b => b.size = n
      | .byteList limit, .bytes b =>
          b.size ≤ limit ∧ b.size < 2 ^ 256
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveList elem, .list xs =>
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveByteList, .bytes b => b.size < 2 ^ 256
      | .container fields, .container xs =>
          fields ≠ [] ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | .progressiveContainer mask fields, .container xs =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | _, _ => False := by
  cases t <;> cases v <;>
    simp only [Ssz.Rootable, rootable, rootableValues_iff, rootableFields_iff,
      basicSupported]

end STFSpec.Codec
