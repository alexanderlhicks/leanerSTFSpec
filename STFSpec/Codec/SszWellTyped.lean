/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszModel

/-!
# Structural SSZ payload typing

Library `EthCodec`. Payload-only typing on every raw descriptor/value pair (Q71),
independent of schema admission, source construction and operation domains.
Source interpretation: `src/ethereum/utils/ssz.py:169–325` and eth-remerkleable 0.1.31.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

mutual
  private def wellTyped : SszType → SszValue → Prop
    | .uint width, .uint n => n < 2 ^ (8 * width)
    | .bool, .bool _ => True
    | .byteVector size, .bytes b => b.size = size
    | .byteList limit, .bytes b => b.size ≤ limit
    | .list elem limit, .list xs => xs.length ≤ limit ∧ wellTypedValues elem xs
    | .progressiveList elem, .list xs => wellTypedValues elem xs
    | .progressiveByteList, .bytes _ => True
    | .container fields, .container xs => wellTypedFields fields xs
    | .progressiveContainer _ fields, .container xs => wellTypedFields fields xs
    | _, _ => False
  private def wellTypedValues (elem : SszType) : List SszValue → Prop
    | [] => True
    | x :: xs => wellTyped elem x ∧ wellTypedValues elem xs
  private def wellTypedFields : List SszType → List SszValue → Prop
    | [], [] => True
    | field :: fields, x :: xs => wellTyped field x ∧ wellTypedFields fields xs
    | _, _ => False
end

/-- Payload-only structural typing (Q71), with mathematical ranges at every raw width.
Corresponds conditionally to `src/ethereum/utils/ssz.py:169–325`; source class admission,
actual uint256 backing counts, codec and root premises remain separate. -/
def SszValue.WellTyped : SszType → SszValue → Prop := wellTyped

private theorem wellTypedValues_iff (elem : SszType) (xs : List SszValue) :
    wellTypedValues elem xs ↔ ∀ x ∈ xs, SszValue.WellTyped elem x := by
  induction xs with
  | nil => simp only [wellTypedValues, List.not_mem_nil, false_implies, implies_true]
  | cons x xs ih =>
    simp only [wellTypedValues, ih, List.mem_cons, forall_eq_or_imp, SszValue.WellTyped]

private theorem wellTypedFields_iff (fields : List SszType) (xs : List SszValue) :
    wellTypedFields fields xs ↔ fields.length = xs.length ∧
      ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2 := by
  induction fields generalizing xs with
  | nil => cases xs <;> simp [wellTypedFields]
  | cons field fields ih =>
    cases xs with
    | nil => simp [wellTypedFields]
    | cons x xs =>
      simp only [wellTypedFields, ih, List.length_cons, Nat.succ.injEq, List.zip_cons_cons,
        List.mem_cons, forall_eq_or_imp, SszValue.WellTyped]
      exact and_left_comm

private theorem wellTyped_iff_impl (t : SszType) (v : SszValue) :
    SszValue.WellTyped t v ↔
      match t, v with
      | .uint width, .uint n => n < 2 ^ (8 * width)
      | .bool, .bool _ => True
      | .byteVector size, .bytes b => b.size = size
      | .byteList limit, .bytes b => b.size ≤ limit
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧ ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveList elem, .list xs => ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveByteList, .bytes _ => True
      | .container fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | .progressiveContainer _ fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | _, _ => False := by
  cases t <;> cases v <;>
    simp only [SszValue.WellTyped, wellTyped, wellTypedValues_iff, wellTypedFields_iff]

/-- Complete payload equation, including exact positional container arity and every unmatched tag.
Empty actual lists are vacuous; progressive masks and schema WF impose no payload premise. -/
theorem SszValue.wellTyped_iff (t : SszType) (v : SszValue) :
    SszValue.WellTyped t v ↔
      match t, v with
      | .uint width, .uint n => n < 2 ^ (8 * width)
      | .bool, .bool _ => True
      | .byteVector size, .bytes b => b.size = size
      | .byteList limit, .bytes b => b.size ≤ limit
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧ ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveList elem, .list xs =>
          ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveByteList, .bytes _ => True
      | .container fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | .progressiveContainer _ fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | _, _ => False := wellTyped_iff_impl t v

end STFSpec.Codec
