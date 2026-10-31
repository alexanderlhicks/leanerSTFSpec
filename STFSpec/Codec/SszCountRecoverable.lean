/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszFixedSize

/-!
# Actual-value SSZ count recovery

Library `EthCodec`. The local inverse premise (Q87) excludes zero-width immediate
list elements only at visited value nodes. It leaves forward support and decoder
completion separate. Source motivation: eth-remerkleable 0.1.31
`complex.py:188–220,224–242,930–962`, through `src/ethereum/utils/ssz.py:137–146`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

mutual
  private def countRecoverable : SszType → SszValue → Prop
    | .uint _, .uint _ => True
    | .bool, .bool _ => True
    | .byteVector _, .bytes _ => True
    | .byteList _, .bytes _ => True
    | .progressiveByteList, .bytes _ => True
    | .list elem _, .list xs | .progressiveList elem, .list xs =>
        elem.fixedSize? ≠ some 0 ∧ countRecoverableValues elem xs
    | .container fields, .container xs | .progressiveContainer _ fields, .container xs =>
        countRecoverableFields fields xs
    | _, _ => False
  private def countRecoverableValues (elem : SszType) : List SszValue → Prop
    | [] => True
    | x :: xs => countRecoverable elem x ∧ countRecoverableValues elem xs
  private def countRecoverableFields : List SszType → List SszValue → Prop
    | [], [] => True
    | field :: fields, x :: xs =>
        countRecoverable field x ∧ countRecoverableFields fields xs
    | _, _ => False
end

/-- Local count-recovery premise for a future SSZ inverse (Q87).
Leaves carry only tag compatibility; lists inspect immediate fixed width and actual
children; containers retain exact positional arity. No forward or decoder law is asserted. -/
def Ssz.CountRecoverable (t : SszType) (v : SszValue) : Prop := countRecoverable t v

private theorem countRecoverableValues_iff (elem : SszType) (xs : List SszValue) :
    countRecoverableValues elem xs ↔ ∀ x ∈ xs, Ssz.CountRecoverable elem x := by
  induction xs with
  | nil => simp only [countRecoverableValues, List.not_mem_nil, false_implies, implies_true]
  | cons x xs ih =>
    simp only [countRecoverableValues, ih, List.mem_cons, forall_eq_or_imp,
      Ssz.CountRecoverable]

private theorem countRecoverableFields_iff (fields : List SszType) (xs : List SszValue) :
    countRecoverableFields fields xs ↔ fields.length = xs.length ∧
      ∀ pair ∈ fields.zip xs, Ssz.CountRecoverable pair.1 pair.2 := by
  induction fields generalizing xs with
  | nil => cases xs <;> simp [countRecoverableFields]
  | cons field fields ih =>
    cases xs with
    | nil => simp [countRecoverableFields]
    | cons x xs =>
      simp only [countRecoverableFields, ih, List.length_cons, Nat.succ.injEq,
        List.zip_cons_cons, List.mem_cons, forall_eq_or_imp, Ssz.CountRecoverable]
      exact and_left_comm

/-- Complete count-recovery equation for every raw descriptor/value pair.
Empty actual lists still check their immediate element width; unused nested schemas
are not traversed. Progressive masks, leaf ranges/lengths and ordinary limits are independent. -/
theorem Ssz.countRecoverable_iff (t : SszType) (v : SszValue) :
    Ssz.CountRecoverable t v ↔
      match t, v with
      | .uint _, .uint _ => True
      | .bool, .bool _ => True
      | .byteVector _, .bytes _ => True
      | .byteList _, .bytes _ => True
      | .progressiveByteList, .bytes _ => True
      | .list elem _, .list xs | .progressiveList elem, .list xs =>
          elem.fixedSize? ≠ some 0 ∧ ∀ x ∈ xs, Ssz.CountRecoverable elem x
      | .container fields, .container xs | .progressiveContainer _ fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, Ssz.CountRecoverable pair.1 pair.2
      | _, _ => False := by
  cases t <;> cases v <;>
    simp only [Ssz.CountRecoverable, countRecoverable, countRecoverableValues_iff,
      countRecoverableFields_iff]

end STFSpec.Codec
