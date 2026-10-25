/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf
import Init.Data.List.Monadic

/-!
# Generic typed RLP lists

Library `EthCodec`. Ordered model composition and complete first-error values.
The two inverse laws retain membership-local element agreement; only the wire
law requires the complete assembled model's encoder domain (Q69).
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Preserve the complete ordered list model; locked `ethereum_rlp/rlp.py:70–78`. -/
instance {α : Type} [RlpEncode α] : RlpEncode (List α) where
  toRlp xs := .list (xs.map RlpEncode.toRlp)

/-- Check list shape before ordered child typing; locked `ethereum_rlp/rlp.py:370–384`.
Core mapM preserves the complete first supplied error as a pure result value. -/
instance {α : Type} [RlpDecode α] : RlpDecode (List α) where
  ofRlp item := (Rlp.toList item).bind
    (fun children => children.mapM (RlpDecode.ofRlp (α := α)))

/-- Lift agreement on actual members without any wire-domain premise. -/
theorem Rlp.ofRlp_toRlp_list {α : Type} [RlpEncode α] [RlpDecode α]
    (xs : List α)
    (hElements : ∀ a ∈ xs,
      RlpDecode.ofRlp (RlpEncode.toRlp a) =
        (Except.ok a : Except RlpError α)) :
    RlpDecode.ofRlp (α := List α) (RlpEncode.toRlp xs) =
      (Except.ok xs : Except RlpError (List α)) := by
  change (xs.map RlpEncode.toRlp).mapM (RlpDecode.ofRlp (α := α)) = .ok xs
  induction xs with
  | nil => simp only [List.map_nil, List.mapM_nil]; rfl
  | cons a xs ih =>
    have ha := hElements a (List.mem_cons_self)
    have ht : ∀ b ∈ xs, RlpDecode.ofRlp (RlpEncode.toRlp b) =
        (Except.ok b : Except RlpError α) :=
      fun b hb => hElements b (List.mem_cons_of_mem a hb)
    rw [List.map_cons, List.mapM_cons, ha]
    simp only [bind, Except.bind]
    rw [ih ht]
    rfl

/-- Compose member agreement with raw inversion on the whole assembled list. -/
theorem Rlp.decodeTo_encodeOf_list {α : Type} [RlpEncode α] [RlpDecode α]
    (xs : List α)
    (hElements : ∀ a ∈ xs,
      RlpDecode.ofRlp (RlpEncode.toRlp a) =
        (Except.ok a : Except RlpError α))
    (h : Rlp.Encodable (.list (xs.map RlpEncode.toRlp))) :
    Rlp.decodeTo (α := List α) (Rlp.encodeOf xs) =
      (Except.ok xs : Except RlpError (List α)) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  have hd : Rlp.Encodable (RlpEncode.toRlp xs) := h
  rw [Rlp.decode_encode _ hd]
  exact Rlp.ofRlp_toRlp_list xs hElements

end STFSpec.Codec
