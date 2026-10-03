/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec.RlpCanonical

/-!
# Certified canonical RLP facade

These subtypes retain the core's complete recursive Encodable premises and use
its public encoder/decoder laws. A valid list is not a canonical Patricia tree.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7.
-/

namespace ToVCVio.Rlp
open STFSpec.Codec

/-- Canonical RLP domain, retaining every recursive complete payload bound. -/
abbrev ValidItem := {x : RlpItem // STFSpec.Codec.Rlp.Encodable x}

namespace ValidItem
/-- The existing packed encoder, with its standard-domain certificate. -/
def encode (x : ValidItem) : ByteArray := STFSpec.Codec.Rlp.encode x.val

/-- Decoding a certified item's complete wire recovers that item. -/
theorem decode_encode (x : ValidItem) :
    STFSpec.Codec.Rlp.decode x.encode = .ok x.val :=
  STFSpec.Codec.Rlp.decode_encode x.val x.property

/-- Successful whole-input decoding is exactly the certified encoded image. -/
theorem decode_eq_ok_iff (b : ByteArray) (x : ValidItem) :
    STFSpec.Codec.Rlp.decode b = .ok x.val ↔ x.encode = b := by
  rw [STFSpec.Codec.Rlp.decode_eq_ok_iff]
  exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩

/-- Certified items are equal exactly when their complete wires are equal. -/
theorem encode_inj (x y : ValidItem) : x.encode = y.encode ↔ x = y := by
  constructor
  · intro he
    apply Subtype.ext
    exact STFSpec.Codec.Rlp.eq_of_encode_eq _ _ x.property y.property he
  · rintro rfl; rfl

/-- Equal concatenated certified encodings determine the item and the remaining bytes. -/
theorem encode_prefix_free (x y : ValidItem) (r s : ByteArray)
    (he : x.encode ++ r = y.encode ++ s) : x = y ∧ r = s := by
  obtain ⟨hx, ht⟩ := STFSpec.Codec.Rlp.encode_prefix_free _ _ x.property y.property r s he
  exact ⟨Subtype.ext hx, ht⟩

/-- All and only accepted complete wires have a certified preimage. -/
theorem accepted_image (b : ByteArray) :
    (∃ x : RlpItem, STFSpec.Codec.Rlp.decode b = .ok x) ↔
      ∃ x : ValidItem, x.encode = b := by
  rw [STFSpec.Codec.Rlp.exists_decode_eq_ok_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x, hx⟩, he⟩
  · rintro ⟨x, he⟩
    exact ⟨x.val, x.property, he⟩

/-- All-input packed/list correspondence, restricted here only by the facade type. -/
theorem encode_toList (x : ValidItem) :
    x.encode.data.toList = STFSpec.Codec.Rlp.encodeModel x.val :=
  STFSpec.Codec.Rlp.toList_encode x.val
end ValidItem

/-- A valid RLP list; this does not assert canonical Patricia grammar. -/
abbrev RlpListNode := {x : ValidItem // ∃ xs, x.val = .list xs}

namespace RlpListNode
/-- Complete node preimage, including the outer RLP header. -/
def encode (x : RlpListNode) : ByteArray := x.val.encode

/-- The list and recursive domain certificates do not change item equality. -/
theorem eq_of_item_eq {x y : RlpListNode} (he : x.val.val = y.val.val) : x = y :=
  Subtype.ext (Subtype.ext he)

/-- Certified items are equal exactly when their complete wires are equal. -/
theorem encode_inj (x y : RlpListNode) : x.encode = y.encode ↔ x = y := by
  constructor
  · intro he
    exact Subtype.ext ((ValidItem.encode_inj _ _).mp he)
  · rintro rfl; rfl

/-- A certified list cannot be a byte-string item. -/
theorem ne_bytes (x : RlpListNode) (b : ByteArray) : x.val.val ≠ .bytes b := by
  obtain ⟨xs, hx⟩ := x.property
  rw [hx]
  intro he
  cases he
end RlpListNode
end ToVCVio.Rlp
