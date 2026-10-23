/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Bool RLP public-law callers

Library `EthConformance`. Eight private groups use only the Codec facade.
Source-class/host and first-handler premises remain separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpBoolCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp

-- 1. Complete encoder models and the arbitrary-item decoder equation.
private theorem false_model : RlpEncode.toRlp false = .bytes ByteArray.empty := rfl
private theorem true_model : RlpEncode.toRlp true = .bytes ⟨#[1]⟩ := rfl
private theorem decoder (x : RlpItem) : RlpDecode.ofRlp (α := Bool) x = toBool x := rfl

-- 2. The finite Bool domain follows from the public byte-domain characterization.
private theorem domain (b : Bool) : Encodable (RlpEncode.toRlp b) := by
  cases b <;> apply (encodable_bytes_iff _).mpr <;> decide

-- 3. The exact typed model inverse uses the public acceptance characterization.
private theorem model_inverse (b : Bool) :
    RlpDecode.ofRlp (RlpEncode.toRlp b) = .ok b := by
  apply (toBool_eq_ok_iff _ b).mpr
  cases b
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

-- 4. Arbitrary Bool callers use the unconditional public wire theorem.
private theorem inverse (b : Bool) : decodeTo (encodeOf b) = .ok b :=
  decodeTo_encodeOf_bool b

-- 5. Typed success recovers its exact model and every original wire byte.
private theorem raw_success (wire : ByteArray) (b : Bool) (h : decodeTo wire = .ok b) :
    decode wire = .ok (RlpEncode.toRlp b) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok x =>
    have ht : toBool x = .ok b := by
      unfold decodeTo at h
      rw [hd] at h
      exact h
    rcases (toBool_eq_ok_iff x b).mp ht with ⟨hx, hb⟩ | ⟨hx, hb⟩ <;>
      subst b <;> rw [hx] <;> rfl
private theorem reencode (wire : ByteArray) (b : Bool) (h : decodeTo wire = .ok b) :
    encodeOf b = wire := encode_eq_of_decode_eq_ok wire _ (raw_success wire b h)

-- 6. Both phases preserve complete results, with raw errors first.
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := Bool) wire = .error e := by unfold decodeTo; rw [h]
private theorem raw_ok (wire : ByteArray) (x : RlpItem) (h : decode wire = .ok x) :
    decodeTo (α := Bool) wire = toBool x := by unfold decodeTo; rw [h]; rfl

-- 7. Lists and invalid byte leaves retain the same existing diagnostic.
private theorem list_error (xs : List RlpItem) :
    RlpDecode.ofRlp (α := Bool) (.list xs) = .error (.shape "boolean") := rfl
private theorem bytes_error (a : ByteArray) (he : a ≠ ByteArray.empty)
    (h1 : a ≠ (⟨#[1]⟩ : ByteArray)) :
    RlpDecode.ofRlp (α := Bool) (.bytes a) = .error (.shape "boolean") := by
  change Rlp.toBool (RlpItem.bytes a) = _
  simp only [Rlp.toBool, he, h1, ↓reduceIte]

-- 8. The complete diagnostic survives; only external observation erases it.
private theorem typed_error (wire : ByteArray) (x : RlpItem)
    (hd : decode wire = .ok x) (ht : toBool x = .error (.shape "boolean")) :
    decodeTo (α := Bool) wire = .error (.shape "boolean") ∧
      (decodeTo (α := Bool) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  have h : decodeTo (α := Bool) wire = .error (.shape "boolean") := by
    rw [raw_ok wire x hd, ht]
  exact ⟨h, by rw [h]; rfl⟩

end STFSpec.Conformance.Codec.RlpBoolCallerProofs
