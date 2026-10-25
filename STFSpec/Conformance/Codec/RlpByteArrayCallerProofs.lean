/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# ByteArray RLP public-law callers

Library `EthConformance`. Eight private groups compose public laws through the
Codec facade. Source-class/host/first-handler and Q47 premises remain explicit.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpByteArrayCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp

-- 1. Every byte leaf is preserved by the public accept law.
private theorem leaf (b : ByteArray) : toBytes (.bytes b) = .ok b :=
  (toBytes_eq_ok_iff _ b).mpr rfl

-- 2. Exact model shape and complete payload characterize typed success.
private theorem adapter (x : RlpItem) (b : ByteArray) :
    RlpDecode.ofRlp (α := ByteArray) x = .ok b ↔ x = .bytes b :=
  toBytes_eq_ok_iff x b

-- 3. Arbitrary callers retain the assembled domain premise.
private theorem inverse (b : ByteArray) (h : Encodable (.bytes b)) :
    decodeTo (α := ByteArray) (encodeOf b) = .ok b := decodeTo_encodeOf_byteArray b h

-- 4. Typed success recovers the exact raw byte leaf.
private theorem raw_success (wire b : ByteArray) (h : decodeTo wire = .ok b) :
    decode wire = .ok (.bytes b) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok x =>
    have ht : toBytes x = .ok b := by
      unfold decodeTo at h
      rw [hd] at h
      exact h
    rw [(toBytes_eq_ok_iff x b).mp ht]

-- 5. Success supplies its own domain and complete payload-width bound.
private theorem success_domain (wire b : ByteArray) (h : decodeTo wire = .ok b) :
    Encodable (.bytes b) ∧ b.size < 2 ^ 64 := by
  have hd := decode_success_encodable wire _ (raw_success wire b h)
  exact ⟨hd, (encodable_bytes_iff b).mp hd⟩

-- 6. Reencoding preserves every original wire byte.
private theorem reencode (wire b : ByteArray) (h : decodeTo wire = .ok b) :
    encode (.bytes b) = wire ∧ encodeOf b = wire := by
  have he := encode_eq_of_decode_eq_ok wire _ (raw_success wire b h)
  exact ⟨he, he⟩

-- 7. A bounded local caller discharges the premise without an input guard.
private theorem bounded_inverse (b : ByteArray) (h : b.size ≤ 256) :
    decodeTo (α := ByteArray) (encodeOf b) = .ok b := by
  apply inverse
  apply (encodable_bytes_iff b).mpr
  omega

-- 8. No integer normalization: zeros remain data; lists cannot be byte success.
private theorem encode_adapter (b : ByteArray) : RlpEncode.toRlp b = .bytes b := rfl
private theorem list_not_success (xs : List RlpItem) (b : ByteArray) :
    RlpDecode.ofRlp (α := ByteArray) (.list xs) ≠ .ok b := by
  intro h
  have hshape := (adapter (.list xs) b).mp h
  contradiction

end STFSpec.Conformance.Codec.RlpByteArrayCallerProofs
