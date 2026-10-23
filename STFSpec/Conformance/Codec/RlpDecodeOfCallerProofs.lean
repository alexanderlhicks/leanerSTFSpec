/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Typed RLP decoding public-law callers

Library `EthConformance`. Eight private client groups use the Codec facade.
Only new adapters reduce; raw/leaf/Base operations use public laws. Pure callback
results give no effect trace or invocation-count claim. Q20/O12/D14 remain local
source/host/first-handler obligations, including the intended source class.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpDecodeOfCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance


-- 1. Whole equation and independent classes.
private theorem wrapper {α : Type} [RlpDecode α] (b : ByteArray) :
    decodeTo (α := α) b = match decode b with
      | .error e => .error e
      | .ok x => RlpDecode.ofRlp x := rfl

private structure DecodeOnly where
  value : Nat
private instance : RlpDecode DecodeOnly where
  ofRlp _ := .ok ⟨7⟩
private theorem decode_only (b : ByteArray) :
    decodeTo (α := DecodeOnly) b = match decode b with
      | .error e => .error e
      | .ok _ => .ok ⟨7⟩ := rfl
private structure EncodeOnly where
  value : Nat
private instance : RlpEncode EncodeOnly where
  toRlp a := ofNat a.value
private theorem encode_only (a : EncodeOnly) : encodeOf a = encode (ofNat a.value) := rfl

-- 2. Raw failure retains the whole arbitrary diagnostic.
private theorem raw_failure {α : Type} [RlpDecode α] (b : ByteArray) (e : RlpError)
    (h : decode b = .error e) : decodeTo (α := α) b = .error e := by
  rw [wrapper, h]

-- 3. Whole typed forwarding, including arbitrary success and error values.
private theorem typed_result {α : Type} [RlpDecode α] (b : ByteArray) (x : RlpItem)
    (r : Except RlpError α) (h : decode b = .ok x) (ht : RlpDecode.ofRlp x = r) :
    decodeTo b = r := by rw [wrapper, h]; exact ht
private theorem typed_error {α : Type} [RlpDecode α] (b : ByteArray) (x : RlpItem)
    (e : RlpError) (h : decode b = .ok x)
    (ht : RlpDecode.ofRlp x = (.error e : Except RlpError α)) :
    decodeTo (α := α) b = .error e := typed_result b x _ h ht
private theorem typed_success {α : Type} [RlpDecode α] (b : ByteArray) (x : RlpItem)
    (a : α) (h : decode b = .ok x) (ht : RlpDecode.ofRlp x = .ok a) :
    decodeTo b = .ok a := typed_result b x _ h ht

-- 4. Both actual premises are necessary; classes alone give no inverse law.
private theorem inverse {α : Type} [RlpEncode α] [RlpDecode α] (a : α)
    (hi : RlpDecode.ofRlp (RlpEncode.toRlp a) = .ok a)
    (hd : Encodable (RlpEncode.toRlp a)) : decodeTo (encodeOf a) = .ok a := by
  apply typed_result _ _ _ (decode_encode _ hd) hi
private structure Collapsed where
  value : Nat
private instance : RlpEncode Collapsed where
  toRlp _ := ofNat 0
private instance : RlpDecode Collapsed where
  ofRlp _ := .ok ⟨0⟩
private theorem collapsed_domain : Encodable (RlpEncode.toRlp (Collapsed.mk 1)) := by
  have shape : RlpItem.bytes (Uint.toBeBytes 0).toByteArray = ofNat 0 :=
    (toNat_eq_ok_iff _ 0).mp (toNat_ofNat 0)
  rw [show RlpEncode.toRlp (Collapsed.mk 1) = ofNat 0 from rfl, ← shape,
    encodable_bytes_iff, Bytes.size_toByteArray, Uint.toBeBytes_zero, Bytes.size_empty]
  decide
private theorem classes_not_inverse :
    decodeTo (α := Collapsed) (encodeOf (Collapsed.mk 1)) ≠ .ok ⟨1⟩ := by
  have hw : decode (encodeOf (Collapsed.mk 1)) = .ok (ofNat 0) :=
    decode_encode _ collapsed_domain
  rw [wrapper, hw]
  change (Except.ok (Collapsed.mk 0) : Except RlpError Collapsed) ≠ .ok ⟨1⟩
  intro he
  have hn : (0 : Nat) = 1 := congrArg Collapsed.value (Except.ok.inj he)
  omega

-- 5. Exact Nat adapter and public conditional law.
private theorem nat_adapter (x : RlpItem) : RlpDecode.ofRlp (α := Nat) x = toNat x := rfl
private theorem nat_inverse (n : Nat) (h : Encodable (ofNat n)) :
    decodeTo (α := Nat) (encodeOf n) = .ok n := decodeTo_encodeOf_nat n h

-- 6. A local bounded caller discharges, rather than removes, the premise.
private theorem bounded_domain (n : Nat) (h : n < 2 ^ 256) : Encodable (ofNat n) := by
  have shape : RlpItem.bytes (Uint.toBeBytes n).toByteArray = ofNat n :=
    (toNat_eq_ok_iff _ n).mp ((toNat_canonical_iff _ n).mpr rfl)
  rw [← shape, encodable_bytes_iff, Bytes.size_toByteArray]
  have width : (Uint.toBeBytes n).size ≤ 32 := (Uint.size_toBeBytes_le_iff _ _).mpr h
  omega
private theorem bounded_inverse (n : Nat) (h : n < 2 ^ 256) :
    decodeTo (α := Nat) (encodeOf n) = .ok n := nat_inverse n (bounded_domain n h)

-- 7. Successful Nat decoding recovers both its domain and the exact input wire.
private theorem successful_nat (b : ByteArray) (n : Nat) (h : decodeTo b = .ok n) :
    Encodable (ofNat n) ∧ encodeOf n = b := by
  cases hd : decode b with
  | error e => rw [wrapper, hd] at h; contradiction
  | ok x =>
    have ht : toNat x = .ok n := by
      have ht := h
      rw [wrapper, hd] at ht
      exact ht
    have hx := (toNat_eq_ok_iff x n).mp ht
    subst x
    exact ⟨decode_success_encodable b _ hd, encode_eq_of_decode_eq_ok b _ hd⟩

-- 8. A local observation composes outside the wrapper and exports no projection.
private theorem observation {α : Type} [RlpDecode α] (b : ByteArray) :
    (decodeTo (α := α) b).mapError (fun (_ : RlpError) => ()) =
      (match decode b with
       | .error e => (.error e : Except RlpError α)
       | .ok x => RlpDecode.ofRlp x).mapError (fun (_ : RlpError) => ()) := rfl

end STFSpec.Conformance.Codec.RlpDecodeOfCallerProofs
