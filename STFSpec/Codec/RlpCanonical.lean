/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec.RlpDecode

/-!
# Canonical raw RLP image and wire binding

Library `EthCodec`. The inverse and binding laws retain Q47's `Encodable` domain.
Raw decoding follows locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:387–484`;
header extents follow `:487–543`. Extent-only recovery below serves arbitrary-tail
prefix binding. The decoder separately recovers a validated dependent descriptor
for ordered-child inversion. Typed/schema and pinned-host correspondence remain
separate obligations.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3,7.
-/

namespace STFSpec.Codec.Rlp
open STFSpec.Base

/-! ### Encoded first-item extent -/

/-- Short standard prefixes determine their extent with any following tail. -/
private theorem short_header (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hs : short = 128 ∨ short = 192) (hn : n < 56) :
    itemLengthModel (lengthPrefixModel short long n ++ tail) = .ok (1 + n) := by
  rw [lengthPrefixModel_short short long n hn]
  rcases hs with hs | hs
  · subst short
    have ht : (UInt8.ofNat (128 + n)).toNat = 128 + n :=
      short_tag_toNat 128 n (by change 128 + n < 256; omega)
    change itemLengthModel (UInt8.ofNat (128 + n) :: tail) = _
    simp only [itemLengthModel, ht,
      show ¬128 + n < 128 by omega, ite_false, show 128 + n ≤ 183 by omega,
      ite_true, Nat.add_sub_cancel_left]
  · subst short
    have ht : (UInt8.ofNat (192 + n)).toNat = 192 + n :=
      short_tag_toNat 192 n (by change 192 + n < 256; omega)
    change itemLengthModel (UInt8.ofNat (192 + n) :: tail) = _
    simp only [itemLengthModel, ht,
      show ¬192 + n < 128 by omega, ite_false, show ¬192 + n ≤ 183 by omega,
      show ¬192 + n ≤ 191 by omega, show 192 + n ≤ 247 by omega,
      ite_true, Nat.add_sub_cancel_left]

/-- Minimal one-to-eight-byte length digits determine long extents (rlp.py:510–543). -/
private theorem long_header (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hs : long = 183 ∨ long = 247) (hn : 56 ≤ n)
    (hw : (Uint.toBeBytes n).size ≤ 8) :
    itemLengthModel (lengthPrefixModel short long n ++ tail) =
      .ok (1 + (Uint.toBeBytes n).size + n) := by
  have hp : 0 < (Uint.toBeBytes n).size := by
    have hb := (Uint.size_toBeBytes_le_iff n 0)
    simp only [Nat.mul_zero, Nat.pow_zero] at hb
    omega
  have hh := length_digits_head n (by omega)
  have hl : ((Uint.toBeBytes n).toList ++ tail).head? ≠ some 0 := by
    cases he : (Uint.toBeBytes n).toList with
    | nil =>
      have := Bytes.length_toList (Uint.toBeBytes n)
      rw [he] at this
      simp only [List.length_nil] at this
      omega
    | cons x xs => simpa only [he, List.cons_append, List.head?_cons] using hh
  have ht : (((Uint.toBeBytes n).toList ++ tail).take (Uint.toBeBytes n).size) =
      (Uint.toBeBytes n).toList := by
    rw [← Bytes.length_toList, List.take_left]
  rw [lengthPrefixModel_long short long n hn, List.cons_append]
  rcases hs with hs | hs
  all_goals subst long
  · have hb : (UInt8.ofNat (183 + (Uint.toBeBytes n).size)).toNat =
        183 + (Uint.toBeBytes n).size := long_tag_toNat 183 n (by decide) hw
    change itemLengthModel (UInt8.ofNat (183 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail) = _
    simp only [List.cons_append, itemLengthModel, hb,
      show ¬183 + (Uint.toBeBytes n).size < 128 by omega,
      show ¬183 + (Uint.toBeBytes n).size ≤ 183 by omega, ite_false,
      show 183 + (Uint.toBeBytes n).size ≤ 191 by omega, ite_true,
      Nat.add_sub_cancel_left]
    change (if (Uint.toBeBytes n).size ≤ ((Uint.toBeBytes n).toList ++ tail).length then
      if ((Uint.toBeBytes n).toList ++ tail).head? = some 0 then _ else
        Except.ok (ε := RlpError) (1 + (Uint.toBeBytes n).size +
          Uint.ofBeBytes (Bytes.ofList
            (((Uint.toBeBytes n).toList ++ tail).take (Uint.toBeBytes n).size)))
      else _) = _
    rw [ite_eq_left (by rw [List.length_append, Bytes.length_toList]; omega),
      ite_eq_right hl, ht, Bytes.ofList_toList, Uint.ofBeBytes_toBeBytes]
  · have hb : (UInt8.ofNat (247 + (Uint.toBeBytes n).size)).toNat =
        247 + (Uint.toBeBytes n).size := long_tag_toNat 247 n (by decide) hw
    change itemLengthModel (UInt8.ofNat (247 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail) = _
    simp only [List.cons_append, itemLengthModel, hb,
      show ¬247 + (Uint.toBeBytes n).size < 128 by omega,
      show ¬247 + (Uint.toBeBytes n).size ≤ 183 by omega,
      show ¬247 + (Uint.toBeBytes n).size ≤ 191 by omega,
      show ¬247 + (Uint.toBeBytes n).size ≤ 247 by omega, ite_false,
      Nat.add_sub_cancel_left]
    change (if (Uint.toBeBytes n).size ≤ ((Uint.toBeBytes n).toList ++ tail).length then
      if ((Uint.toBeBytes n).toList ++ tail).head? = some 0 then _ else
        Except.ok (ε := RlpError) (1 + (Uint.toBeBytes n).size +
          Uint.ofBeBytes (Bytes.ofList
            (((Uint.toBeBytes n).toList ++ tail).take (Uint.toBeBytes n).size)))
      else _) = _
    rw [ite_eq_left (by rw [List.length_append, Bytes.length_toList]; omega),
      ite_eq_right hl, ht, Bytes.ofList_toList, Uint.ofBeBytes_toBeBytes]

/-- Both standard length forms recover prefix width plus payload length. -/
private theorem prefixed_header (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hs : short = 128 ∨ short = 192) (hl : long = 183 ∨ long = 247)
    (hw : (Uint.toBeBytes n).size ≤ 8) :
    itemLengthModel (lengthPrefixModel short long n ++ tail) =
      .ok ((lengthPrefixModel short long n).length + n) := by
  by_cases hn : n < 56
  · rw [short_header short long n tail hs hn,
      lengthPrefixModel_short short long n hn]
    rfl
  · rw [long_header short long n tail hl (by omega) hw,
      lengthPrefixModel_long short long n (by omega)]
    simp only [List.length_cons, Bytes.length_toList]
    congr 1
    omega

/-- Encodable item headers recover the encoded item extent independently of trailing bytes. -/
theorem itemLengthModel_encodeModel (x : RlpItem) (h : Encodable x) (tail : List UInt8) :
    itemLengthModel (encodeModel x ++ tail) = .ok (encodeModel x).length := by
  cases x with
  | bytes b =>
    unfold encodeModel
    split
    · next hb =>
      have hs : b.size = 1 := hb.1
      have hp : (b[0]?.getD 128).toNat < 128 := hb.2
      have hm : b.data.toList.length = 1 := by
        rw [Array.length_toList]
        exact hs
      cases he : b.data.toList with
      | nil => simp only [he, List.length_nil] at hm; omega
      | cons tag bs =>
        have hn : bs = [] := by
          rw [he, List.length_cons] at hm
          exact List.length_eq_zero_iff.mp (by omega)
        subst bs
        have ht : b[0]? = some tag := by
          change b.data[0]? = _
          rw [← Array.getElem?_toList, he]
          rfl
        rw [ht] at hp
        simp only [List.singleton_append, itemLengthModel, Option.getD_some] at *
        rw [ite_eq_left hp]
        rfl
    · have hw : (Uint.toBeBytes b.size).size ≤ 8 := by simpa only [Encodable] using h
      rw [List.append_assoc,
        prefixed_header 128 183 b.size (b.data.toList ++ tail)
          (Or.inl rfl) (Or.inl rfl) hw,
        List.length_append, Array.length_toList]
      rfl
  | list xs =>
    have hc : (∀ x ∈ xs, Encodable x) ∧
        (Uint.toBeBytes (encodePayloadModel xs).length).size ≤ 8 := by
      simpa only [Encodable] using h
    have hw := hc.2
    rw [encodeModel, List.append_assoc,
      prefixed_header 192 247 (encodePayloadModel xs).length
        (encodePayloadModel xs ++ tail) (Or.inr rfl) (Or.inr rfl) hw,
      List.length_append]

/-! ### Encoded prefixes and arbitrary tails -/

/-- Equal encoded prefixes with arbitrary tails have equal bytes and equal tails. -/
private theorem encodeModel_eq_and_tail_eq_of_append_eq (x y : RlpItem)
    (hx : Encodable x) (hy : Encodable y)
    (r s : List UInt8) (he : encodeModel x ++ r = encodeModel y ++ s) :
    encodeModel x = encodeModel y ∧ r = s := by
  have hh := congrArg itemLengthModel he
  rw [itemLengthModel_encodeModel x hx r, itemLengthModel_encodeModel y hy s] at hh
  have hw := Except.ok.inj hh
  have hg := congrArg (List.take (encodeModel x).length) he
  rw [List.take_left, hw, List.take_left] at hg
  refine ⟨hg, ?_⟩
  rw [hg] at he
  exact List.append_cancel_left he

/-! ### Accepted image and encoder binding -/

/-- Exact successful image, with domain membership supplied by the decoder itself. -/
theorem decode_eq_ok_iff (b : ByteArray) (x : RlpItem) :
    decode b = .ok x ↔ Encodable x ∧ encode x = b := by
  constructor
  · intro h
    exact ⟨decode_success_encodable b x h, encode_eq_of_decode_eq_ok b x h⟩
  · rintro ⟨hx, rfl⟩
    exact decode_encode x hx

/-- Accepted finite wires are precisely encodings of Encodable items. -/
theorem exists_decode_eq_ok_iff (b : ByteArray) :
    (∃ x, decode b = .ok x) ↔ ∃ x, Encodable x ∧ encode x = b := by
  simp only [decode_eq_ok_iff]

/-- The standard-domain encoder preserves every leaf, child and child order. -/
theorem eq_of_encode_eq (x y : RlpItem) (hx : Encodable x) (hy : Encodable y)
    (h : encode x = encode y) : x = y := by
  have hd := congrArg decode h
  rw [decode_encode x hx, decode_encode y hy] at hd
  exact Except.ok.inj hd

/-- Equality of standard-domain encoded bytes is equivalent to equality of items. -/
theorem encode_inj (x y : RlpItem) (hx : Encodable x) (hy : Encodable y) :
    encode x = encode y ↔ x = y := by
  constructor
  · exact eq_of_encode_eq x y hx hy
  · intro h
    exact congrArg encode h

/-- Standard RLP encodings are prefix-free even with arbitrary trailing packed bytes. -/
theorem encode_prefix_free (x y : RlpItem) (hx : Encodable x) (hy : Encodable y)
    (r s : ByteArray) (h : encode x ++ r = encode y ++ s) : x = y ∧ r = s := by
  have hl := congrArg (fun b : ByteArray ↦ b.data.toList) h
  simp only [ByteArray.toList_data_append, toList_encode] at hl
  obtain ⟨he, ht⟩ :=
    encodeModel_eq_and_tail_eq_of_append_eq x y hx hy r.data.toList s.data.toList hl
  have hd := congrArg decodeModel he
  rw [decodeModel_encodeModel x hx, decodeModel_encodeModel y hy] at hd
  refine ⟨Except.ok.inj hd, ?_⟩
  apply ByteArray.ext
  exact Array.toList_inj.mp ht

end STFSpec.Codec.Rlp
