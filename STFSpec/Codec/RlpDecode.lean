/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpHeader

/-!
# Total raw RLP cursor decoding

Library `EthCodec`. Locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:143–162,385–543`.
Every recursive window stays inside the original input. Only successful byte leaves
are copied; list payloads and child windows are never copied. Mathematical totality
is independent of host stack/allocation limits (Q20, O12). Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7. Wire canonicality
and the Encodable inverse/prefix-free contracts are separate pending obligations.
-/

namespace STFSpec.Codec.Rlp

open STFSpec.Base

-- A packed reader and a proof-facing list reader instantiate the same semantics.
-- Both callbacks are used only inside a previously validated scope.
private structure Input where
  byte : Nat → UInt8
  leaf : Nat → Nat → ByteArray

private def packedInput (b : ByteArray) : Input :=
  ⟨fun i ↦ b[i]?.getD 0,
    fun start stop ↦ ((Bytes.ofByteArray b).extract start stop).toByteArray⟩

private def listInput (xs : List UInt8) : Input :=
  ⟨fun i ↦ xs[i]?.getD 0, fun start stop ↦ ((xs.drop start).take (stop - start)).toByteArray⟩

private def digits (input : Input) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | count + 1, pos, acc => digits input count (pos + 1) (256 * acc + (input.byte pos).toNat)

private structure Header (pos stop : Nat) where
  isList : Bool
  isSingle : Bool
  isLong : Bool
  payload : Nat
  start : Nat
  advances : pos < start
  available : start ≤ stop

-- This helper is permissive, like decode_item_length: no body or short/long-form check.
private def header (input : Input) (pos stop : Nat) : Except RlpError (Header pos stop) :=
  if hp : pos < stop then
    let tag := (input.byte pos).toNat
    if hs : tag < 128 then .ok ⟨false, true, false, 0, pos + 1, by omega, by omega⟩ else
    if hb : tag ≤ 183 then .ok ⟨false, false, false, tag - 128, pos + 1, by omega, by omega⟩ else
    if hl : tag ≤ 191 then
      let count := tag - 183
      if ha : pos + 1 + count ≤ stop then
        if input.byte (pos + 1) = 0 then .error (.nonCanonical "leading zero length") else
          .ok ⟨false, false, true, digits input count (pos + 1) 0,
            pos + 1 + count, by omega, ha⟩
      else .error .truncated
    else if hl : tag ≤ 247 then
      .ok ⟨true, false, false, tag - 192, pos + 1, by omega, by omega⟩
    else
      let count := tag - 247
      if ha : pos + 1 + count ≤ stop then
        if input.byte (pos + 1) = 0 then .error (.nonCanonical "leading zero length") else
          .ok ⟨true, false, true, digits input count (pos + 1) 0,
            pos + 1 + count, by omega, ha⟩
      else .error .truncated
  else .error .empty

mutual
  private def item (input : Input) (pos stop : Nat) : Except RlpError RlpItem :=
    match header input pos stop with
    | .error e => .error e
    | .ok h =>
      if h.isSingle then
        if stop = pos + 1 then .ok (.bytes (input.leaf pos stop)) else
          .error (.nonCanonical "negative length")
      else if h.isLong && h.payload < 56 then .error (.nonCanonical "long form for short payload") else
      if _he : h.start + h.payload > stop then .error .truncated else
      if h.start + h.payload < stop then .error .trailing else
      if h.isList then
        match joined input h.start stop [] with
        | .error e => .error e
        | .ok xs => .ok (.list xs)
      else if h.payload = 1 && (input.byte h.start).toNat < 128 then
        .error (.nonCanonical "prefixed single byte")
      else .ok (.bytes (input.leaf h.start stop))
  termination_by 2 * (stop - pos)
  decreasing_by have := h.advances; have := h.available; omega

  private def joined (input : Input) (pos stop : Nat) (rev : List RlpItem) :
      Except RlpError (List RlpItem) :=
    if _hp : pos < stop then
      match header input pos stop with
      | .error e => .error e
      | .ok h =>
        if _he : h.start + h.payload ≤ stop then
          match item input pos (h.start + h.payload) with
          | .error e => .error e
          | .ok x => joined input (h.start + h.payload) stop (x :: rev)
        else .error .truncated
    else .ok rev.reverse
  termination_by 2 * (stop - pos) + 1
  decreasing_by
    all_goals have := h.advances; have := h.available; omega
end

/-- Readable byte-list instantiation of the bounded cursor semantics. It preserves
whole byte/list trees and ordered diagnostics; it is proof-facing, not the packed
implementation. The full universal canonicality and inverse laws remain pending. -/
def decodeModel (xs : List UInt8) : Except RlpError RlpItem := item (listInput xs) 0 xs.length

/-- Pure total raw decoder, locked `rlp.py:143–162,385–484`. All extents use Nat;
child headers are observed before their declared extent is checked against the
parent window. No declared-length allocation precedes that check. -/
def decode (b : ByteArray) : Except RlpError RlpItem := item (packedInput b) 0 b.size

private theorem packedInput_eq_listInput (b : ByteArray) :
    packedInput b = listInput b.data.toList := by
  unfold packedInput listInput
  congr 1
  · funext i
    rw [Array.getElem?_toList]
    by_cases h : i < b.size
    · simp only [getElem?_pos b i h, Array.getElem?_eq_getElem (show i < b.data.size from h)]
      rfl
    · simp only [getElem?_neg b i h, Array.getElem?_eq_none (show b.data.size ≤ i from Nat.le_of_not_lt h)]
  · funext start stop
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [Bytes.toList_toByteArray, Bytes.toList_extract, Bytes.toList_ofByteArray,
      List.toList_data_toByteArray]

/-- Packed execution equals the readable list model on every finite input,
including complete diagnostics and the whole nested result. -/
theorem decode_eq_model (b : ByteArray) : decode b = decodeModel b.data.toList := by
  unfold decode decodeModel
  rw [packedInput_eq_listInput, Array.length_toList]
  rfl

/-- Empty input fails before reading a tag. -/
theorem decode_empty : decode ByteArray.empty = .error .empty := by
  rw [decode, item, header]
  rfl

/-- Extracted public byte windows have the exact list-window semantics. This
storage correspondence includes empty/clipped and conceptual large offsets. -/
theorem decode_window_model (b : ByteArray) (start stop : Nat) :
    decode ((Bytes.ofByteArray b).extract start stop).toByteArray =
      decodeModel ((b.data.toList.drop start).take (stop - start)) := by
  rw [decode_eq_model, Bytes.toList_toByteArray, Bytes.toList_extract,
    Bytes.toList_ofByteArray]

private theorem header_single (input : Input) (pos stop : Nat) (hp : pos < stop)
    (h : (input.byte pos).toNat < 128) :
    header input pos stop = .ok ⟨false, true, false, 0, pos + 1, by omega, by omega⟩ := by
  unfold header
  rw [dite_eq_left hp, dite_eq_left h]

/-- A literal low byte is accepted only as an exact singleton. -/
theorem decodeModel_single (tag : UInt8) (body : List UInt8) (h : tag.toNat < 128) :
    decodeModel (tag :: body) =
      if body = [] then .ok (.bytes [tag].toByteArray) else
        .error (.nonCanonical "negative length") := by
  unfold decodeModel
  rw [item, header_single _ _ _ (by simp) (by exact h)]
  change (if body.length + 1 = 1 then
    Except.ok (RlpItem.bytes (((tag :: body).drop 0).take (body.length + 1)).toByteArray) else _) = _
  cases body with
  | nil => rfl
  | cons x xs => simp only [List.length_cons, Nat.add_eq_right,
      Nat.add_one_ne_zero, ite_false, List.cons_ne_nil]

/-- A packed exact singleton below 0x80 preserves its byte leaf. -/
theorem decode_single (b : ByteArray) (tag : UInt8) (hs : b.size = 1)
    (ht : b[0]? = some tag) (h : tag.toNat < 128) : decode b = .ok (.bytes b) := by
  rw [decode_eq_model]
  have hm : b.data.toList = [tag] := by
    apply List.ext_getElem
    · simpa only [Array.length_toList, ← ByteArray.size_data, List.length_singleton] using hs
    · intro i hi hj
      have hz : i = 0 := by simp only [List.length_singleton] at hj; omega
      subst i
      have hp : 0 < b.size := by omega
      rw [getElem?_pos b 0 hp] at ht
      simpa only [List.getElem_cons_zero, Array.getElem_toList,
        ← ByteArray.getElem_eq_getElem_data] using Option.some.inj ht
  rw [hm, decodeModel_single tag [] h, ite_eq_left rfl]
  congr 2
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray, hm]

/-- The short-string equation exposes source failure priority: extent truncation,
trailing bytes, then a noncanonical prefixed low singleton. -/
theorem decodeModel_short_bytes (tag : UInt8) (body : List UInt8)
    (lo : 128 ≤ tag.toNat) (hi : tag.toNat ≤ 183) :
    decodeModel (tag :: body) =
      if tag.toNat - 128 > body.length then .error .truncated else
      if tag.toNat - 128 < body.length then .error .trailing else
      if tag.toNat - 128 = 1 && (body[0]?.getD 0).toNat < 128 then
        .error (.nonCanonical "prefixed single byte") else .ok (.bytes body.toByteArray) := by
  have hh : header (listInput (tag :: body)) 0 (tag :: body).length =
      .ok ⟨false, false, false, tag.toNat - 128, 1, by omega, by simp⟩ := by
    unfold header
    rw [dite_eq_left (by simp)]
    change (if _ : tag.toNat < 128 then _ else _) = _
    rw [dite_eq_right (by omega)]
    rw [dite_eq_left (show ((listInput (tag :: body)).byte 0).toNat ≤ 183 from hi)]
    rfl
  unfold decodeModel
  rw [item, hh]
  dsimp only
  simp only [Bool.false_eq_true, Bool.false_and, ite_false]
  simp only [listInput, List.length_cons, List.getElem?_cons_succ,
    List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel_right, List.take_length]
  have ht : (1 + (tag.toNat - 128) > body.length + 1) =
      (tag.toNat - 128 > body.length) := propext (by omega)
  have hl : (1 + (tag.toNat - 128) < body.length + 1) =
      (tag.toNat - 128 < body.length) := propext (by omega)
  simp only [ht, hl, dite_eq_ite]
  rfl

private theorem header_short_list (tag : UInt8) (body : List UInt8)
    (lo : 192 ≤ tag.toNat) (hi : tag.toNat ≤ 247) :
    header (listInput (tag :: body)) 0 (tag :: body).length =
      .ok ⟨true, false, false, tag.toNat - 192, 1, by omega, by simp⟩ := by
  unfold header
  rw [dite_eq_left (by simp)]
  change (if _ : tag.toNat < 128 then _ else _) = _
  rw [dite_eq_right (by omega)]
  rw [dite_eq_right (show ¬((listInput (tag :: body)).byte 0).toNat ≤ 183 from (by omega : ¬tag.toNat ≤ 183))]
  rw [dite_eq_right (show ¬((listInput (tag :: body)).byte 0).toNat ≤ 191 from (by omega : ¬tag.toNat ≤ 191))]
  rw [dite_eq_left (show ((listInput (tag :: body)).byte 0).toNat ≤ 247 from hi)]
  rfl

/-- A short list's truncated outer extent wins before inspecting any child. -/
theorem decodeModel_short_list_truncated (tag : UInt8) (body : List UInt8)
    (lo : 192 ≤ tag.toNat) (hi : tag.toNat ≤ 247)
    (he : body.length < tag.toNat - 192) :
    decodeModel (tag :: body) = .error .truncated := by
  unfold decodeModel
  rw [item, header_short_list tag body lo hi]
  dsimp only
  simp only [Bool.false_eq_true, Bool.false_and, ite_false]
  rw [dite_eq_left (by simp only [List.length_cons]; omega)]

/-- A short list's trailing bytes win before inspecting any child. -/
theorem decodeModel_short_list_trailing (tag : UInt8) (body : List UInt8)
    (lo : 192 ≤ tag.toNat) (hi : tag.toNat ≤ 247)
    (he : tag.toNat - 192 < body.length) :
    decodeModel (tag :: body) = .error .trailing := by
  unfold decodeModel
  rw [item, header_short_list tag body lo hi]
  dsimp only
  simp only [Bool.false_eq_true, Bool.false_and, ite_false]
  rw [dite_eq_right (by simp only [List.length_cons]; omega)]
  rw [ite_eq_left (by simp only [List.length_cons]; omega)]

/-- A successful full decode consumed a nonempty input. The private advancing
header witnesses also establish strict decrease for every recursive continuation. -/
theorem decode_success_nonempty (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) :
    0 < b.size := by
  by_cases hn : 0 < b.size
  · exact hn
  have hz : b.size = 0 := by omega
  have hm : b.data.toList = [] := List.length_eq_zero_iff.mp (by
    rw [Array.length_toList]
    exact hz)
  rw [decode_eq_model, hm] at h
  rw [decodeModel, item, header] at h
  simp only [List.length_nil, dite_eq_right (Nat.lt_irrefl 0)] at h
  cases h

end STFSpec.Codec.Rlp
