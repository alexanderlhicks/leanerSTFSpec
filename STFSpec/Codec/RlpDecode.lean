/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpHeader
import STFSpec.Codec.RlpEncode

/-!
# Total raw RLP cursor decoding

Library `EthCodec`. Locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:143–162,387–543`.
Every recursive window stays inside the original input. Only successful byte leaves
are copied; list payloads and child windows are never copied. Mathematical totality
is independent of host stack/allocation limits (Q20, O12). Successful-wire
laws are listed in EthCodec §7. Proofs remain beside the parser to reason about
its private bounded cursors; consumers use the public laws.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
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
implementation. Its public laws are owned by EthCodec §7. -/
def decodeModel (xs : List UInt8) : Except RlpError RlpItem := item (listInput xs) 0 xs.length

/-- Pure total raw decoder, locked `rlp.py:143–162,387–484`. All extents use Nat;
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

/-! ### Scoped observation congruence -/

/-- Equal observations in a validated digit window give equal complete folds. -/
private theorem digits_congr (a b : Input) (pos count stop acc : Nat)
    (hc : pos + count ≤ stop)
    (hb : ∀ i, pos ≤ i → i < stop → a.byte i = b.byte i) :
    digits a count pos acc = digits b count pos acc := by
  induction count generalizing pos acc with
  | zero => rfl
  | succ count ih =>
    rw [digits, digits, hb pos (by omega) (by omega)]
    apply ih (pos + 1) _ (by omega)
    intro i hi he
    exact hb i (by omega) he

/-- Header classification observes only bytes inside its validated scope. -/
private theorem header_congr (a b : Input) (pos stop : Nat)
    (hb : ∀ i, pos ≤ i → i < stop → a.byte i = b.byte i) :
    header a pos stop = header b pos stop := by
  by_cases hp : pos < stop
  · have ht := hb pos (by omega) hp
    by_cases hs : (b.byte pos).toNat < 128
    · simp only [header, dite_eq_left hp, ht, dite_eq_left hs]
    · by_cases hs' : (b.byte pos).toNat ≤ 183
      · simp only [header, dite_eq_left hp, ht, dite_eq_right hs, dite_eq_left hs']
      · by_cases hl : (b.byte pos).toNat ≤ 191
        · by_cases ha : pos + 1 + ((b.byte pos).toNat - 183) ≤ stop
          · have hz := hb (pos + 1) (by omega) (by omega)
            have hd := digits_congr a b (pos + 1) _ stop 0 ha
              (fun i hi he ↦ hb i (by omega) he)
            simp only [header, dite_eq_left hp, ht, dite_eq_right hs,
              dite_eq_right hs', dite_eq_left hl, dite_eq_left ha, hz, hd]
          · simp only [header, dite_eq_left hp, ht, dite_eq_right hs,
              dite_eq_right hs', dite_eq_left hl, dite_eq_right ha]
        · by_cases hl' : (b.byte pos).toNat ≤ 247
          · simp only [header, dite_eq_left hp, ht, dite_eq_right hs,
              dite_eq_right hs', dite_eq_right hl, dite_eq_left hl']
          · by_cases ha : pos + 1 + ((b.byte pos).toNat - 247) ≤ stop
            · have hz := hb (pos + 1) (by omega) (by omega)
              have hd := digits_congr a b (pos + 1) _ stop 0 ha
                (fun i hi he ↦ hb i (by omega) he)
              simp only [header, dite_eq_left hp, ht, dite_eq_right hs,
                dite_eq_right hs', dite_eq_right hl, dite_eq_right hl',
                dite_eq_left ha, hz, hd]
            · simp only [header, dite_eq_left hp, ht, dite_eq_right hs,
                dite_eq_right hs', dite_eq_right hl, dite_eq_right hl',
                dite_eq_right ha]
  · simp only [header, dite_eq_right hp]

mutual
  /-- Exact scoped observation equality preserves every item result and diagnostic. -/
  private theorem item_congr (a b : Input) (pos stop : Nat)
      (hb : ∀ i, pos ≤ i → i < stop → a.byte i = b.byte i)
      (hl : ∀ start endPos, pos ≤ start → start ≤ endPos → endPos ≤ stop →
        a.leaf start endPos = b.leaf start endPos) (hp : pos ≤ stop) :
      item a pos stop = item b pos stop := by
    rw [item, item, header_congr a b pos stop hb]
    cases hh : header b pos stop with
    | error e => rfl
    | ok h =>
      simp only
      split
      · split
        · rw [hl pos stop (by omega) hp (by omega)]
        · rfl
      · split
        · rfl
        · split
          · rfl
          · next he =>
            split
            · rfl
            · next ht =>
              split
              · rw [joined_congr a b h.start stop []]
                · intro i hi he
                  exact hb i (by have := h.advances; omega) he
                · intro s e hs he he'
                  exact hl s e (by have := h.advances; omega) he he'
                · exact h.available
              · by_cases hn : h.payload = 1
                · have hs : h.start < stop := by omega
                  rw [hb h.start (by have := h.advances; omega) hs]
                  rw [hl h.start stop (by have := h.advances; omega) h.available (by omega)]
                · simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
                  rw [hl h.start stop (by have := h.advances; omega) h.available (by omega)]
  termination_by 2 * (stop - pos)
  decreasing_by have := h.advances; have := h.available; omega
  /-- Scoped equality also preserves joined children and their original order. -/
  private theorem joined_congr (a b : Input) (pos stop : Nat) (rev : List RlpItem)
      (hb : ∀ i, pos ≤ i → i < stop → a.byte i = b.byte i)
      (hl : ∀ start endPos, pos ≤ start → start ≤ endPos → endPos ≤ stop →
        a.leaf start endPos = b.leaf start endPos) (_hp : pos ≤ stop) :
      joined a pos stop rev = joined b pos stop rev := by
    rw [joined, joined]
    split
    · next hp =>
      rw [header_congr a b pos stop hb]
      cases hh : header b pos stop with
      | error e => rfl
      | ok h =>
        simp only
        split
        · next he =>
          rw [item_congr a b pos (h.start + h.payload)]
          · cases hx : item b pos (h.start + h.payload) with
            | error e => rfl
            | ok x =>
              simp only
              apply joined_congr a b (h.start + h.payload) stop (x :: rev)
              · intro i hi he'
                exact hb i (by have := h.advances; omega) he'
              · intro s e hs he' he''
                exact hl s e (by have := h.advances; omega) he' he''
              · exact he
          · intro i hi he'
            exact hb i hi (by omega)
          · intro s e hs he' he''
            exact hl s e hs he' (by omega)
          · have := h.advances
            omega
        · rfl
    · rfl
  termination_by 2 * (stop - pos) + 1
  decreasing_by all_goals have := h.advances; have := h.available; omega
end

/-! ### Cursor translation -/

/-- Translate callbacks while retaining the same original storage. -/
private def Input.shift (input : Input) (offset : Nat) : Input :=
  ⟨fun i ↦ input.byte (i + offset), fun p e ↦ input.leaf (p + offset) (e + offset)⟩

/-- Translated input reads preserve the original byte observation. -/
private theorem Input.byte_shift (input : Input) (offset pos : Nat) :
    (input.shift offset).byte pos = input.byte (pos + offset) := rfl

/-- Translate a validated descriptor; no new header interpretation is introduced. -/
private def Header.shift {pos stop : Nat} (h : Header pos stop) (offset : Nat) :
    Header (pos + offset) (stop + offset) :=
  ⟨h.isList, h.isSingle, h.isLong, h.payload, h.start + offset,
    by have := h.advances; omega, by have := h.available; omega⟩

/-- Digit accumulation commutes with translation of the validated input window. -/
private theorem digits_shift (input : Input) (offset count pos acc : Nat) :
    digits (input.shift offset) count pos acc = digits input count (pos + offset) acc := by
  induction count generalizing pos acc with
  | zero => rfl
  | succ count ih =>
    rw [digits, digits, ih]
    simp only [Input.shift]
    congr 1
    omega

/-- Short string classification at an arbitrary available cursor. -/
private theorem header_short_bytes_at (input : Input) (pos stop : Nat)
    (hp : pos < stop) (lo : 128 ≤ (input.byte pos).toNat) (hi : (input.byte pos).toNat ≤ 183) :
    header input pos stop =
      .ok ⟨false, false, false, (input.byte pos).toNat - 128, pos + 1, by omega, by omega⟩ := by
  simp only [header, dite_eq_left hp, dite_eq_right (by omega : ¬(input.byte pos).toNat < 128),
    dite_eq_left hi]

/-- Short list classification at an arbitrary available cursor. -/
private theorem header_short_list_at (input : Input) (pos stop : Nat)
    (hp : pos < stop) (lo : 192 ≤ (input.byte pos).toNat) (hi : (input.byte pos).toNat ≤ 247) :
    header input pos stop =
      .ok ⟨true, false, false, (input.byte pos).toNat - 192, pos + 1, by omega, by omega⟩ := by
  simp only [header, dite_eq_left hp, dite_eq_right (by omega : ¬(input.byte pos).toNat < 128),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 183),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 191), dite_eq_left hi]

/-- Long string classification at an arbitrary available cursor. -/
private theorem header_long_bytes_at (input : Input) (pos stop : Nat)
    (hp : pos < stop) (lo : 184 ≤ (input.byte pos).toNat) (hi : (input.byte pos).toNat ≤ 191) :
    header input pos stop = if ha : pos + 1 + ((input.byte pos).toNat - 183) ≤ stop then
        if input.byte (pos + 1) = 0 then .error (.nonCanonical "leading zero length") else
          .ok ⟨false, false, true, digits input ((input.byte pos).toNat - 183) (pos + 1) 0,
            pos + 1 + ((input.byte pos).toNat - 183), by omega, ha⟩
      else .error .truncated := by
  simp only [header, dite_eq_left hp, dite_eq_right (by omega : ¬(input.byte pos).toNat < 128),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 183), dite_eq_left hi]

/-- Long list classification at an arbitrary available cursor. -/
private theorem header_long_list_at (input : Input) (pos stop : Nat)
    (hp : pos < stop) (lo : 248 ≤ (input.byte pos).toNat) :
    header input pos stop = if ha : pos + 1 + ((input.byte pos).toNat - 247) ≤ stop then
        if input.byte (pos + 1) = 0 then .error (.nonCanonical "leading zero length") else
          .ok ⟨true, false, true, digits input ((input.byte pos).toNat - 247) (pos + 1) 0,
            pos + 1 + ((input.byte pos).toNat - 247), by omega, ha⟩
      else .error .truncated := by
  simp only [header, dite_eq_left hp, dite_eq_right (by omega : ¬(input.byte pos).toNat < 128),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 183),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 191),
    dite_eq_right (by omega : ¬(input.byte pos).toNat ≤ 247)]

/-- Translation preserves all ordered header cases, including truncated digits. -/
private theorem header_shift (input : Input) (offset pos stop : Nat) :
    header input (pos + offset) (stop + offset) =
      (header (input.shift offset) pos stop).map (fun h ↦ h.shift offset) := by
  by_cases hp : pos < stop
  · have hp' : pos + offset < stop + offset := by omega
    have hb : (input.shift offset).byte pos = input.byte (pos + offset) := rfl
    have hb' : (input.shift offset).byte (pos + 1) = input.byte (pos + offset + 1) := by
      rw [Input.byte_shift]
      congr 1
      omega
    by_cases hs : (input.byte (pos + offset)).toNat < 128
    · rw [header_single input _ _ hp' hs,
        header_single (input.shift offset) _ _ hp (by rw [hb]; exact hs)]
      simp only [Except.map, Header.shift]
      congr 2 <;> omega
    · by_cases hs' : (input.byte (pos + offset)).toNat ≤ 183
      · rw [header_short_bytes_at input _ _ hp' (by omega) hs',
          header_short_bytes_at (input.shift offset) _ _ hp (by rw [hb]; omega)
            (by rw [hb]; exact hs')]
        simp only [Except.map, Header.shift, hb]
        congr 2 <;> omega
      · by_cases hl : (input.byte (pos + offset)).toNat ≤ 191
        · rw [header_long_bytes_at input _ _ hp' (by omega) hl,
            header_long_bytes_at (input.shift offset) _ _ hp (by rw [hb]; omega)
              (by rw [hb]; exact hl)]
          simp only [hb]
          by_cases ha : pos + 1 + ((input.byte (pos + offset)).toNat - 183) ≤ stop
          · have ha' : pos + offset + 1 +
              ((input.byte (pos + offset)).toNat - 183) ≤ stop + offset := by
              omega
            rw [dite_eq_left ha', dite_eq_left ha, hb']
            split
            · rfl
            · simp only [Except.map, Header.shift, digits_shift, Except.ok.injEq,
                Header.mk.injEq, true_and]
              refine ⟨?_, ?_⟩
              · exact congrArg (fun q ↦ digits input ((input.byte (pos + offset)).toNat - 183) q 0)
                  (by omega)
              · omega
          · have ha' : ¬pos + offset + 1 +
              ((input.byte (pos + offset)).toNat - 183) ≤ stop + offset := by
              omega
            rw [dite_eq_right ha', dite_eq_right ha]
            rfl
        · by_cases hl' : (input.byte (pos + offset)).toNat ≤ 247
          · rw [header_short_list_at input _ _ hp' (by omega) hl',
              header_short_list_at (input.shift offset) _ _ hp (by rw [hb]; omega)
                (by rw [hb]; exact hl')]
            simp only [Except.map, Header.shift, hb]
            congr 2 <;> omega
          · rw [header_long_list_at input _ _ hp' (by omega),
              header_long_list_at (input.shift offset) _ _ hp (by rw [hb]; omega)]
            simp only [hb]
            by_cases ha : pos + 1 + ((input.byte (pos + offset)).toNat - 247) ≤ stop
            · have ha' : pos + offset + 1 +
                ((input.byte (pos + offset)).toNat - 247) ≤ stop + offset := by
                omega
              rw [dite_eq_left ha', dite_eq_left ha, hb']
              split
              · rfl
              · simp only [Except.map, Header.shift, digits_shift, Except.ok.injEq,
                  Header.mk.injEq, true_and]
                refine ⟨?_, ?_⟩
                · exact congrArg
                    (fun q ↦ digits input ((input.byte (pos + offset)).toNat - 247) q 0)
                    (by omega)
                · omega
            · have ha' : ¬pos + offset + 1 +
                ((input.byte (pos + offset)).toNat - 247) ≤ stop + offset := by
                omega
              rw [dite_eq_right ha', dite_eq_right ha]
              rfl
  · have hp' : ¬pos + offset < stop + offset := by omega
    rw [header, header, dite_eq_right hp', dite_eq_right hp]
    rfl

mutual
  /-- Translating a validated item window preserves its complete result. -/
  private theorem item_shift (input : Input) (offset pos stop : Nat) :
      item input (pos + offset) (stop + offset) = item (input.shift offset) pos stop := by
    rw [item, item, header_shift]
    cases hh : header (input.shift offset) pos stop with
    | error e => rfl
    | ok h =>
      simp only [Except.map, Header.shift]
      have hs : (stop + offset = pos + offset + 1) = (stop = pos + 1) := propext (by omega)
      have he : (h.start + offset + h.payload > stop + offset) = (h.start + h.payload > stop) :=
        propext (by omega)
      have ht : (h.start + offset + h.payload < stop + offset) = (h.start + h.payload < stop) :=
        propext (by omega)
      simp only [hs, he, ht, Input.shift]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · rw [joined_shift input offset h.start stop []]
                rfl
              · rfl
  termination_by 2 * (stop - pos)
  decreasing_by have := h.advances; have := h.available; omega
  /-- Translation preserves the ordered child cursor and its prior reverse accumulator. -/
  private theorem joined_shift (input : Input) (offset pos stop : Nat) (rev : List RlpItem) :
      joined input (pos + offset) (stop + offset) rev =
        joined (input.shift offset) pos stop rev := by
    by_cases hp : pos < stop
    · have hp' : pos + offset < stop + offset := by omega
      rw [joined, joined, dite_eq_left hp', dite_eq_left hp, header_shift]
      cases hh : header (input.shift offset) pos stop with
      | error e => rfl
      | ok h =>
        simp only [Except.map, Header.shift]
        by_cases he : h.start + h.payload ≤ stop
        · have he' : h.start + offset + h.payload ≤ stop + offset := by omega
          rw [dite_eq_left he', dite_eq_left he]
          have hn : h.start + offset + h.payload = h.start + h.payload + offset := by omega
          rw [hn, item_shift input offset pos (h.start + h.payload)]
          cases hx : item (input.shift offset) pos (h.start + h.payload) with
          | error e => rfl
          | ok x => exact joined_shift input offset (h.start + h.payload) stop (x :: rev)
        · have he' : ¬h.start + offset + h.payload ≤ stop + offset := by omega
          rw [dite_eq_right he', dite_eq_right he]
    · have hp' : ¬pos + offset < stop + offset := by omega
      rw [joined, joined, dite_eq_right hp', dite_eq_right hp]
  termination_by 2 * (stop - pos) + 1
  decreasing_by all_goals have := h.advances; have := h.available; omega
end

/-! ### Window and minimal-digit algebra -/

/-- A scoped digit fold observes exactly the bounded ambient digits. -/
private theorem digits_window (bs : List UInt8) (count pos acc : Nat)
    (hb : pos + count ≤ bs.length) :
    digits (listInput bs) count pos acc =
      ((bs.drop pos).take count).foldl (fun a b ↦ 256 * a + b.toNat) acc := by
  induction count generalizing pos acc with
  | zero => simp only [digits, List.take_zero, List.foldl_nil]
  | succ count ih =>
    have hp : pos < bs.length := by omega
    rw [digits, ih (pos + 1) _ (by omega)]
    rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, List.foldl_cons]
    simp only [listInput, List.getElem?_eq_getElem hp, Option.getD_some]

/-- Every non-leading-zero digit string is the complete minimal encoding. -/
private theorem minimal_digits (ds : List UInt8) (h : ds.head? ≠ some 0) :
    (Uint.toBeBytes (ds.foldl (fun a b ↦ 256 * a + b.toNat) 0)).toList = ds := by
  have hg : ds.toByteArray[0]? ≠ some 0 := by
    change ds.toByteArray.data[0]? ≠ some 0
    rw [← Array.getElem?_toList, List.toList_data_toByteArray]
    simpa only [List.head?_eq_getElem?] using h
  have hv : Uint.ofBeBytes (Bytes.ofByteArray ds.toByteArray) =
      ds.foldl (fun a b ↦ 256 * a + b.toNat) 0 := by
    rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofByteArray, List.toList_data_toByteArray]
  have hc := (toNat_canonical_iff ds.toByteArray _).mp
    ((toNat_eq_ok_bytes_iff ds.toByteArray _).mpr ⟨hg, hv⟩)
  have := congrArg (fun b : ByteArray ↦ b.data.toList) hc
  simpa only [List.toList_data_toByteArray, Bytes.toList_toByteArray] using this.symm

/-- Adjacent ambient windows append without clipping under explicit bounds. -/
private theorem window_split (bs : List UInt8) (p m e : Nat)
    (hpm : p ≤ m) (hme : m ≤ e) :
    (bs.drop p).take (e - p) = (bs.drop p).take (m - p) ++ (bs.drop m).take (e - m) := by
  have he : e - p = (m - p) + (e - m) := by omega
  rw [he, List.take_add]
  rw [List.drop_drop]
  rw [show p + (m - p) = m by omega]

/-- A nonempty bounded window exposes its original tag and remaining bytes. -/
private theorem window_cons (bs : List UInt8) (p e : Nat)
    (hp : p < e) (he : e ≤ bs.length) :
    (bs.drop p).take (e - p) = (listInput bs).byte p :: (bs.drop (p + 1)).take (e - (p + 1)) := by
  have hb : p < bs.length := by omega
  rw [List.drop_eq_getElem_cons hb, show e - p = (e - (p + 1)) + 1 by omega,
    List.take_succ_cons]
  simp only [listInput, List.getElem?_eq_getElem hb, Option.getD_some]

/-- Successful long length digits are minimal, exact-width and below the wire limit. -/
private theorem digits_canonical (bs : List UInt8) (p count : Nat)
    (hpos : 0 < count) (hcount : count ≤ 8) (hb : p + count ≤ bs.length)
    (hz : (listInput bs).byte p ≠ 0) :
    (Uint.toBeBytes (digits (listInput bs) count p 0)).toList = (bs.drop p).take count ∧
    (Uint.toBeBytes (digits (listInput bs) count p 0)).size = count ∧
    digits (listInput bs) count p 0 < 2 ^ 64 := by
  have hp : p < bs.length := by omega
  have hhead : ((bs.drop p).take count).head? ≠ some 0 := by
    rw [List.drop_eq_getElem_cons hp]
    cases count with
    | zero => omega
    | succ count =>
      simp only [List.take_succ_cons, List.head?_cons]
      intro hzero
      apply hz
      simpa only [listInput, List.getElem?_eq_getElem hp, Option.getD_some] using
        Option.some.inj hzero
  have hd := minimal_digits ((bs.drop p).take count) hhead
  rw [← digits_window bs count p 0 hb] at hd
  have hw : (Uint.toBeBytes (digits (listInput bs) count p 0)).size = count := by
    rw [← Bytes.length_toList, hd, List.length_take, List.length_drop]
    omega
  refine ⟨hd, hw, ?_⟩
  have hv : digits (listInput bs) count p 0 =
      Uint.ofBeBytes (Bytes.ofList ((bs.drop p).take count)) := by
    rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofList, digits_window bs count p 0 hb]
  rw [hv]
  apply Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt _)
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  rw [Bytes.size_ofList, List.length_take, List.length_drop]
  omega

/-- Exact short nonsingleton headers reconstruct their standard prefix. -/
private theorem short_window_prefix (bs : List UInt8) (p e payload : Nat)
    (short long : UInt8) (he : e ≤ bs.length) (hn : payload < 56)
    (htag : ((listInput bs).byte p).toNat = short.toNat + payload)
    (hex : p + 1 + payload = e) :
    (bs.drop p).take (e - p) =
      lengthPrefixModel short long payload ++ (bs.drop (p + 1)).take (e - (p + 1)) := by
  rw [window_cons bs p e (by omega) he, lengthPrefixModel_short short long payload hn]
  simp only [List.singleton_append]
  congr 1
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat_of_lt' (by
    change _ < 256
    have := ((listInput bs).byte p).toNat_lt
    omega)]
  exact htag

/-- Exact long headers reconstruct both original length digits and standard prefix. -/
private theorem long_window_prefix (bs : List UInt8) (p e count : Nat)
    (short long : UInt8) (he : e ≤ bs.length) (hpos : 0 < count) (hcount : count ≤ 8)
    (hb : p + 1 + count ≤ e) (hz : (listInput bs).byte (p + 1) ≠ 0)
    (hn : 56 ≤ digits (listInput bs) count (p + 1) 0)
    (htag : ((listInput bs).byte p).toNat = long.toNat + count) :
    (bs.drop p).take (e - p) =
      lengthPrefixModel short long (digits (listInput bs) count (p + 1) 0) ++
        (bs.drop (p + 1 + count)).take (e - (p + 1 + count)) := by
  obtain ⟨hd, hw, _⟩ := digits_canonical bs (p + 1) count hpos hcount (by omega) hz
  rw [window_cons bs p e (by omega) he,
    lengthPrefixModel_long short long _ hn, hw, List.cons_append, hd]
  congr 1
  · apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat_of_lt' (by
      change _ < 256
      have := ((listInput bs).byte p).toNat_lt
      omega)]
    exact htag
  · simpa only [Nat.add_sub_cancel_left] using
      window_split bs (p + 1) (p + 1 + count) e (by omega) hb

/-! ### Canonical header reconstruction -/

/-- A successful canonical nonsingleton header identifies the exact standard prefix.
The header itself remains permissive; the caller supplies canonical long form and
exact extent, as enforced by `item`. The payload bound is derived from the header. -/
private theorem header_encoding (bs : List UInt8) (p e : Nat) (h : Header p e)
    (he : e ≤ bs.length) (hh : header (listInput bs) p e = .ok h)
    (hsingle : h.isSingle = false) (hcanonical : h.isLong = true → 56 ≤ h.payload)
    (hex : h.start + h.payload = e) :
    h.payload < 2 ^ 64 ∧ (Uint.toBeBytes h.payload).size ≤ 8 ∧
    (bs.drop p).take (e - p) = lengthPrefixModel (if h.isList then 192 else 128)
        (if h.isList then 247 else 183) h.payload ++
          (bs.drop h.start).take (e - h.start) := by
  have hp : p < e := by
    have := h.advances
    have := h.available
    omega
  by_cases hs : ((listInput bs).byte p).toNat < 128
  · rw [header_single _ p e hp hs] at hh
    cases Except.ok.inj hh
    cases hsingle
  by_cases hb : ((listInput bs).byte p).toNat ≤ 183
  · rw [header_short_bytes_at _ p e hp (by omega) hb] at hh
    cases Except.ok.inj hh
    dsimp only at hex ⊢
    have hn : ((listInput bs).byte p).toNat - 128 < 56 := by omega
    refine ⟨by omega, ?_, ?_⟩
    · rw [length_digits_width]
      omega
    · apply short_window_prefix bs p e _ 128 183 he hn _ hex
      change ((listInput bs).byte p).toNat = 128 + _
      omega
  by_cases hl : ((listInput bs).byte p).toNat ≤ 191
  · rw [header_long_bytes_at _ p e hp (by omega) hl] at hh
    split at hh
    · next ha =>
      split at hh
      · cases hh
      · next hz =>
        cases Except.ok.inj hh
        dsimp only at hcanonical hex ⊢
        have hpos : 0 < ((listInput bs).byte p).toNat - 183 := by omega
        have hcount : ((listInput bs).byte p).toNat - 183 ≤ 8 := by omega
        obtain ⟨_, hw, hv⟩ := digits_canonical bs (p + 1) _ hpos hcount (by omega) hz
        refine ⟨hv, by omega, ?_⟩
        apply long_window_prefix bs p e _ 128 183 he hpos hcount ha hz
          (hcanonical rfl)
        change ((listInput bs).byte p).toNat = 183 + _
        omega
    · cases hh
  by_cases hlist : ((listInput bs).byte p).toNat ≤ 247
  · rw [header_short_list_at _ p e hp (by omega) hlist] at hh
    cases Except.ok.inj hh
    dsimp only at hex ⊢
    have hn : ((listInput bs).byte p).toNat - 192 < 56 := by omega
    refine ⟨by omega, ?_, ?_⟩
    · rw [length_digits_width]
      omega
    · apply short_window_prefix bs p e _ 192 247 he hn _ hex
      change ((listInput bs).byte p).toNat = 192 + _
      omega
  rw [header_long_list_at _ p e hp (by omega)] at hh
  split at hh
  · next ha =>
    split at hh
    · cases hh
    · next hz =>
      cases Except.ok.inj hh
      dsimp only at hcanonical hex ⊢
      have htag := ((listInput bs).byte p).toNat_lt
      have hpos : 0 < ((listInput bs).byte p).toNat - 247 := by omega
      have hcount : ((listInput bs).byte p).toNat - 247 ≤ 8 := by omega
      obtain ⟨_, hw, hv⟩ := digits_canonical bs (p + 1) _ hpos hcount (by omega) hz
      refine ⟨hv, by omega, ?_⟩
      apply long_window_prefix bs p e _ 192 247 he hpos hcount ha hz
        (hcanonical rfl)
      change ((listInput bs).byte p).toNat = 247 + _
      omega
  · cases hh

/-! ### Encoded header recovery -/

/-- Digits following a tag recover exactly the encoded prefix before any tail. -/
private theorem digits_prefix (tag : UInt8) (ds tail : List UInt8) :
    digits (listInput (tag :: ds ++ tail)) ds.length 1 0 =
      ds.foldl (fun a b ↦ 256 * a + b.toNat) 0 := by
  rw [digits_window (tag :: ds ++ tail) ds.length 1 0 (by simp; omega)]
  change ((ds ++ tail).take ds.length).foldl (fun a b ↦ 256 * a + b.toNat) 0 = _
  rw [List.take_left]

/-- The semantic descriptor fields determine a header; scope proofs are irrelevant. -/
private theorem header_fields_eq {p e : Nat} (h k : Header p e)
    (hl : h.isList = k.isList) (hs : h.isSingle = k.isSingle) (hg : h.isLong = k.isLong)
    (hn : h.payload = k.payload) (hp : h.start = k.start) : h = k := by
  cases h
  cases k
  cases hl
  cases hs
  cases hg
  cases hn
  cases hp
  rfl

/-- Every standard short prefix is recovered by the original private header. -/
private theorem header_short_prefix (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hstd : short = 128 ∨ short = 192) (hn : n < 56) :
    ∃ h : Header 0 (lengthPrefixModel short long n ++ tail).length,
      header (listInput (lengthPrefixModel short long n ++ tail)) 0
        (lengthPrefixModel short long n ++ tail).length = .ok h ∧
      h.isList = (short == 192) ∧ h.isSingle = false ∧ h.isLong = false ∧
      h.payload = n ∧ h.start = (lengthPrefixModel short long n).length := by
  rw [lengthPrefixModel_short short long n hn]
  simp only [List.singleton_append, List.length_cons]
  rcases hstd with rfl | rfl
  · have ht : (UInt8.ofNat (128 + n)).toNat = 128 + n :=
      UInt8.toNat_ofNat_of_lt' (by change 128 + n < 256; omega)
    refine ⟨⟨false, false, false, n, 1, by omega, by omega⟩, ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [header_short_bytes_at _ 0 _ (by omega)
      (by change 128 ≤ (UInt8.ofNat (128 + n)).toNat; omega)
      (by change (UInt8.ofNat (128 + n)).toNat ≤ 183; omega)]
    apply congrArg (Except.ok (ε := RlpError))
    apply header_fields_eq
    · rfl
    · rfl
    · rfl
    · change (UInt8.ofNat (128 + n)).toNat - 128 = n
      omega
    · rfl
  · have ht : (UInt8.ofNat (192 + n)).toNat = 192 + n :=
      UInt8.toNat_ofNat_of_lt' (by change 192 + n < 256; omega)
    refine ⟨⟨true, false, false, n, 1, by omega, by omega⟩, ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [header_short_list_at _ 0 _ (by omega)
      (by change 192 ≤ (UInt8.ofNat (192 + n)).toNat; omega)
      (by change (UInt8.ofNat (192 + n)).toNat ≤ 247; omega)]
    apply congrArg (Except.ok (ε := RlpError))
    apply header_fields_eq
    · rfl
    · rfl
    · rfl
    · change (UInt8.ofNat (192 + n)).toNat - 192 = n
      omega
    · rfl

/-- The long-string branch equation keeps the original permissive scanner. -/
private theorem header_long_bytes_observation (input : Input) (p e : Nat)
    (hp : p < e) (hlo : 184 ≤ (input.byte p).toNat)
    (hhi : (input.byte p).toNat ≤ 191)
    (ha : p + 1 + ((input.byte p).toNat - 183) ≤ e) (hz : input.byte (p + 1) ≠ 0) :
    header input p e = .ok
      ⟨false, false, true, digits input ((input.byte p).toNat - 183) (p + 1) 0,
        p + 1 + ((input.byte p).toNat - 183), by omega, ha⟩ := by
  rw [header_long_bytes_at input p e hp hlo hhi, dite_eq_left ha, ite_eq_right hz]

/-- The long-list branch equation keeps the original permissive scanner. -/
private theorem header_long_list_observation (input : Input) (p e : Nat)
    (hp : p < e) (hlo : 248 ≤ (input.byte p).toNat)
    (ha : p + 1 + ((input.byte p).toNat - 247) ≤ e) (hz : input.byte (p + 1) ≠ 0) :
    header input p e = .ok
      ⟨true, false, true, digits input ((input.byte p).toNat - 247) (p + 1) 0,
        p + 1 + ((input.byte p).toNat - 247), by omega, ha⟩ := by
  rw [header_long_list_at input p e hp hlo, dite_eq_left ha, ite_eq_right hz]

/-- Nonempty minimal integer digits expose a nonzero first digit after a tag. -/
private theorem prefix_first_digit_ne_zero (tag : UInt8) (n : Nat) (tail : List UInt8)
    (hn : n ≠ 0) :
    (listInput (tag :: (Uint.toBeBytes n).toList ++ tail)).byte 1 ≠ 0 := by
  have hh := length_digits_head n hn
  have hsize : 0 < (Uint.toBeBytes n).size := by
    have hw := length_digits_width n 0
    simp only [Nat.pow_zero] at hw
    omega
  cases hd : (Uint.toBeBytes n).toList with
  | nil =>
    have hl := Bytes.length_toList (Uint.toBeBytes n)
    rw [hd] at hl
    simp only [List.length_nil] at hl
    omega
  | cons a ds =>
    change a ≠ 0
    intro hz
    apply hh
    rw [hd, List.head?_cons, hz]

/-- The original private fold recovers complete standard length digits. -/
private theorem prefix_digits_value (tag : UInt8) (n : Nat) (tail : List UInt8) :
    digits (listInput (tag :: (Uint.toBeBytes n).toList ++ tail))
      (Uint.toBeBytes n).size 1 0 = n := by
  rw [← Bytes.length_toList, digits_prefix, length_digits_value]

/-- Standard long prefixes recover every descriptor field, with arbitrary trailing bytes. -/
private theorem header_long_prefix (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hstd : (short = 128 ∧ long = 183) ∨ (short = 192 ∧ long = 247))
    (hn : 56 ≤ n) (hw : (Uint.toBeBytes n).size ≤ 8) :
    ∃ h : Header 0 (lengthPrefixModel short long n ++ tail).length,
      header (listInput (lengthPrefixModel short long n ++ tail)) 0
        (lengthPrefixModel short long n ++ tail).length = .ok h ∧
      h.isList = (short == 192) ∧ h.isSingle = false ∧ h.isLong = true ∧
      h.payload = n ∧ h.start = (lengthPrefixModel short long n).length := by
  have hpos : 0 < (Uint.toBeBytes n).size := by
    have hzero := length_digits_width n 0
    simp only [Nat.pow_zero] at hzero
    omega
  rw [lengthPrefixModel_long short long n hn, List.cons_append]
  rcases hstd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let input := listInput (UInt8.ofNat (183 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail)
    let e := (UInt8.ofNat (183 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail).length
    have hp : 0 < e := by
      change 0 < ((Uint.toBeBytes n).toList ++ tail).length + 1
      omega
    have ht : (input.byte 0).toNat = 183 + (Uint.toBeBytes n).size := by
      change (UInt8.ofNat (183 + (Uint.toBeBytes n).size)).toNat = _
      exact long_tag_toNat 183 n (by decide) hw
    have hc : (input.byte 0).toNat - 183 = (Uint.toBeBytes n).size := by omega
    have ha : 0 + 1 + ((input.byte 0).toNat - 183) ≤ e := by
      rw [hc]
      dsimp only [e]
      simp only [List.length_cons, List.length_append, Bytes.length_toList]
      omega
    have hz : input.byte (0 + 1) ≠ 0 :=
      prefix_first_digit_ne_zero _ n tail (by omega)
    have hh := header_long_bytes_observation input 0 e hp (by omega) (by omega) ha hz
    refine ⟨_, hh, rfl, rfl, rfl, ?_, ?_⟩
    · dsimp only [Header.payload]
      rw [hc]
      exact prefix_digits_value _ n tail
    · change 0 + 1 + ((input.byte 0).toNat - 183) = _
      rw [hc]
      simp only [List.length_cons, Bytes.length_toList]
      omega
  · let input := listInput (UInt8.ofNat (247 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail)
    let e := (UInt8.ofNat (247 + (Uint.toBeBytes n).size) ::
      (Uint.toBeBytes n).toList ++ tail).length
    have hp : 0 < e := by
      change 0 < ((Uint.toBeBytes n).toList ++ tail).length + 1
      omega
    have ht : (input.byte 0).toNat = 247 + (Uint.toBeBytes n).size := by
      change (UInt8.ofNat (247 + (Uint.toBeBytes n).size)).toNat = _
      exact long_tag_toNat 247 n (by decide) hw
    have hc : (input.byte 0).toNat - 247 = (Uint.toBeBytes n).size := by omega
    have ha : 0 + 1 + ((input.byte 0).toNat - 247) ≤ e := by
      rw [hc]
      dsimp only [e]
      simp only [List.length_cons, List.length_append, Bytes.length_toList]
      omega
    have hz : input.byte (0 + 1) ≠ 0 :=
      prefix_first_digit_ne_zero _ n tail (by omega)
    have hh := header_long_list_observation input 0 e hp (by omega) ha hz
    refine ⟨_, hh, rfl, rfl, rfl, ?_, ?_⟩
    · dsimp only [Header.payload]
      rw [hc]
      exact prefix_digits_value _ n tail
    · change 0 + 1 + ((input.byte 0).toNat - 247) = _
      rw [hc]
      simp only [List.length_cons, Bytes.length_toList]
      omega

/-- Every bounded standard prefix yields its exact original header descriptor.
This scanner equation allows arbitrary tail bytes; payload availability and exact
extent belong to the later item checks. The literal low-singleton case is separate. -/
private theorem header_prefix (short long : UInt8) (n : Nat) (tail : List UInt8)
    (hstd : (short = 128 ∧ long = 183) ∨ (short = 192 ∧ long = 247))
    (hw : (Uint.toBeBytes n).size ≤ 8) :
    ∃ h : Header 0 (lengthPrefixModel short long n ++ tail).length,
      header (listInput (lengthPrefixModel short long n ++ tail)) 0
        (lengthPrefixModel short long n ++ tail).length = .ok h ∧
      h.isList = (short == 192) ∧ h.isSingle = false ∧
      h.isLong = decide (56 ≤ n) ∧ h.payload = n ∧
      h.start = (lengthPrefixModel short long n).length := by
  by_cases hn : n < 56
  · have hs : short = 128 ∨ short = 192 := hstd.elim (fun h ↦ .inl h.1) (fun h ↦ .inr h.1)
    obtain ⟨h, hh, hl, hs, hg, hp, he⟩ := header_short_prefix short long n tail hs hn
    refine ⟨h, hh, hl, hs, ?_, hp, he⟩
    rw [hg]
    exact (decide_eq_false (by omega : ¬56 ≤ n)).symm
  · obtain ⟨h, hh, hl, hs, hg, hp, he⟩ :=
      header_long_prefix short long n tail hstd (by omega) hw
    refine ⟨h, hh, hl, hs, ?_, hp, he⟩
    rw [hg]
    exact (decide_eq_true (by omega : 56 ≤ n)).symm


/-! ### Bounded window transport -/

/-- Suffix callbacks are exactly a translated original reader. -/
private theorem listInput_shift (bs : List UInt8) (offset : Nat) :
    (listInput bs).shift offset = listInput (bs.drop offset) := by
  unfold Input.shift listInput
  congr 1
  · funext i
    rw [List.getElem?_drop, Nat.add_comm offset i]
  · funext p e
    change ((bs.drop (p + offset)).take ((e + offset) - (p + offset))).toByteArray =
      (((bs.drop offset).drop p).take (e - p)).toByteArray
    rw [List.drop_drop, Nat.add_comm offset p, Nat.add_sub_add_right]

/-- Clipping beyond an observed byte does not change that byte. -/
private theorem listInput_byte_take (bs : List UInt8) (n i : Nat) (hi : i < n) :
    (listInput bs).byte i = (listInput (bs.take n)).byte i := by
  change bs[i]?.getD 0 = (bs.take n)[i]?.getD 0
  rw [List.getElem?_take_of_lt hi]

/-- Clipping beyond an observed leaf does not change its complete window. -/
private theorem listInput_leaf_take (bs : List UInt8) (n start endPos : Nat)
    (hs : start ≤ endPos) (he : endPos ≤ n) :
    (listInput bs).leaf start endPos = (listInput (bs.take n)).leaf start endPos := by
  change ((bs.drop start).take (endPos - start)).toByteArray =
    (((bs.take n).drop start).take (endPos - start)).toByteArray
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Clipping after the scope preserves all reads, including failure diagnostics. -/
private theorem item_take (bs : List UInt8) (n p e : Nat) (hp : p ≤ e) (he : e ≤ n) :
    item (listInput bs) p e = item (listInput (bs.take n)) p e := by
  apply item_congr _ _ p e
  · intro i _ hi
    exact listInput_byte_take bs n i (by omega)
  · intro start endPos _ hs ht
    exact listInput_leaf_take bs n start endPos hs (by omega)
  · exact hp

/-- Restricting storage beyond a joined cursor scope preserves its complete result. -/
private theorem joined_take (bs : List UInt8) (n p e : Nat) (rev : List RlpItem)
    (hp : p ≤ e) (he : e ≤ n) :
    joined (listInput bs) p e rev = joined (listInput (bs.take n)) p e rev := by
  apply joined_congr _ _ p e rev
  · intro i _ hi
    exact listInput_byte_take bs n i (by omega)
  · intro start endPos _ hs ht
    exact listInput_leaf_take bs n start endPos hs (by omega)
  · exact hp

/-- The private ambient cursor is exactly the full decoder of its bounded window. -/
private theorem item_window (bs : List UInt8) (p e : Nat)
    (hp : p ≤ e) (he : e ≤ bs.length) :
    item (listInput bs) p e = decodeModel ((bs.drop p).take (e - p)) := by
  have hw : ((bs.drop p).take (e - p)).length = e - p := by
    rw [List.length_take, List.length_drop]
    omega
  have hs := item_shift (listInput bs) p 0 (e - p)
  rw [Nat.zero_add, show e - p + p = e by omega, listInput_shift] at hs
  rw [hs, item_take (bs.drop p) (e - p) 0 (e - p) (by omega) (by omega)]
  rw [decodeModel, hw]

/-- Joined cursors preserve the reverse accumulator when translated to a window. -/
private theorem joined_window (bs : List UInt8) (p e : Nat) (rev : List RlpItem)
    (hp : p ≤ e) :
    joined (listInput bs) p e rev =
      joined (listInput ((bs.drop p).take (e - p))) 0 (e - p) rev := by
  have hs := joined_shift (listInput bs) p 0 (e - p) rev
  rw [Nat.zero_add, show e - p + p = e by omega, listInput_shift] at hs
  rw [hs, joined_take (bs.drop p) (e - p) 0 (e - p) rev (by omega) (by omega)]

/-! ### Copied byte-leaf encoding -/

/-- Bounded windows retain their exact width. -/
private theorem window_length (bs : List UInt8) (p e : Nat)
    (hp : p ≤ e) (he : e ≤ bs.length) : ((bs.drop p).take (e - p)).length = e - p := by
  rw [List.length_take, List.length_drop]
  omega

/-- A validated copied byte leaf has exactly the window length. -/
private theorem leaf_size (bs : List UInt8) (p e : Nat)
    (hp : p ≤ e) (he : e ≤ bs.length) : ((listInput bs).leaf p e).size = e - p := by
  change ((bs.drop p).take (e - p)).toByteArray.size = e - p
  change ((bs.drop p).take (e - p)).toByteArray.data.size = _
  rw [← Array.length_toList, List.toList_data_toByteArray, window_length bs p e hp he]

/-- Leaf copying preserves the exact readable byte window. -/
private theorem leaf_model (bs : List UInt8) (p e : Nat) :
    ((listInput bs).leaf p e).data.toList = (bs.drop p).take (e - p) := by
  exact List.toList_data_toByteArray

/-- The first byte of a nonempty copied leaf is the original cursor byte. -/
private theorem leaf_head (bs : List UInt8) (p e : Nat)
    (hp : p < e) (he : e ≤ bs.length) :
    ((listInput bs).leaf p e)[0]? = some ((listInput bs).byte p) := by
  change ((bs.drop p).take (e - p)).toByteArray.data[0]? = _
  rw [← Array.getElem?_toList, List.toList_data_toByteArray, window_cons bs p e hp he]
  rfl

/-- A successful singleton header denotes precisely a literal low byte. -/
private theorem header_single_low (input : Input) (p e : Nat) (h : Header p e)
    (hh : header input p e = .ok h) (hs : h.isSingle = true) : (input.byte p).toNat < 128 := by
  have hp : p < e := by have := h.advances; have := h.available; omega
  by_cases ht : (input.byte p).toNat < 128
  · exact ht
  · unfold header at hh
    rw [dite_eq_left hp, dite_eq_right ht] at hh
    split at hh
    · cases Except.ok.inj hh
      cases hs
    · split at hh
      · dsimp only at hh
        split at hh
        · split at hh
          · cases hh
          · cases Except.ok.inj hh
            cases hs
        · cases hh
      · split at hh
        · cases Except.ok.inj hh
          cases hs
        · dsimp only at hh
          split at hh
          · split at hh
            · cases hh
            · cases Except.ok.inj hh
              cases hs
          · cases hh

/-- Literal singleton leaves preserve exactly their byte model. -/
private theorem encode_leaf_single (bs : List UInt8) (p e : Nat)
    (he : e ≤ bs.length) (hex : e = p + 1) (ht : ((listInput bs).byte p).toNat < 128) :
    encodeModel (.bytes ((listInput bs).leaf p e)) = (bs.drop p).take (e - p) := by
  have hp : p < e := by omega
  have hs := leaf_size bs p e (by omega) he
  have hh := leaf_head bs p e hp he
  rw [encodeModel]
  have hsingle : ((listInput bs).leaf p e).size = 1 ∧
      ((((listInput bs).leaf p e)[0]?).getD 128).toNat < 128 := by
    refine ⟨by omega, ?_⟩
    simpa only [hh, Option.getD_some] using ht
  split
  · exact leaf_model bs p e
  · next hn => exact False.elim (hn hsingle)

/-- A validated nonsingleton leaf has the exact ordinary length prefix. -/
private theorem encode_leaf_prefixed (bs : List UInt8) (p e payload : Nat)
    (hp : p ≤ e) (he : e ≤ bs.length) (hex : e - p = payload)
    (hn : ¬(payload = 1 ∧ ((listInput bs).byte p).toNat < 128)) :
    encodeModel (.bytes ((listInput bs).leaf p e)) =
      lengthPrefixModel 128 183 payload ++ (bs.drop p).take (e - p) := by
  have hs := leaf_size bs p e hp he
  have hsingle : ¬(((listInput bs).leaf p e).size = 1 ∧
      ((((listInput bs).leaf p e)[0]?).getD 128).toNat < 128) := by
    intro hc
    have hpos : p < e := by omega
    have hh := leaf_head bs p e hpos he
    apply hn
    refine ⟨by omega, ?_⟩
    simpa only [hh, Option.getD_some] using hc.2
  rw [encodeModel]
  split
  · next hy => exact False.elim (hsingle hy)
  · rw [hs, leaf_model, hex]

/-! ### Successful item and ordered-child induction -/

mutual
  /-- Every successful item is encodable and owns exactly its complete ambient window. -/
  private theorem item_success (bs : List UInt8) (p e : Nat) (x : RlpItem)
      (hp : p ≤ e) (he : e ≤ bs.length) (hd : item (listInput bs) p e = .ok x) :
      Encodable x ∧ encodeModel x = (bs.drop p).take (e - p) := by
    rw [item] at hd
    cases hh : header (listInput bs) p e with
    | error err => rw [hh] at hd; cases hd
    | ok h =>
      rw [hh] at hd
      dsimp only at hd
      split at hd
      · next hs =>
        split at hd
        · next hex =>
          cases Except.ok.inj hd
          refine ⟨?_, encode_leaf_single bs p e he hex (header_single_low _ p e h hh hs)⟩
          apply (encodable_bytes_iff _).mpr
          rw [leaf_size bs p e hp he]
          omega
        · cases hd
      · next hs =>
        split at hd
        · cases hd
        · next hc =>
          split at hd
          · cases hd
          · next htr =>
            split at hd
            · cases hd
            · next htail =>
              have hex : h.start + h.payload = e := by omega
              have hsingle : h.isSingle = false := Bool.eq_false_iff.mpr hs
              have hcanonical : h.isLong = true → 56 ≤ h.payload := by
                intro hl
                have hc' : ¬(h.isLong = true ∧ h.payload < 56) := by
                  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
                by_cases hn : 56 ≤ h.payload
                · exact hn
                · exact False.elim (hc' ⟨hl, by omega⟩)
              obtain ⟨hbound, _, hprefix⟩ := header_encoding bs p e h he hh hsingle hcanonical hex
              split at hd
              · next hl =>
                cases hj : joined (listInput bs) h.start e [] with
                | error err => rw [hj] at hd; cases hd
                | ok ys =>
                  rw [hj] at hd
                  dsimp only at hd
                  cases Except.ok.inj hd
                  obtain ⟨zs, hys, hz, hm⟩ := joined_success bs h.start e [] ys h.available he hj
                  simp only [List.reverse_nil, List.nil_append] at hys
                  subst ys
                  have hlen : (encodePayloadModel zs).length = h.payload := by
                    rw [hm, window_length bs h.start e h.available he]
                    omega
                  refine ⟨(encodable_list_iff zs).mpr ⟨hz, by omega⟩, ?_⟩
                  rw [encodeModel, hlen, hm]
                  simpa only [hl, ite_true] using hprefix.symm
              · next hl =>
                split at hd
                · cases hd
                · next hn =>
                  cases Except.ok.inj hd
                  have hn' : ¬(h.payload = 1 ∧ ((listInput bs).byte h.start).toNat < 128) := by
                    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hn
                  refine ⟨?_, ?_⟩
                  · apply (encodable_bytes_iff _).mpr
                    rw [leaf_size bs h.start e h.available he]
                    omega
                  · rw [encode_leaf_prefixed bs h.start e h.payload h.available he (by omega) hn']
                    simpa only [hl, Bool.false_eq_true, ite_false] using hprefix.symm
  termination_by 2 * (e - p)
  decreasing_by have := h.advances; have := h.available; omega
  /-- Joined success exposes only the fresh canonical suffix, independent of prior rev. -/
  private theorem joined_success (bs : List UInt8) (p e : Nat) (rev ys : List RlpItem)
      (hp : p ≤ e) (he : e ≤ bs.length)
      (hd : joined (listInput bs) p e rev = .ok ys) :
      ∃ zs, ys = rev.reverse ++ zs ∧ (∀ x ∈ zs, Encodable x) ∧
        encodePayloadModel zs = (bs.drop p).take (e - p) := by
    rw [joined] at hd
    split at hd
    · next hpos =>
      cases hh : header (listInput bs) p e with
      | error err => rw [hh] at hd; cases hd
      | ok h =>
        rw [hh] at hd
        dsimp only at hd
        split at hd
        · next hend =>
          cases hx : item (listInput bs) p (h.start + h.payload) with
          | error err => rw [hx] at hd; cases hd
          | ok x =>
            rw [hx] at hd
            dsimp only at hd
            have hxcan := item_success bs p (h.start + h.payload) x
              (by have := h.advances; omega) (by omega) hx
            obtain ⟨zs, hys, hz, hm⟩ := joined_success bs (h.start + h.payload) e (x :: rev) ys
              hend he hd
            refine ⟨x :: zs, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hys
            · intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with hy | hy
              · subst y
                exact hxcan.1
              · exact hz y hy
            · rw [encodePayloadModel_cons, hxcan.2, hm]
              exact (window_split bs p (h.start + h.payload) e
                (by have := h.advances; omega) hend).symm
        · cases hd
    · next hpos =>
      have hex : e = p := by omega
      cases Except.ok.inj hd
      refine ⟨[], by rw [List.append_nil], ?_, ?_⟩
      · intro x hx
        cases hx
      · rw [hex, Nat.sub_self, List.take_zero, encodePayloadModel_nil]
  termination_by 2 * (e - p) + 1
  decreasing_by all_goals have := h.advances; have := h.available; omega
end

/-! ### Successful-input laws -/

/-- Successful model decoding is canonical on every finite input; `rlp.py:387–484`. -/
theorem decodeModel_success (bs : List UInt8) (x : RlpItem) (h : decodeModel bs = .ok x) :
    Encodable x ∧ encodeModel x = bs := by
  have hs := item_success bs 0 bs.length x (by omega) (by omega) h
  simpa only [List.drop_zero, Nat.sub_zero, List.take_length] using hs

/-- Successful packed decoding proves its own Q47 encoding-domain premise. -/
theorem decode_success_encodable (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) :
    Encodable x := by
  rw [decode_eq_model] at h
  exact (decodeModel_success b.data.toList x h).1

/-- Reencoding any accepted input preserves every original byte; `rlp.py:387–484`. -/
theorem encode_eq_of_decode_eq_ok (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) :
    encode x = b := by
  rw [decode_eq_model] at h
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [toList_encode]
  exact (decodeModel_success b.data.toList x h).2

/-! ### Forward encoder inversion -/

/-- Canonical nonsingleton headers with exact bodies expose the unchanged item equation. -/
private theorem item_header_exact (input : Input) (p e : Nat) (h : Header p e)
    (hh : header input p e = .ok h) (hs : h.isSingle = false)
    (hc : h.isLong = true → 56 ≤ h.payload) (he : h.start + h.payload = e) :
    item input p e = if h.isList then
        match joined input h.start e [] with
        | .error err => .error err
        | .ok xs => .ok (.list xs)
      else if h.payload = 1 && (input.byte h.start).toNat < 128 then
        .error (.nonCanonical "prefixed single byte")
      else .ok (.bytes (input.leaf h.start e)) := by
  have hn : ¬(h.isLong && decide (h.payload < 56)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro hd
    have := hc hd.1
    omega
  rw [item, hh]
  dsimp only
  simp only [hs, Bool.false_eq_true, ite_false, ite_eq_right hn,
    dite_eq_right (by omega : ¬h.start + h.payload > e),
    ite_eq_right (by omega : ¬h.start + h.payload < e)]

/-- The complete payload is the window after its already validated prefix. -/
private theorem window_after_pre (pre body : List UInt8) :
    ((pre ++ body).drop pre.length).take ((pre ++ body).length - pre.length) = body := by
  rw [List.drop_left, List.length_append, Nat.add_sub_cancel_left, List.take_length]

/-- An Encodable first encoding recovers its validated dependent header descriptor.
The extent-only observation in `RlpCanonical` serves prefix binding; this descriptor
also supplies the classification and scoped start needed by ordered-child inversion. -/
private theorem header_encoded (x : RlpItem) (hx : Encodable x) (tail : List UInt8) :
    ∃ h : Header 0 (encodeModel x ++ tail).length,
      header (listInput (encodeModel x ++ tail)) 0 (encodeModel x ++ tail).length = .ok h ∧
      h.start + h.payload = (encodeModel x).length := by
  cases x with
  | bytes b =>
    by_cases hb : b.size = 1 ∧ (b[0]?.getD 128).toNat < 128
    · have hmodel : encodeModel (.bytes b) = b.data.toList := by
        rw [encodeModel]
        split
        · rfl
        · next hn => exact False.elim (hn hb)
      rw [hmodel]
      have hs : b.size = 1 := hb.1
      have hp : (b[0]?.getD 128).toNat < 128 := hb.2
      have hm : b.data.toList.length = 1 := by rw [Array.length_toList]; exact hs
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
        simp only [Option.getD_some] at hp
        refine ⟨⟨false, true, false, 0, 1, by omega, by simp⟩, ?_, rfl⟩
        exact header_single _ 0 _ (by simp) hp
    · have hmodel : encodeModel (.bytes b) = lengthPrefixModel 128 183 b.size ++ b.data.toList :=
      by
        rw [encodeModel]
        split
        · next hy => exact False.elim (hb hy)
        · rfl
      rw [hmodel, List.append_assoc]
      have hw : (Uint.toBeBytes b.size).size ≤ 8 := by simpa only [Encodable] using hx
      obtain ⟨h, hh, _, _, _, hn, hs⟩ :=
        header_prefix 128 183 b.size (b.data.toList ++ tail) (Or.inl ⟨rfl, rfl⟩) hw
      refine ⟨h, hh, ?_⟩
      rw [hs, hn, List.length_append, Array.length_toList]
      rfl
  | list xs =>
    have hc : (∀ x ∈ xs, Encodable x) ∧
        (Uint.toBeBytes (encodePayloadModel xs).length).size ≤ 8 := by
      simpa only [Encodable] using hx
    rw [encodeModel, List.append_assoc]
    obtain ⟨h, hh, _, _, _, hn, hs⟩ := header_prefix 192 247
      (encodePayloadModel xs).length (encodePayloadModel xs ++ tail) (Or.inr ⟨rfl, rfl⟩) hc.2
    refine ⟨h, hh, ?_⟩
    rw [hs, hn, List.length_append]

/-- Standard prefixes supply the exact canonical item guard premises. -/
private theorem header_prefix_canonical (short long : UInt8) (body : List UInt8)
    (hstd : (short = 128 ∧ long = 183) ∨ (short = 192 ∧ long = 247))
    (hw : (Uint.toBeBytes body.length).size ≤ 8) :
    ∃ h : Header 0 (lengthPrefixModel short long body.length ++ body).length,
      header (listInput (lengthPrefixModel short long body.length ++ body)) 0
        (lengthPrefixModel short long body.length ++ body).length = .ok h ∧
      h.isList = (short == 192) ∧ h.isSingle = false ∧
      (h.isLong = true → 56 ≤ h.payload) ∧
      h.start + h.payload = (lengthPrefixModel short long body.length ++ body).length ∧
      h.payload = body.length ∧ h.start = (lengthPrefixModel short long body.length).length := by
  obtain ⟨h, hh, hl, hs, hg, hn, he⟩ := header_prefix short long body.length body hstd hw
  refine ⟨h, hh, hl, hs, ?_, ?_, hn, he⟩
  · intro hlong
    rw [hn]
    exact of_decide_eq_true (hg.symm.trans hlong)
  · rw [he, hn, List.length_append]

/-- Byte position just after a complete prefix is the original body head. -/
private theorem byte_after_prefix (pre body : List UInt8) :
    (listInput (pre ++ body)).byte pre.length = body[0]?.getD 0 := by
  change (pre ++ body)[pre.length]?.getD 0 = _
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]

/-- Canonical prefixed byte bodies are decoded without changing any body byte. -/
private theorem decode_prefix_bytes (body : List UInt8)
    (hw : (Uint.toBeBytes body.length).size ≤ 8)
    (hn : ¬(body.length = 1 ∧ (body[0]?.getD 0).toNat < 128)) :
    decodeModel (lengthPrefixModel 128 183 body.length ++ body) =
      .ok (.bytes body.toByteArray) := by
  obtain ⟨h, hh, hl, hs, hc, he, hp, hstart⟩ :=
    header_prefix_canonical 128 183 body (Or.inl ⟨rfl, rfl⟩) hw
  rw [decodeModel, item_header_exact _ 0 _ h hh hs hc he]
  have hl' : h.isList = false := hl
  simp only [hl', Bool.false_eq_true, ite_false]
  rw [hp, hstart, byte_after_prefix]
  have hg : ¬(decide (body.length = 1) && decide ((body[0]?.getD 0).toNat < 128)) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hn
  rw [ite_eq_right hg]
  congr 2
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [leaf_model, List.toList_data_toByteArray, window_after_pre]

/-- A canonical list prefix delegates to the unchanged exact payload cursor. -/
private theorem decode_prefix_list (body : List UInt8)
    (hw : (Uint.toBeBytes body.length).size ≤ 8) :
    decodeModel (lengthPrefixModel 192 247 body.length ++ body) =
      match joined (listInput (lengthPrefixModel 192 247 body.length ++ body))
          (lengthPrefixModel 192 247 body.length).length
          (lengthPrefixModel 192 247 body.length ++ body).length [] with
      | .error err => .error err
      | .ok xs => .ok (.list xs) := by
  obtain ⟨h, hh, hl, hs, hc, he, _, hstart⟩ :=
    header_prefix_canonical 192 247 body (Or.inr ⟨rfl, rfl⟩) hw
  rw [decodeModel, item_header_exact _ 0 _ h hh hs hc he]
  have hl' : h.isList = true := hl
  rw [ite_eq_left hl', hstart]

/-! ### Encoded item and ordered-child induction -/

mutual
  /-- Structural completeness preserves the entire item on the exact Q47 domain. -/
  private theorem item_inverse (x : RlpItem) (hx : Encodable x) :
      decodeModel (encodeModel x) = .ok x := by
    cases x with
    | bytes b =>
      by_cases hb : b.size = 1 ∧ (b[0]?.getD 128).toNat < 128
      · have hp : 0 < b.size := by omega
        have hv : b[0]? = some b[0] := getElem?_pos b 0 hp
        have ht : b[0].toNat < 128 := by
          simpa only [hv, Option.getD_some] using hb.2
        have hd : decode (encode (.bytes b)) = .ok (.bytes b) := by
          rw [encode_bytes, encodeBytes_single b b[0] hb.1 hv ht]
          exact decode_single b b[0] hb.1 hv ht
        rw [decode_eq_model, toList_encode] at hd
        exact hd
      · have hmodel : encodeModel (.bytes b) = lengthPrefixModel 128 183 b.size ++ b.data.toList :=
        by
          rw [encodeModel]
          split
          · next hy => exact False.elim (hb hy)
          · rfl
        rw [hmodel]
        have hw : (Uint.toBeBytes b.size).size ≤ 8 := by simpa only [Encodable] using hx
        have hn : ¬(b.data.toList.length = 1 ∧ (b.data.toList[0]?.getD 0).toNat < 128) := by
          intro hc
          have hs : b.size = 1 := by
            simpa only [Array.length_toList, ← ByteArray.size_data] using hc.1
          have hp : 0 < b.size := by omega
          have hv : b[0]? = some b[0] := getElem?_pos b 0 hp
          have he : b.data.toList[0]? = b[0]? := by rw [Array.getElem?_toList]; rfl
          apply hb
          refine ⟨hs, ?_⟩
          simpa only [he, hv, Option.getD_some] using hc.2
        have hd := decode_prefix_bytes b.data.toList
          (by simpa only [Array.length_toList, ← ByteArray.size_data] using hw) hn
        have he : b.data.toList.toByteArray = b := by
          apply ByteArray.ext
          apply Array.toList_inj.mp
          rw [List.toList_data_toByteArray]
        simpa only [Array.length_toList, ← ByteArray.size_data, he] using hd
    | list xs =>
      have hc : (∀ x ∈ xs, Encodable x) ∧
          (Uint.toBeBytes (encodePayloadModel xs).length).size ≤ 8 := by
        simpa only [Encodable] using hx
      rw [encodeModel, decode_prefix_list (encodePayloadModel xs) hc.2]
      have hj := joined_inverse xs hc.1
        (lengthPrefixModel 192 247 (encodePayloadModel xs).length ++ encodePayloadModel xs)
        (lengthPrefixModel 192 247 (encodePayloadModel xs).length).length
        (lengthPrefixModel 192 247 (encodePayloadModel xs).length ++ encodePayloadModel xs).length
        [] (by rw [List.length_append]; omega) (by omega) (window_after_pre _ _)
      rw [hj]
      rfl
  /-- Ordered payload completeness works in any bounded ambient window and accumulator. -/
  private theorem joined_inverse (xs : List RlpItem) (hx : ∀ x ∈ xs, Encodable x)
      (bs : List UInt8) (p e : Nat) (rev : List RlpItem)
      (hp : p ≤ e) (he : e ≤ bs.length)
      (hw : (bs.drop p).take (e - p) = encodePayloadModel xs) :
      joined (listInput bs) p e rev = .ok (rev.reverse ++ xs) := by
    cases xs with
    | nil =>
      have hl := congrArg List.length hw
      rw [window_length bs p e hp he, encodePayloadModel_nil, List.length_nil] at hl
      have hn : ¬p < e := by omega
      rw [joined, dite_eq_right hn, List.append_nil]
    | cons x xs =>
      have hx' : Encodable x := hx x (by simp)
      have hxs : ∀ y ∈ xs, Encodable y := by
        intro y hy
        exact hx y (by simp only [List.mem_cons]; exact Or.inr hy)
      rw [encodePayloadModel_cons] at hw
      have hl : e - p = (encodeModel x ++ encodePayloadModel xs).length := by
        rw [← hw, window_length bs p e hp he]
      rw [joined_window bs p e rev hp, hw, hl]
      obtain ⟨h, hh, hend⟩ := header_encoded x hx' (encodePayloadModel xs)
      have hpos : 0 < (encodeModel x ++ encodePayloadModel xs).length := by
        have := h.advances
        have := h.available
        omega
      have hbody : h.start + h.payload ≤ (encodeModel x ++ encodePayloadModel xs).length := by
        rw [hend, List.length_append]
        omega
      rw [joined, dite_eq_left hpos, hh]
      dsimp only
      rw [dite_eq_left hbody]
      have hi : item (listInput (encodeModel x ++ encodePayloadModel xs)) 0
          (h.start + h.payload) = .ok x := by
        rw [item_window _ 0 _ (by omega) hbody, List.drop_zero, Nat.sub_zero,
          hend, List.take_left]
        exact item_inverse x hx'
      rw [hi]
      dsimp only
      have hwindow : ((encodeModel x ++ encodePayloadModel xs).drop (h.start + h.payload)).take
          ((encodeModel x ++ encodePayloadModel xs).length - (h.start + h.payload)) =
            encodePayloadModel xs := by
        rw [hend]
        exact window_after_pre _ _
      rw [joined_inverse xs hxs _ _ _ (x :: rev) hbody (by omega) hwindow,
        List.reverse_cons, List.append_assoc, List.singleton_append]
end

/-! ### Public encoder round-trip laws -/

/-- Every Encodable item round-trips through the model decoder; `rlp.py:66–135,387–484`. -/
theorem decodeModel_encodeModel (x : RlpItem) (hx : Encodable x) :
    decodeModel (encodeModel x) = .ok x := item_inverse x hx

/-- Packed RLP round trip on exactly the standard encoding domain selected by Q47. -/
theorem decode_encode (x : RlpItem) (hx : Encodable x) : decode (encode x) = .ok x := by
  rw [decode_eq_model, toList_encode]
  exact decodeModel_encodeModel x hx

end STFSpec.Codec.Rlp
