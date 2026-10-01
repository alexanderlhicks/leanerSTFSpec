/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpItem

/-!
# Packed RLP item-length observations

Library `EthCodec`. Locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:488–543`.
The cursor reads the original packed input: one tag and at most eight digits.
Declared extent is distinct from successful whole-item decoding; missing payload,
noncanonical short/long forms and trailing bytes are left to `decode` and its caller
(`rlp.py:385–484`). No host-depth or guest-outcome correspondence is asserted.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec.Rlp

open STFSpec.Base

private def readDigits (b : ByteArray) :
    (count pos : Nat) → pos + count ≤ b.size → Nat → Nat
  | 0, _, _, acc => acc
  | count + 1, pos, h, acc =>
      readDigits b count (pos + 1) (by omega) (256 * acc + (b[pos]'(by omega)).toNat)

private theorem readDigits_model (b : ByteArray) (count pos : Nat)
    (h : pos + count ≤ b.size) (acc : Nat) :
    readDigits b count pos h acc =
      ((b.data.toList.drop pos).take count).foldl (fun a v ↦ 256 * a + v.toNat) acc := by
  induction count generalizing pos acc with
  | zero => simp [readDigits]
  | succ count ih =>
    have hp : pos < b.data.toList.length := by
      rw [Array.length_toList]
      change _ < b.size
      omega
    rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, List.foldl_cons]
    rw [readDigits, ih]
    rfl

private theorem readDigits_endian (b : ByteArray) (pos count : Nat)
    (h : pos + count ≤ b.size) :
    readDigits b count pos h 0 =
      Uint.ofBeBytes ((Bytes.ofByteArray b).extract pos (pos + count)) := by
  rw [Uint.ofBeBytes_eq_fold, Bytes.toList_extract, Bytes.toList_ofByteArray,
    Nat.add_sub_cancel_left, readDigits_model]

private def longLength (b : ByteArray) (pos count : Nat) (hc : 0 < count) :
    Except RlpError Nat :=
  if h : pos + 1 + count ≤ b.size then
    if b[pos + 1]'(by omega) = 0 then .error (.nonCanonical "leading zero length") else
      .ok (1 + count + readDigits b count (pos + 1) h 0)
  else .error .truncated

private def longLengthModel (body : List UInt8) (count : Nat) : Except RlpError Nat :=
  if count ≤ body.length then
    if body.head? = some 0 then .error (.nonCanonical "leading zero length") else
      .ok (1 + count + Uint.ofBeBytes (Bytes.ofList (body.take count)))
  else .error .truncated

/-- Readable suffix model of `ethereum_rlp/rlp.py:488–543` (locked 0.1.6).
It observes headers only, without checking payload availability or canonical item forms. -/
def itemLengthModel : List UInt8 → Except RlpError Nat
  | [] => .error .empty
  | tag :: body =>
      if tag.toNat < 128 then .ok 1 else
      if tag.toNat ≤ 183 then .ok (1 + (tag.toNat - 128)) else
      if tag.toNat ≤ 191 then longLengthModel body (tag.toNat - 183) else
      if tag.toNat ≤ 247 then .ok (1 + (tag.toNat - 192)) else
        longLengthModel body (tag.toNat - 247)

/-- Declared encoded extent at a cursor; locked `ethereum_rlp/rlp.py:488–543`.
Corresponds to `decode_item_length(b[pos:])`, with unbounded natural offsets and
extent arithmetic. Header truncation precedes leading-zero rejection. Only long
length digits are traversed; this does not decode or allocate the declared payload. -/
def decodeItemLength (b : ByteArray) (pos : Nat) : Except RlpError Nat :=
  if h : pos < b.size then
    let tag := (b[pos]'h).toNat
    if hsingle : tag < 128 then .ok 1 else
    if hshort : tag ≤ 183 then .ok (1 + (tag - 128)) else
    if hbytes : tag ≤ 191 then longLength b pos (tag - 183) (by omega) else
    if hlist : tag ≤ 247 then .ok (1 + (tag - 192)) else
      longLength b pos (tag - 247) (by omega)
  else .error .empty

private theorem longLength_eq_model (b : ByteArray) (pos count : Nat) (hc : 0 < count) :
    longLength b pos count hc = longLengthModel (b.data.toList.drop (pos + 1)) count := by
  unfold longLength longLengthModel
  have hl : (b.data.toList.drop (pos + 1)).length = b.size - (pos + 1) := by
    simp only [List.length_drop, Array.length_toList, ← ByteArray.size_data]
  by_cases h : pos + 1 + count ≤ b.size
  · have hd : count ≤ (b.data.toList.drop (pos + 1)).length := by rw [hl]; omega
    rw [dite_eq_left h, ite_eq_left hd]
    have hp : pos + 1 < b.data.toList.length := by
      rw [Array.length_toList]
      change _ < b.size
      omega
    have hh : (b.data.toList.drop (pos + 1)).head? = some b[pos + 1] := by
      rw [List.drop_eq_getElem_cons hp, List.head?_cons]
      rfl
    simp only [hh, Option.some.injEq]
    rw [readDigits_model]
    rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofList]
  · have hd : ¬count ≤ (b.data.toList.drop (pos + 1)).length := by rw [hl]; omega
    rw [dite_eq_right h, ite_eq_right hd]

/-- Packed cursor scanning equals the readable suffix model for every offset,
including conceptual offsets too large for a machine index. -/
theorem decodeItemLength_eq_model (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos = itemLengthModel (b.data.toList.drop pos) := by
  unfold decodeItemLength
  split
  · next hp =>
    have hl : pos < b.data.toList.length := by
      simpa only [Array.length_toList, ← ByteArray.size_data] using hp
    rw [List.drop_eq_getElem_cons hl, itemLengthModel]
    simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
    change (if (b[pos]).toNat < 128 then _ else _) = _
    split
    · rfl
    · split
      · rfl
      · split
        · exact longLength_eq_model b pos _ _
        · split
          · rfl
          · exact longLength_eq_model b pos _ _
  · next hp =>
    rw [List.drop_of_length_le (by
      simpa only [Array.length_toList, ← ByteArray.size_data] using Nat.not_lt.mp hp)]
    rfl

/-- End or out-of-range cursors fail before any packed read. -/
theorem decodeItemLength_empty (b : ByteArray) (pos : Nat) (h : b.size ≤ pos) :
    decodeItemLength b pos = .error .empty := by
  simp only [decodeItemLength, dite_eq_right (by omega : ¬pos < b.size)]

/-- Literal bytes below 0x80 declare extent one, independently of following bytes. -/
theorem decodeItemLength_single (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (h : (b[pos]).toNat < 128) : decodeItemLength b pos = .ok 1 := by
  simp only [decodeItemLength, dite_eq_left hp, dite_eq_left h]

/-- Short strings declare one tag plus their payload length; no payload read is needed. -/
theorem decodeItemLength_short_bytes (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (lo : 128 ≤ (b[pos]).toNat) (hi : (b[pos]).toNat ≤ 183) :
    decodeItemLength b pos = .ok (1 + ((b[pos]).toNat - 128)) := by
  simp only [decodeItemLength, dite_eq_left hp, dite_eq_right (by omega : ¬(b[pos]).toNat < 128),
    dite_eq_left hi]

/-- Short lists declare their encoded payload width, without inspecting children. -/
theorem decodeItemLength_short_list (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (lo : 192 ≤ (b[pos]).toNat) (hi : (b[pos]).toNat ≤ 247) :
    decodeItemLength b pos = .ok (1 + ((b[pos]).toNat - 192)) := by
  simp only [decodeItemLength, dite_eq_left hp, dite_eq_right (by omega : ¬(b[pos]).toNat < 128),
    dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 183),
    dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 191), dite_eq_left hi]

/-- Exact long-header equation for both byte-string and list tags. Header truncation
comes first; all digit values are interpreted by the public Base endian model. -/
theorem decodeItemLength_long (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (ht : (184 ≤ (b[pos]).toNat ∧ (b[pos]).toNat ≤ 191) ∨ 248 ≤ (b[pos]).toNat) :
    let count := if (b[pos]).toNat ≤ 191 then (b[pos]).toNat - 183 else (b[pos]).toNat - 247
    decodeItemLength b pos =
      if h : pos + 1 + count ≤ b.size then
        if b[pos + 1]'(by
            have hc : 0 < count := by
              dsimp only [count]
              split <;> omega
            omega) = 0 then
          .error (.nonCanonical "leading zero length") else
          .ok (1 + count +
            Uint.ofBeBytes ((Bytes.ofByteArray b).extract (pos + 1) (pos + 1 + count)))
      else .error .truncated := by
  dsimp only
  rcases ht with ht | ht
  · simp only [decodeItemLength, dite_eq_left hp,
      dite_eq_right (by omega : ¬(b[pos]).toNat < 128),
      dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 183),
      dite_eq_left ht.2, ite_eq_left ht.2, longLength]
    split
    · rw [readDigits_endian]
    · rfl
  · simp only [decodeItemLength, dite_eq_left hp,
      dite_eq_right (by omega : ¬(b[pos]).toNat < 128),
      dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 183),
      dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 191),
      ite_eq_right (by omega : ¬(b[pos]).toNat ≤ 191),
      dite_eq_right (by omega : ¬(b[pos]).toNat ≤ 247), longLength]
    split
    · rw [readDigits_endian]
    · rfl

/-- Long tags carry between one and eight length digits, for both item kinds. -/
theorem length_digits_bound (tag : UInt8)
    (h : (184 ≤ tag.toNat ∧ tag.toNat ≤ 191) ∨ 248 ≤ tag.toNat) :
    let count := if tag.toNat ≤ 191 then tag.toNat - 183 else tag.toNat - 247
    1 ≤ count ∧ count ≤ 8 := by
  have := tag.toNat_lt
  dsimp only
  split <;> omega

/-- Slicing a window is a proof observation only: the executable scanner reads the
original buffer. This equation also covers empty windows and arbitrarily large offsets. -/
theorem decodeItemLength_window (b : ByteArray) (start stop offset : Nat) :
    decodeItemLength ((Bytes.ofByteArray b).extract start stop).toByteArray offset =
      itemLengthModel (((b.data.toList.drop start).take (stop - start)).drop offset) := by
  rw [decodeItemLength_eq_model, Bytes.toList_toByteArray, Bytes.toList_extract,
    Bytes.toList_ofByteArray]

/-- Moving a cursor to zero in its suffix preserves the complete result. -/
theorem decodeItemLength_suffix (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos =
      decodeItemLength ((Bytes.ofByteArray b).extract pos b.size).toByteArray 0 := by
  rw [decodeItemLength_eq_model, decodeItemLength_window, List.drop_zero]
  have hl : (b.data.toList.drop pos).length = b.size - pos := by
    simp only [List.length_drop, Array.length_toList, ← ByteArray.size_data]
  rw [← hl, List.take_length]

private theorem longLengthModel_take_eight (body : List UInt8) (count : Nat)
    (hpos : 0 < count) (hcount : count ≤ 8) :
    longLengthModel body count = longLengthModel (body.take 8) count := by
  unfold longLengthModel
  have hb : count ≤ body.length ↔ count ≤ (body.take 8).length := by
    rw [List.length_take]
    omega
  by_cases h : count ≤ body.length
  · simp only [ite_eq_left h, ite_eq_left (hb.mp h)]
    simp only [List.head?_take, show ¬(8 : Nat) = 0 by decide, ite_false,
      List.take_take, Nat.min_eq_left hcount]
  · rw [ite_eq_right h, ite_eq_right (fun ht ↦ h (hb.mpr ht))]

/-- At most nine available bytes determine the whole header observation. -/
theorem itemLengthModel_take_nine (xs : List UInt8) :
    itemLengthModel xs = itemLengthModel (xs.take 9) := by
  cases xs with
  | nil => rfl
  | cons tag body =>
    simp only [List.take_succ_cons, itemLengthModel]
    split
    · rfl
    · split
      · rfl
      · split
        · apply longLengthModel_take_eight <;> omega
        · split
          · rfl
          · have := tag.toNat_lt
            apply longLengthModel_take_eight <;> omega

/-- Bytes outside the bounded header window cannot affect the result. Availability
inside that window is preserved by list equality; no equal total-size premise is needed. -/
theorem decodeItemLength_header_congr (b c : ByteArray) (pos offset : Nat)
    (h : (b.data.toList.drop pos).take 9 = (c.data.toList.drop offset).take 9) :
    decodeItemLength b pos = decodeItemLength c offset := by
  rw [decodeItemLength_eq_model, decodeItemLength_eq_model,
    itemLengthModel_take_nine (b.data.toList.drop pos), h,
    ← itemLengthModel_take_nine]

private theorem longLengthModel_success_bound (body : List UInt8) (count extent : Nat)
    (hc : count ≤ 8) (h : longLengthModel body count = .ok extent) :
    ∃ payload, payload < 2 ^ 64 ∧ extent = 1 + count + payload := by
  unfold longLengthModel at h
  split at h
  · split at h
    · cases h
    · have he := Except.ok.inj h
      refine ⟨Uint.ofBeBytes (Bytes.ofList (body.take count)), ?_, he.symm⟩
      apply Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt _)
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      rw [Bytes.size_ofList, List.length_take]
      omega
  · cases h

/-- Every success has a bounded payload number and at most eight digits, while
adding the tag and digit count uses unbounded Nat arithmetic. -/
theorem decodeItemLength_success_bound (b : ByteArray) (pos extent : Nat)
    (h : decodeItemLength b pos = .ok extent) :
    ∃ count payload, count ≤ 8 ∧ payload < 2 ^ 64 ∧ extent = 1 + count + payload := by
  rw [decodeItemLength_eq_model] at h
  cases hx : b.data.toList.drop pos with
  | nil => simp only [hx, itemLengthModel] at h; cases h
  | cons tag body =>
    simp only [hx, itemLengthModel] at h
    split at h
    · cases h
      exact ⟨0, 0, by decide, by decide, rfl⟩
    · split at h
      · have he := Except.ok.inj h
        refine ⟨0, tag.toNat - 128, by decide, ?_, ?_⟩
        · have hb : tag.toNat - 128 < 256 := by have := tag.toNat_lt; omega
          exact Nat.lt_trans hb (by decide)
        · omega
      · split at h
        · obtain ⟨payload, hb, he⟩ := longLengthModel_success_bound body
            (tag.toNat - 183) extent (by omega) h
          exact ⟨_, payload, by omega, hb, he⟩
        · split at h
          · have he := Except.ok.inj h
            refine ⟨0, tag.toNat - 192, by decide, ?_, ?_⟩
            · have hb : tag.toNat - 192 < 256 := by have := tag.toNat_lt; omega
              exact Nat.lt_trans hb (by decide)
            · omega
          · have ht := tag.toNat_lt
            obtain ⟨payload, hb, he⟩ := longLengthModel_success_bound body
              (tag.toNat - 247) extent (by omega) h
            exact ⟨_, payload, by omega, hb, he⟩

/-- A successful item-length observation always advances by a positive extent. -/
theorem decodeItemLength_pos (b : ByteArray) (pos extent : Nat)
    (h : decodeItemLength b pos = .ok extent) : 0 < extent := by
  obtain ⟨count, payload, _, _, he⟩ := decodeItemLength_success_bound b pos extent h
  omega

/-- The largest possible header extent is bounded without narrowing to UInt64. -/
theorem decodeItemLength_lt (b : ByteArray) (pos extent : Nat)
    (h : decodeItemLength b pos = .ok extent) : extent < 2 ^ 64 + 9 := by
  obtain ⟨count, payload, hc, hb, he⟩ := decodeItemLength_success_bound b pos extent h
  omega

/-- Empty is exactly the out-of-range case; malformed long headers use other diagnostics. -/
theorem decodeItemLength_empty_iff (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos = .error .empty ↔ b.size ≤ pos := by
  constructor
  · intro he
    by_cases hn : b.size ≤ pos
    · exact hn
    have hp : pos < b.size := by omega
    rw [decodeItemLength_eq_model, List.drop_eq_getElem_cons
      (by simpa only [Array.length_toList, ← ByteArray.size_data] using hp)] at he
    simp only [itemLengthModel, longLengthModel] at he
    split at he
    · cases he
    · split at he
      · cases he
      · split at he
        · split at he
          · split at he <;> cases he
          · cases he
        · split at he
          · cases he
          · split at he
            · split at he <;> cases he
            · cases he
  · exact decodeItemLength_empty b pos

end STFSpec.Codec.Rlp
