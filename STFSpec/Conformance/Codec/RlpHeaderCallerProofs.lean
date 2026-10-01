/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Public RLP header caller proofs

Library `EthConformance`. Uses only public header/model and Base byte/endian laws;
no packed digit-loop implementation or replaceable Base storage is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Codec.RlpHeaderCallerProofs

open STFSpec.Base STFSpec.Codec STFSpec.Codec.Rlp

example (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos = itemLengthModel (b.data.toList.drop pos) :=
  decodeItemLength_eq_model b pos

example (b : ByteArray) (pos : Nat) (h : b.size ≤ pos) :
    decodeItemLength b pos = .error .empty := decodeItemLength_empty b pos h

example (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos = .error .empty ↔ b.size ≤ pos := decodeItemLength_empty_iff b pos

example (b : ByteArray) (pos : Nat) (hp : pos < b.size) (h : (b[pos]).toNat < 128) :
    decodeItemLength b pos = .ok 1 := decodeItemLength_single b pos hp h

example (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (lo : 128 ≤ (b[pos]).toNat) (hi : (b[pos]).toNat ≤ 183) :
    decodeItemLength b pos = .ok (1 + ((b[pos]).toNat - 128)) :=
  decodeItemLength_short_bytes b pos hp lo hi

example (b : ByteArray) (pos : Nat) (hp : pos < b.size)
    (lo : 192 ≤ (b[pos]).toNat) (hi : (b[pos]).toNat ≤ 247) :
    decodeItemLength b pos = .ok (1 + ((b[pos]).toNat - 192)) :=
  decodeItemLength_short_list b pos hp lo hi

-- Simultaneous header shortage and zero leading digit is still truncation.
example (b : ByteArray) (pos count : Nat) (hp : pos < b.size)
    (ht : (184 ≤ (b[pos]).toNat ∧ (b[pos]).toNat ≤ 191) ∨ 248 ≤ (b[pos]).toNat)
    (hc : count = if (b[pos]).toNat ≤ 191 then (b[pos]).toNat - 183
      else (b[pos]).toNat - 247)
    (h : b.size < pos + 1 + count) : decodeItemLength b pos = .error .truncated := by
  rw [decodeItemLength_long b pos hp ht]
  simp only [← hc]
  rw [dite_eq_right (by omega : ¬pos + 1 + count ≤ b.size)]

-- The endian bridge retains complete ordered digits and unbounded header addition.
example (b : ByteArray) (pos count : Nat) (hp : pos < b.size)
    (ht : (184 ≤ (b[pos]).toNat ∧ (b[pos]).toNat ≤ 191) ∨ 248 ≤ (b[pos]).toNat)
    (hc : count = if (b[pos]).toNat ≤ 191 then (b[pos]).toNat - 183
      else (b[pos]).toNat - 247)
    (hb : pos + 1 + count ≤ b.size)
    (hp1 : pos + 1 < b.size) (hz : b[pos + 1] ≠ 0) :
    decodeItemLength b pos = .ok (1 + count +
      Uint.ofBeBytes ((Bytes.ofByteArray b).extract (pos + 1) (pos + 1 + count))) := by
  rw [decodeItemLength_long b pos hp ht]
  simp only [← hc]
  rw [dite_eq_left hb, ite_eq_right hz]

example (tag : UInt8)
    (h : (184 ≤ tag.toNat ∧ tag.toNat ≤ 191) ∨ 248 ≤ tag.toNat) :
    let count := if tag.toNat ≤ 191 then tag.toNat - 183 else tag.toNat - 247
    1 ≤ count ∧ count ≤ 8 := length_digits_bound tag h

example (b : ByteArray) (start stop offset : Nat) :
    decodeItemLength ((Bytes.ofByteArray b).extract start stop).toByteArray offset =
      itemLengthModel (((b.data.toList.drop start).take (stop - start)).drop offset) :=
  decodeItemLength_window b start stop offset

example (b : ByteArray) (pos : Nat) :
    decodeItemLength b pos =
      decodeItemLength ((Bytes.ofByteArray b).extract pos b.size).toByteArray 0 :=
  decodeItemLength_suffix b pos

example (b c : ByteArray) (pos offset : Nat)
    (h : (b.data.toList.drop pos).take 9 = (c.data.toList.drop offset).take 9) :
    decodeItemLength b pos = decodeItemLength c offset :=
  decodeItemLength_header_congr b c pos offset h

example (b : ByteArray) (pos extent : Nat) (h : decodeItemLength b pos = .ok extent) :
    ∃ count payload, count ≤ 8 ∧ payload < 2 ^ 64 ∧ extent = 1 + count + payload :=
  decodeItemLength_success_bound b pos extent h

example (b : ByteArray) (pos extent : Nat) (h : decodeItemLength b pos = .ok extent) :
    0 < extent := decodeItemLength_pos b pos extent h

example (b : ByteArray) (pos extent : Nat) (h : decodeItemLength b pos = .ok extent) :
    extent < 2 ^ 64 + 9 := decodeItemLength_lt b pos extent h

end STFSpec.Conformance.Codec.RlpHeaderCallerProofs
