/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Blake2Parameters

/-!
# BLAKE2F codec composition clients

Library `EthConformance`: callers consume public byte/word and codec laws without
unfolding the implementation. These are parameter parsing proofs, before gas and
flag validation in `EthPrecompiles`.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3,7–8.
-/

open STFSpec.Hash.Blake2b

example (p : Params) : getParameters (serialize p) (serialize_size p) = p :=
  getParameters_serialize p

example (data : ByteArray) (h : data.size = 213) :
    serialize (getParameters data h) = data := serialize_getParameters data h

-- The serializer is injective on every raw parameter record.
example (p q : Params) (he : serialize p = serialize q) : p = q := by
  exact (getParameters_serialize p).symm.trans
    ((getParameters_congr _ _ (serialize_size p) (serialize_size q) he).trans
      (getParameters_serialize q))

-- The parser is injective on the caller-checked domain.
example (a b : ByteArray) (ha : a.size = 213) (hb : b.size = 213)
    (he : getParameters a ha = getParameters b hb) : a = b := by
  exact (serialize_getParameters a ha).symm.trans
    ((congrArg serialize he).trans (serialize_getParameters b hb))

-- The round bytes run high-to-low, while each state lane runs low-to-high.
example (data : ByteArray) (h : data.size = 213) (j : Fin 4) :
    wordByte (n := 4) (getParameters data h).rounds.toBitVec j =
      inputByte data h ⟨3 - j.val, by omega⟩ := by
  rw [getParameters_rounds, wordByte_leWord]

example (data : ByteArray) (h : data.size = 213) (i j : Fin 8) :
    wordByte (n := 8) ((getParameters data h).h.get i).toBitVec j =
      inputByte data h ⟨4 + 8 * i.val + j.val, by omega⟩ := by
  rw [getParameters_h, wordByte_leWord]

example (data : ByteArray) (h : data.size = 213) (i : Fin 16) (j : Fin 8) :
    wordByte (n := 8) ((getParameters data h).m.get i).toBitVec j =
      inputByte data h ⟨68 + 8 * i.val + j.val, by omega⟩ := by
  rw [getParameters_m, wordByte_leWord]

example (data : ByteArray) (h : data.size = 213) (j : Fin 8) :
    wordByte (n := 8) (getParameters data h).t0.toBitVec j =
      inputByte data h ⟨196 + j.val, by omega⟩ := by
  rw [getParameters_t0, wordByte_leWord]

example (data : ByteArray) (h : data.size = 213) (j : Fin 8) :
    wordByte (n := 8) (getParameters data h).t1.toBitVec j =
      inputByte data h ⟨204 + j.val, by omega⟩ := by
  rw [getParameters_t1, wordByte_leWord]

-- The serializer preserves a raw flag of any UInt8 value.
example (p : Params) : (getParameters (serialize p) (serialize_size p)).f = p.f := by
  rw [getParameters_serialize]

-- Clients can reason about numeric digits using the public radix-256 law.
example (word : UInt64) (j : Fin 8) :
    (wordByte (n := 8) word.toBitVec j).toNat = word.toNat / 256 ^ j.val % 256 :=
  wordByte_toNat word.toBitVec j
