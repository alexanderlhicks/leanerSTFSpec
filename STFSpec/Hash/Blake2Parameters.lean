/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes

/-!
# BLAKE2F raw parameters

Library `EthHash`. EELS `crypto/blake2.py:10–32,133–150` at the pin in
`reference.toml`; layout and contract: `STFSpec/informal/modules/EthHash.md` R5.
The size premise belongs to the caller. All round counts and flag bytes are retained.
-/

namespace STFSpec.Hash.Blake2b

/-- Raw EIP-152 parameters, before the precompile's gas and flag checks. -/
structure Params where
  rounds : UInt32
  h : Vector UInt64 8
  m : Vector UInt64 16
  t0 : UInt64
  t1 : UInt64
  f : UInt8
  deriving DecidableEq, Repr

/-- Equality of all six raw fields determines the record. -/
@[ext] theorem Params.ext {p q : Params} (hr : p.rounds = q.rounds)
    (hh : p.h = q.h) (hm : p.m = q.m) (ht0 : p.t0 = q.t0)
    (ht1 : p.t1 = q.t1) (hf : p.f = q.f) : p = q := by
  cases p
  cases q
  simp_all

/-- Little-endian byte concatenation: the first byte occupies the low eight bits. -/
def leWord : (n : Nat) → (Fin n → UInt8) → BitVec (8 * n)
  | 0, _ => 0#0
  | n + 1, bytes =>
    ((leWord n (fun i => bytes i.succ)) ++ (bytes ⟨0, by omega⟩).toBitVec).cast (by omega)

/-- The low-to-high byte at a word position. -/
def wordByte {n : Nat} (word : BitVec (8 * n)) (i : Fin n) : UInt8 :=
  UInt8.ofBitVec (word.extractLsb' (8 * i.val) 8)

private theorem leWord_bit (n : Nat) (bytes : Fin n → UInt8) (i : Nat)
    (hi : i < 8 * n) :
    (leWord n bytes).getLsbD i =
      (bytes ⟨i / 8, by omega⟩).toBitVec.getLsbD (i % 8) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [leWord, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases h : i < 8
    · simp only [h, ↓reduceIte]
      have hd : i / 8 = 0 := by omega
      have hm : i % 8 = i := by omega
      simp [hd, hm]
    · simp only [h, ↓reduceIte]
      rw [ih _ _ (by omega)]
      have hd : (i - 8) / 8 + 1 = i / 8 := by omega
      have hm : (i - 8) % 8 = i % 8 := by omega
      simp only [hm]
      congr 2
      apply congrArg bytes
      apply Fin.ext
      exact hd

/-- Every byte of little-endian concatenation is recovered, including high bits. -/
theorem wordByte_leWord (n : Nat) (bytes : Fin n → UInt8) (i : Fin n) :
    wordByte (leWord n bytes) i = bytes i := by
  apply UInt8.toBitVec_inj.mp
  simp only [wordByte, UInt8.toBitVec_ofBitVec]
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [BitVec.getElem_extractLsb', leWord_bit _ _ _ (by omega)]
  have hd : (8 * i.val + k) / 8 = i.val := by omega
  have hm : (8 * i.val + k) % 8 = k := by omega
  simp only [hd, hm]
  exact BitVec.getLsbD_eq_getElem hk

/-- Concatenating all low-to-high bytes recovers the entire word. -/
theorem leWord_wordByte {n : Nat} (word : BitVec (8 * n)) :
    leWord n (wordByte word) = word := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [← BitVec.getLsbD_eq_getElem, leWord_bit _ _ _ hk]
  simp only [wordByte, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb']
  have hm : k % 8 < 8 := by omega
  have he : 8 * (k / 8) + k % 8 = k := by omega
  simp only [hm, he, decide_true, Bool.true_and]
  exact BitVec.getLsbD_eq_getElem hk

/-- Byte observation of the raw 213-byte caller-checked input. -/
def inputByte (data : ByteArray) (h : data.size = 213) (i : Fin 213) : UInt8 :=
  data[i.val]'(by omega)

/-- EELS `get_blake2_parameters`: four big-endian round bytes, then 26
little-endian 64-bit words and one raw flag byte. -/
def getParameters (data : ByteArray) (h : data.size = 213) : Params :=
  let b := inputByte data h
  { rounds := UInt32.ofBitVec (leWord 4 (fun i => b ⟨3 - i.val, by omega⟩))
    h := Vector.ofFn (fun i => UInt64.ofBitVec
      (leWord 8 (fun j => b ⟨4 + 8 * i.val + j.val, by omega⟩)))
    m := Vector.ofFn (fun i => UInt64.ofBitVec
      (leWord 8 (fun j => b ⟨68 + 8 * i.val + j.val, by omega⟩)))
    t0 := UInt64.ofBitVec (leWord 8 (fun j => b ⟨196 + j.val, by omega⟩))
    t1 := UInt64.ofBitVec (leWord 8 (fun j => b ⟨204 + j.val, by omega⟩))
    f := b ⟨212, by omega⟩ }

/-- Parsing is independent of the proof of input size and respects input equality. -/
theorem getParameters_congr (a b : ByteArray) (ha : a.size = 213) (hb : b.size = 213)
    (he : a = b) : getParameters a ha = getParameters b hb := by
  cases he
  rfl

/-- Exact byte layout of the serializer, including the unvalidated flag byte. -/
def parameterByte (p : Params) (i : Fin 213) : UInt8 :=
  if h0 : i.val < 4 then
    wordByte (n := 4) p.rounds.toBitVec ⟨3 - i.val, by omega⟩
  else if h1 : i.val < 68 then
    wordByte (n := 8) (p.h.get ⟨(i.val - 4) / 8, by omega⟩).toBitVec ⟨(i.val - 4) % 8, by omega⟩
  else if h2 : i.val < 196 then
    wordByte (n := 8) (p.m.get ⟨(i.val - 68) / 8, by omega⟩).toBitVec ⟨(i.val - 68) % 8, by omega⟩
  else if h3 : i.val < 204 then
    wordByte (n := 8) p.t0.toBitVec ⟨i.val - 196, by omega⟩
  else if h4 : i.val < 212 then
    wordByte (n := 8) p.t1.toBitVec ⟨i.val - 204, by omega⟩
  else p.f

/-- Serializer witness for the raw parameter bijection. -/
def serialize (p : Params) : ByteArray := ⟨Array.ofFn (parameterByte p)⟩

/-- The raw parameter serialization always has exactly the required size. -/
theorem serialize_size (p : Params) : (serialize p).size = 213 := by
  simp [serialize, ByteArray.size]

set_option maxRecDepth 1024 in
/-- Serializer byte access agrees with the explicit layout. -/
theorem inputByte_serialize (p : Params) (i : Fin 213) :
    inputByte (serialize p) (serialize_size p) i = parameterByte p i := by
  simp only [inputByte, ByteArray.getElem_eq_getElem_data, serialize, Array.getElem_ofFn]

/-- Parsed round bits are the big-endian reversal of bytes 0 through 3. -/
theorem getParameters_rounds (data : ByteArray) (h : data.size = 213) :
    (getParameters data h).rounds.toBitVec =
      leWord 4 (fun i => inputByte data h ⟨3 - i.val, by omega⟩) := rfl

/-- Every parsed chaining-state lane has its own eight-byte little-endian window. -/
theorem getParameters_h (data : ByteArray) (h : data.size = 213) (i : Fin 8) :
    ((getParameters data h).h.get i).toBitVec =
      leWord 8 (fun j => inputByte data h ⟨4 + 8 * i.val + j.val, by omega⟩) := by
  simp [getParameters, Vector.get]
  rfl

/-- Every parsed message lane has its own eight-byte little-endian window. -/
theorem getParameters_m (data : ByteArray) (h : data.size = 213) (i : Fin 16) :
    ((getParameters data h).m.get i).toBitVec =
      leWord 8 (fun j => inputByte data h ⟨68 + 8 * i.val + j.val, by omega⟩) := by
  simp [getParameters, Vector.get]
  rfl

/-- The low counter word observes bytes 196 through 203. -/
theorem getParameters_t0 (data : ByteArray) (h : data.size = 213) :
    (getParameters data h).t0.toBitVec =
      leWord 8 (fun j => inputByte data h ⟨196 + j.val, by omega⟩) := rfl

/-- The high counter word observes bytes 204 through 211. -/
theorem getParameters_t1 (data : ByteArray) (h : data.size = 213) :
    (getParameters data h).t1.toBitVec =
      leWord 8 (fun j => inputByte data h ⟨204 + j.val, by omega⟩) := rfl

/-- Parsing retains all possible flag values, without a Boolean coercion. -/
theorem getParameters_f (data : ByteArray) (h : data.size = 213) :
    (getParameters data h).f = inputByte data h ⟨212, by omega⟩ := rfl


private theorem parameterByte_rounds (p : Params) (i : Fin 4) :
    parameterByte p ⟨3 - i.val, by omega⟩ = wordByte (n := 4) p.rounds.toBitVec i := by
  simp only [parameterByte, show 3 - i.val < 4 by omega, ↓reduceDIte]
  congr 1
  apply Fin.ext
  change 3 - (3 - i.val) = i.val
  omega

private theorem parameterByte_h (p : Params) (i : Fin 8) (j : Fin 8) :
    parameterByte p ⟨4 + 8 * i.val + j.val, by omega⟩ =
      wordByte (n := 8) (p.h.get i).toBitVec j := by
  simp only [parameterByte, show ¬4 + 8 * i.val + j.val < 4 by omega,
    show 4 + 8 * i.val + j.val < 68 by omega, ↓reduceDIte]
  have hd : (4 + 8 * i.val + j.val - 4) / 8 = i.val := by omega
  have hm : (4 + 8 * i.val + j.val - 4) % 8 = j.val := by omega
  simp only [hd, hm]

private theorem parameterByte_m (p : Params) (i : Fin 16) (j : Fin 8) :
    parameterByte p ⟨68 + 8 * i.val + j.val, by omega⟩ =
      wordByte (n := 8) (p.m.get i).toBitVec j := by
  simp only [parameterByte, show ¬68 + 8 * i.val + j.val < 4 by omega,
    show ¬68 + 8 * i.val + j.val < 68 by omega,
    show 68 + 8 * i.val + j.val < 196 by omega, ↓reduceDIte]
  have hd : (68 + 8 * i.val + j.val - 68) / 8 = i.val := by omega
  have hm : (68 + 8 * i.val + j.val - 68) % 8 = j.val := by omega
  simp only [hd, hm]

private theorem parameterByte_t0 (p : Params) (j : Fin 8) :
    parameterByte p ⟨196 + j.val, by omega⟩ = wordByte (n := 8) p.t0.toBitVec j := by
  simp only [parameterByte, show ¬196 + j.val < 4 by omega,
    show ¬196 + j.val < 68 by omega, show ¬196 + j.val < 196 by omega,
    show 196 + j.val < 204 by omega, ↓reduceDIte]
  simp only [Nat.add_sub_cancel_left]

private theorem parameterByte_t1 (p : Params) (j : Fin 8) :
    parameterByte p ⟨204 + j.val, by omega⟩ = wordByte (n := 8) p.t1.toBitVec j := by
  simp only [parameterByte, show ¬204 + j.val < 4 by omega,
    show ¬204 + j.val < 68 by omega, show ¬204 + j.val < 196 by omega,
    show ¬204 + j.val < 204 by omega, show 204 + j.val < 212 by omega, ↓reduceDIte]
  simp only [Nat.add_sub_cancel_left]

/-- Serialization and parsing recover every raw parameter record. -/
theorem getParameters_serialize (p : Params) :
    getParameters (serialize p) (serialize_size p) = p := by
  have hr : (getParameters (serialize p) (serialize_size p)).rounds = p.rounds := by
    apply UInt32.toBitVec_inj.mp
    rw [getParameters_rounds]
    simp only [inputByte_serialize, parameterByte_rounds, leWord_wordByte]
  have hh : (getParameters (serialize p) (serialize_size p)).h = p.h := by
    apply Vector.ext
    intro i hi
    apply UInt64.toBitVec_inj.mp
    change ((getParameters (serialize p) (serialize_size p)).h.get ⟨i, hi⟩).toBitVec = _
    rw [getParameters_h]
    simp only [inputByte_serialize, parameterByte_h p ⟨i, hi⟩, leWord_wordByte]
    rfl
  have hm : (getParameters (serialize p) (serialize_size p)).m = p.m := by
    apply Vector.ext
    intro i hi
    apply UInt64.toBitVec_inj.mp
    change ((getParameters (serialize p) (serialize_size p)).m.get ⟨i, hi⟩).toBitVec = _
    rw [getParameters_m]
    simp only [inputByte_serialize, parameterByte_m p ⟨i, hi⟩, leWord_wordByte]
    rfl
  have ht0 : (getParameters (serialize p) (serialize_size p)).t0 = p.t0 := by
    apply UInt64.toBitVec_inj.mp
    rw [getParameters_t0]
    simp only [inputByte_serialize, parameterByte_t0, leWord_wordByte]
  have ht1 : (getParameters (serialize p) (serialize_size p)).t1 = p.t1 := by
    apply UInt64.toBitVec_inj.mp
    rw [getParameters_t1]
    simp only [inputByte_serialize, parameterByte_t1, leWord_wordByte]
  have hf : (getParameters (serialize p) (serialize_size p)).f = p.f := by
    rw [getParameters_f, inputByte_serialize]
    simp [parameterByte]
  exact Params.ext hr hh hm ht0 ht1 hf


/-- Numeric radix-256 equation for the little-endian model. -/
theorem leWord_succ_toNat (n : Nat) (bytes : Fin (n + 1) → UInt8) :
    (leWord (n + 1) bytes).toNat =
      256 * (leWord n (fun i => bytes i.succ)).toNat + (bytes ⟨0, by omega⟩).toNat := by
  simp only [leWord, BitVec.toNat_cast, BitVec.toNat_append]
  change (leWord n (fun i => bytes i.succ)).toNat <<< 8 ||| (bytes ⟨0, by omega⟩).toNat = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (bytes ⟨0, by omega⟩).toNat_lt]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-- The numeric observation of a word byte is its radix-256 digit. -/
theorem wordByte_toNat {n : Nat} (word : BitVec (8 * n)) (i : Fin n) :
    (wordByte word i).toNat = word.toNat / 256 ^ i.val % 256 := by
  simp only [wordByte, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_mul]

/-- The explicit byte layout of parsed parameters recovers every input byte. -/
theorem parameterByte_getParameters (data : ByteArray) (h : data.size = 213) (i : Fin 213) :
    parameterByte (getParameters data h) i = inputByte data h i := by
  unfold parameterByte
  split
  next h0 =>
    rw [getParameters_rounds, wordByte_leWord]
    apply congrArg (inputByte data h)
    apply Fin.ext
    change 3 - (3 - i.val) = i.val
    omega
  next h0 =>
    split
    next h1 =>
      rw [getParameters_h, wordByte_leWord]
      apply congrArg (inputByte data h)
      apply Fin.ext
      change 4 + 8 * ((i.val - 4) / 8) + (i.val - 4) % 8 = i.val
      omega
    next h1 =>
      split
      next h2 =>
        rw [getParameters_m, wordByte_leWord]
        apply congrArg (inputByte data h)
        apply Fin.ext
        change 68 + 8 * ((i.val - 68) / 8) + (i.val - 68) % 8 = i.val
        omega
      next h2 =>
        split
        next h3 =>
          rw [getParameters_t0, wordByte_leWord]
          apply congrArg (inputByte data h)
          apply Fin.ext
          change 196 + (i.val - 196) = i.val
          omega
        next h3 =>
          split
          next h4 =>
            rw [getParameters_t1, wordByte_leWord]
            apply congrArg (inputByte data h)
            apply Fin.ext
            change 204 + (i.val - 204) = i.val
            omega
          next h4 =>
            rw [getParameters_f]
            apply congrArg (inputByte data h)
            apply Fin.ext
            change 212 = i.val
            omega

/-- Bounded byte observations determine a 213-byte input. -/
theorem inputByte_ext (a b : ByteArray) (ha : a.size = 213) (hb : b.size = 213)
    (he : ∀ i, inputByte a ha i = inputByte b hb i) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · exact ha.trans hb.symm
  · intro i hi hj
    change a.data.size = 213 at ha
    exact he ⟨i, by omega⟩

/-- Parsing and serialization recover every caller-checked 213-byte input. -/
theorem serialize_getParameters (data : ByteArray) (h : data.size = 213) :
    serialize (getParameters data h) = data := by
  apply inputByte_ext _ _ (serialize_size _) h
  intro i
  exact (inputByte_serialize _ i).trans (parameterByte_getParameters data h i)

end STFSpec.Hash.Blake2b
