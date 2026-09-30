/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Reference SHA-256 compression

Library `EthHash`. Fixed-word compression from FIPS 180-4 §§4.1.2, 4.2.2,
5.3.3 and 6.2.2, https://doi.org/10.6028/NIST.FIPS.180-4.
Words in a state are ordered a,b,c,d,e,f,g,h; input words are already big-endian
parsed. This module does not implement message padding, parsing or a digest API.
Native UInt32 arithmetic is related to the separate BitVec32 model below.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3, 7.
-/

namespace STFSpec.Hash.Sha256

/-- Observe every native word without exposing any Base representation. -/
def wordsModel {n : Nat} (v : Vector UInt32 n) : Vector (BitVec 32) n :=
  v.map UInt32.toBitVec

/-- SHA rotations use amounts strictly between zero and 32. -/
def rotr (x : UInt32) (r : Nat) : UInt32 :=
  (x >>> UInt32.ofNat r) ||| (x <<< UInt32.ofNat (32 - r))

/-- Bitwise choice: select bits of `y` or `z` using `x` (FIPS 180-4 equation (4.2)). -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
/-- Bitwise majority of three words (FIPS 180-4 equation (4.3)). -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- Round function Σ₀ using three rotations (FIPS 180-4 equation (4.4)). -/
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- Round function Σ₁ using three rotations (FIPS 180-4 equation (4.5)). -/
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- Schedule function σ₀ using rotations and a shift (FIPS 180-4 equation (4.6)). -/
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- Schedule function σ₁ using rotations and a shift (FIPS 180-4 equation (4.7)). -/
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- FIPS 180-4 §4.2.2, in ascending round order. -/
def roundConstants : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- FIPS 180-4 §5.3.3. -/
def initialState : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The first sixteen schedule words are the fixed input block. -/
def scheduleInit (block : Vector UInt32 16) : Vector UInt32 64 :=
  Vector.ofFn fun i ↦ if h : i.val < 16 then block[i.val] else 0

/-- Write W[16+j] from its four already available predecessors. -/
def scheduleStep (w : Vector UInt32 64) (j : Fin 48) : Vector UInt32 64 :=
  let t := 16 + j.val
  w.set t (smallSigma1 w[t - 2] + w[t - 7] + smallSigma0 w[t - 15] + w[t - 16])
    (by omega)

/-- Expand the first `n` schedule words after the sixteen input words, with `n ≤ 48`. -/
def scheduleIter (block : Vector UInt32 16) : (n : Nat) → n ≤ 48 → Vector UInt32 64
  | 0, _ => scheduleInit block
  | n + 1, h => scheduleStep (scheduleIter block n (by omega)) ⟨n, by omega⟩

/-- Construct all 64 message-schedule words (FIPS 180-4 §6.2.2, step 1). -/
def schedule (block : Vector UInt32 16) : Vector UInt32 64 := scheduleIter block 48 (by decide)

/-- A round has simultaneous updates, in a,b,c,d,e,f,g,h order. -/
def round (s : Vector UInt32 8) (k w : UInt32) : Vector UInt32 8 :=
  let t1 := s[7] + bigSigma1 s[4] + ch s[4] s[5] s[6] + k + w
  let t2 := bigSigma0 s[0] + maj s[0] s[1] s[2]
  #v[t1 + t2, s[0], s[1], s[2], s[3] + t1, s[4], s[5], s[6]]

/-- Run the first n rounds; recursion is bounded structurally by n ≤ 64. -/
def rounds (w : Vector UInt32 64) (s : Vector UInt32 8) :
    (n : Nat) → n ≤ 64 → Vector UInt32 8
  | 0, _ => s
  | n + 1, h => round (rounds w s n (by omega)) roundConstants[n] w[n]

/-- Add the original chaining state to the work state modulo 2^32, word by word. -/
def feedForward (original work : Vector UInt32 8) : Vector UInt32 8 :=
  Vector.ofFn fun i ↦ original[i.val] + work[i.val]

namespace Model

/-- Bitwise choice: select bits of `y` or `z` using `x` (FIPS 180-4 equation (4.2)). -/
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)
/-- Bitwise majority of three words (FIPS 180-4 equation (4.3)). -/
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- Round function Σ₀ using three rotations (FIPS 180-4 equation (4.4)). -/
def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
/-- Round function Σ₁ using three rotations (FIPS 180-4 equation (4.5)). -/
def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
/-- Schedule function σ₀ using rotations and a shift (FIPS 180-4 equation (4.6)). -/
def smallSigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
/-- Schedule function σ₁ using rotations and a shift (FIPS 180-4 equation (4.7)). -/
def smallSigma1 (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- Place the sixteen input words in a zero-filled 64-word model schedule. -/
def scheduleInit (block : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  Vector.ofFn fun i ↦ if h : i.val < 16 then block[i.val] else 0

/-- Compute model word W[16+j] from its four predecessors (FIPS 180-4 §6.2.2). -/
def scheduleStep (w : Vector (BitVec 32) 64) (j : Fin 48) : Vector (BitVec 32) 64 :=
  let t := 16 + j.val
  w.set t (smallSigma1 w[t - 2] + w[t - 7] + smallSigma0 w[t - 15] + w[t - 16])
    (by omega)

/-- Apply the first `n ≤ 48` model schedule expansions in ascending word order. -/
def scheduleIter (block : Vector (BitVec 32) 16) :
    (n : Nat) → n ≤ 48 → Vector (BitVec 32) 64
  | 0, _ => scheduleInit block
  | n + 1, h => scheduleStep (scheduleIter block n (by omega)) ⟨n, by omega⟩

/-- Complete the 64-word model schedule (FIPS 180-4 §6.2.2, step 1). -/
def schedule (block : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  scheduleIter block 48 (by decide)

/-- Update the eight model work words simultaneously (FIPS 180-4 §6.2.2, step 3). -/
def round (s : Vector (BitVec 32) 8) (k w : BitVec 32) : Vector (BitVec 32) 8 :=
  let t1 := s[7] + bigSigma1 s[4] + ch s[4] s[5] s[6] + k + w
  let t2 := bigSigma0 s[0] + maj s[0] s[1] s[2]
  #v[t1 + t2, s[0], s[1], s[2], s[3] + t1, s[4], s[5], s[6]]

/-- Run the first `n ≤ 64` model rounds with ascending schedule words and constants. -/
def rounds (w : Vector (BitVec 32) 64) (s : Vector (BitVec 32) 8) :
    (n : Nat) → n ≤ 64 → Vector (BitVec 32) 8
  | 0, _ => s
  | n + 1, h => round (rounds w s n (by omega)) (wordsModel roundConstants)[n] w[n]

/-- Add the original chaining words to the final model work words modulo 2^32. -/
def feedForward (original work : Vector (BitVec 32) 8) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun i ↦ original[i.val] + work[i.val]

/-- Model one parsed block: expand its schedule, run 64 rounds and add the original state. -/
def compress (s : Vector (BitVec 32) 8) (block : Vector (BitVec 32) 16) :
    Vector (BitVec 32) 8 := feedForward s (rounds (schedule block) s 64 (by decide))

end Model

end STFSpec.Hash.Sha256

namespace STFSpec.Hash

/-- FIPS SHA-256 compression on exactly one parsed sixteen-word block. -/
def sha256Compress (s : Vector UInt32 8) (block : Vector UInt32 16) : Vector UInt32 8 :=
  Sha256.feedForward s (Sha256.rounds (Sha256.schedule block) s 64 (by decide))

end STFSpec.Hash

namespace STFSpec.Hash.Sha256

/-- Native masked shifts implement the standard rotation for the SHA amounts. -/
theorem toBitVec_rotr (x : UInt32) (r : Nat) (hr0 : 0 < r) (hr32 : r < 32) :
    (rotr x r).toBitVec = x.toBitVec.rotateRight r := by
  have h : UInt32.ofBitVec (x.toBitVec.rotateRight r) = rotr x r := by
    rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr32]
    rw [BitVec.rotateRightAux, UInt32.ofBitVec_or,
      UInt32.ofBitVec_shiftRight _ _ hr32,
      UInt32.ofBitVec_shiftLeft _ _ (by omega)]
    simp only [UInt32.ofBitVec_toBitVec, rotr]
  exact (congrArg UInt32.toBitVec h).symm

/-- Native choice commutes with the BitVec model observation. -/
theorem toBitVec_ch (x y z : UInt32) :
    (ch x y z).toBitVec = Model.ch x.toBitVec y.toBitVec z.toBitVec := by
  simp only [ch, Model.ch, UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_not]

/-- Native majority commutes with the BitVec model observation. -/
theorem toBitVec_maj (x y z : UInt32) :
    (maj x y z).toBitVec = Model.maj x.toBitVec y.toBitVec z.toBitVec := by
  simp only [maj, Model.maj, UInt32.toBitVec_xor, UInt32.toBitVec_and]

/-- Native round function Σ₀ agrees with its BitVec model. -/
theorem toBitVec_bigSigma0 (x : UInt32) :
    (bigSigma0 x).toBitVec = Model.bigSigma0 x.toBitVec := by
  simp only [bigSigma0, Model.bigSigma0, UInt32.toBitVec_xor,
    toBitVec_rotr x 2 (by decide) (by decide),
    toBitVec_rotr x 13 (by decide) (by decide),
    toBitVec_rotr x 22 (by decide) (by decide)]

/-- Native round function Σ₁ agrees with its BitVec model. -/
theorem toBitVec_bigSigma1 (x : UInt32) :
    (bigSigma1 x).toBitVec = Model.bigSigma1 x.toBitVec := by
  simp only [bigSigma1, Model.bigSigma1, UInt32.toBitVec_xor,
    toBitVec_rotr x 6 (by decide) (by decide),
    toBitVec_rotr x 11 (by decide) (by decide),
    toBitVec_rotr x 25 (by decide) (by decide)]

/-- Native schedule function σ₀ agrees with its BitVec model. -/
theorem toBitVec_smallSigma0 (x : UInt32) :
    (smallSigma0 x).toBitVec = Model.smallSigma0 x.toBitVec := by
  have h : (x >>> (3 : UInt32)).toBitVec = x.toBitVec >>> (3 : Nat) := by
    have e := UInt32.ofBitVec_shiftRight x.toBitVec 3 (by decide)
    exact (congrArg UInt32.toBitVec e).symm
  simp only [smallSigma0, Model.smallSigma0, UInt32.toBitVec_xor, h,
    toBitVec_rotr x 7 (by decide) (by decide),
    toBitVec_rotr x 18 (by decide) (by decide)]

/-- Native schedule function σ₁ agrees with its BitVec model. -/
theorem toBitVec_smallSigma1 (x : UInt32) :
    (smallSigma1 x).toBitVec = Model.smallSigma1 x.toBitVec := by
  have h : (x >>> (10 : UInt32)).toBitVec = x.toBitVec >>> (10 : Nat) := by
    have e := UInt32.ofBitVec_shiftRight x.toBitVec 10 (by decide)
    exact (congrArg UInt32.toBitVec e).symm
  simp only [smallSigma1, Model.smallSigma1, UInt32.toBitVec_xor, h,
    toBitVec_rotr x 17 (by decide) (by decide),
    toBitVec_rotr x 19 (by decide) (by decide)]

/-- Observe a native vector at an index by observing its word at that index. -/
theorem wordsModel_get {n : Nat} (v : Vector UInt32 n) (i : Nat) (hi : i < n) :
    (wordsModel v)[i] = v[i].toBitVec := by simp only [wordsModel, Vector.getElem_map]

/-- Equal model observations determine equal native word vectors. -/
theorem wordsModel_injective {n : Nat} : Function.Injective (@wordsModel n) := by
  intro x y h
  apply Vector.ext
  intro i hi
  apply UInt32.eq_of_toBitVec_eq
  simpa only [wordsModel_get] using congrArg (fun v ↦ v[i]) h

/-- Schedule initialization commutes with the model observation. -/
theorem wordsModel_scheduleInit (block : Vector UInt32 16) :
    wordsModel (scheduleInit block) = Model.scheduleInit (wordsModel block) := by
  apply Vector.ext
  intro i hi
  simp only [wordsModel_get, scheduleInit, Model.scheduleInit, Vector.getElem_ofFn]
  split
  · rfl
  · rfl

/-- One schedule expansion commutes with the model observation. -/
theorem wordsModel_scheduleStep (w : Vector UInt32 64) (j : Fin 48) :
    wordsModel (scheduleStep w j) = Model.scheduleStep (wordsModel w) j := by
  simp only [scheduleStep, Model.scheduleStep, wordsModel, Vector.map_set,
    UInt32.toBitVec_add, toBitVec_smallSigma0, toBitVec_smallSigma1, Vector.getElem_map]

/-- Every bounded schedule-expansion prefix agrees with its model. -/
theorem wordsModel_scheduleIter (block : Vector UInt32 16) (n : Nat) (hn : n ≤ 48) :
    wordsModel (scheduleIter block n hn) = Model.scheduleIter (wordsModel block) n hn := by
  induction n with
  | zero => exact wordsModel_scheduleInit block
  | succ n ih =>
    simp only [scheduleIter, Model.scheduleIter, wordsModel_scheduleStep, ih]

/-- The complete native message schedule agrees with its model. -/
theorem wordsModel_schedule (block : Vector UInt32 16) :
    wordsModel (schedule block) = Model.schedule (wordsModel block) :=
  wordsModel_scheduleIter block 48 (by decide)

/-- One simultaneous native round agrees with its model. -/
theorem wordsModel_round (s : Vector UInt32 8) (k w : UInt32) :
    wordsModel (round s k w) = Model.round (wordsModel s) k.toBitVec w.toBitVec := by
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [round, Model.round, wordsModel_get, UInt32.toBitVec_add,
      toBitVec_bigSigma0, toBitVec_bigSigma1, toBitVec_ch, toBitVec_maj]

/-- Every bounded native round prefix agrees with its model. -/
theorem wordsModel_rounds (w : Vector UInt32 64) (s : Vector UInt32 8)
    (n : Nat) (hn : n ≤ 64) :
    wordsModel (rounds w s n hn) = Model.rounds (wordsModel w) (wordsModel s) n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rounds, Model.rounds, wordsModel_round, ih, wordsModel_get]

/-- Wordwise native feed-forward agrees with model addition. -/
theorem wordsModel_feedForward (original work : Vector UInt32 8) :
    wordsModel (feedForward original work) =
      Model.feedForward (wordsModel original) (wordsModel work) := by
  apply Vector.ext
  intro i hi
  simp only [feedForward, Model.feedForward, wordsModel_get, Vector.getElem_ofFn,
    UInt32.toBitVec_add]

/-- Running zero rounds returns the original state. -/
theorem rounds_zero (w : Vector UInt32 64) (s : Vector UInt32 8) :
    rounds w s 0 (by decide) = s := rfl

/-- A round prefix extends by applying the next constant and schedule word. -/
theorem rounds_succ (w : Vector UInt32 64) (s : Vector UInt32 8)
    (n : Nat) (hn : n < 64) :
    rounds w s (n + 1) (by omega) = round (rounds w s n (by omega)) roundConstants[n] w[n] := rfl

/-- Each feed-forward word is the modular sum of original and work words. -/
theorem feedForward_get (original work : Vector UInt32 8) (i : Nat) (hi : i < 8) :
    (feedForward original work)[i] = original[i] + work[i] := by
  simp only [feedForward, Vector.getElem_ofFn]

end STFSpec.Hash.Sha256

namespace STFSpec.Hash

/-- Compression correspondence has no message-length or host premises. -/
theorem sha256Compress_model (s : Vector UInt32 8) (block : Vector UInt32 16) :
    Sha256.wordsModel (sha256Compress s block) =
      Sha256.Model.compress (Sha256.wordsModel s) (Sha256.wordsModel block) := by
  simp only [sha256Compress, Sha256.Model.compress, Sha256.wordsModel_feedForward,
    Sha256.wordsModel_rounds, Sha256.wordsModel_schedule]

/-- Expose compression as schedule expansion, 64 rounds and original-state feed-forward. -/
theorem sha256Compress_eq (s : Vector UInt32 8) (block : Vector UInt32 16) :
    sha256Compress s block =
      Sha256.feedForward s (Sha256.rounds (Sha256.schedule block) s 64 (by decide)) := rfl

end STFSpec.Hash

namespace STFSpec.Hash.Sha256

/-- Schedule initialization preserves each of the sixteen input words. -/
theorem scheduleInit_get (block : Vector UInt32 16) (i : Nat) (hi : i < 16) :
    (scheduleInit block)[i] = block[i] := by
  simp only [scheduleInit, Vector.getElem_ofFn, dite_eq_left hi]

/-- The word written by a schedule step satisfies the four-predecessor recurrence. -/
theorem scheduleStep_get (w : Vector UInt32 64) (j : Fin 48) :
    (scheduleStep w j)[16 + j.val] =
      smallSigma1 w[16 + j.val - 2] + w[16 + j.val - 7] +
        smallSigma0 w[16 + j.val - 15] + w[16 + j.val - 16] := by
  simp only [scheduleStep, Vector.getElem_set_self]

/-- A schedule step preserves every word except the one it writes. -/
theorem scheduleStep_get_of_ne (w : Vector UInt32 64) (j : Fin 48)
    (i : Nat) (hi : i < 64) (hne : i ≠ 16 + j.val) :
    (scheduleStep w j)[i] = w[i] := by
  simp only [scheduleStep, Vector.getElem_set, ite_eq_right (Ne.symm hne)]

/-- Extending the schedule never alters words already computed. -/
theorem scheduleIter_stable (block : Vector UInt32 16) (m n : Nat)
    (hmn : m ≤ n) (hn : n ≤ 48) (i : Nat) (hi : i < 16 + m) :
    (scheduleIter block n hn)[i] = (scheduleIter block m (by omega))[i] := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · rw [scheduleIter, scheduleStep_get_of_ne _ _ _ (by omega) (by change i ≠ 16 + n; omega)]
      exact ih hmn' (by omega)
    · have : m = n + 1 := by omega
      subst m
      rfl

/-- The completed schedule retains every original block word. -/
theorem schedule_get_input (block : Vector UInt32 16) (i : Nat) (hi : i < 16) :
    (schedule block)[i] = block[i] := by
  rw [schedule, scheduleIter_stable block 0 48 (by omega) (by omega) i (by omega)]
  exact scheduleInit_get block i hi

/-- The completed schedule satisfies the standard four-predecessor recurrence. -/
theorem schedule_get_expanded (block : Vector UInt32 16) (j : Fin 48) :
    (schedule block)[16 + j.val] =
      smallSigma1 (schedule block)[16 + j.val - 2] + (schedule block)[16 + j.val - 7] +
        smallSigma0 (schedule block)[16 + j.val - 15] + (schedule block)[16 + j.val - 16] := by
  rw [schedule, scheduleIter_stable block (j.val + 1) 48 (by omega) (by omega)
    (16 + j.val) (by omega), scheduleIter, scheduleStep_get]
  rw [scheduleIter_stable block j.val 48 (by omega) (by omega) (16 + j.val - 2) (by omega),
      scheduleIter_stable block j.val 48 (by omega) (by omega) (16 + j.val - 7) (by omega),
      scheduleIter_stable block j.val 48 (by omega) (by omega) (16 + j.val - 15) (by omega),
      scheduleIter_stable block j.val 48 (by omega) (by omega) (16 + j.val - 16) (by omega)]

end STFSpec.Hash.Sha256
