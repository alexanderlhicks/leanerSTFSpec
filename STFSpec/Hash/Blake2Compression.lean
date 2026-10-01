/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Blake2Parameters

/-!
# BLAKE2b F compression

Library `EthHash`. Pinned EELS `src/ethereum/crypto/blake2.py:91–125,152–266`;
RFC 7693 §§2.6, 3.1–3.2, https://www.rfc-editor.org/rfc/rfc7693.
The native path uses UInt64 words; the separate model uses standard BitVec operations.
Every G statement reads the vector resulting from the preceding statement, including
when indices alias. Compression observes sixteen words: Python's slice assignment
creates an unused seventeenth word, outside all mixing and output reads.
Spec guidance: `STFSpec/informal/modules/EthHash.md` R5, §§3, 7.
-/

namespace STFSpec.Hash.Blake2b

/-- Wordwise observation into the fixed-width model. -/
def wordsModel {n : Nat} (v : Vector UInt64 n) : Vector (BitVec 64) n :=
  v.map UInt64.toBitVec

/-- Total right rotation; counts reduce modulo 64, with zero returning the input. -/
def rotr (x : UInt64) (r : Nat) : UInt64 :=
  let k := r % 64
  if k = 0 then x else
    (x >>> UInt64.ofNat k) ||| (x <<< UInt64.ofNat (64 - k))

/-- Pinned EELS `crypto/blake2.py:104–113`; RFC 7693 §2.6, eight IV words. -/
def IV : Vector UInt64 8 := #v[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- Pinned EELS `crypto/blake2.py:91–102`; RFC 7693 §2.7, ascending sigma rows. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
  #v[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
  #v[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
  #v[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
  #v[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
  #v[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
  #v[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
  #v[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
  #v[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
  #v[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

/-- Pinned EELS `crypto/blake2.py:115–125`: four columns then four diagonals. -/
def MIX_TABLE : Vector (Fin 16 × Fin 16 × Fin 16 × Fin 16) 8 := #v[
  (0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
  (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

/-- Pinned EELS `crypto/blake2.py:152–192`: eight sequential writes, arbitrary aliases. -/
def G (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 :=
  let v := v.set a.val (v[a.val] + v[b.val] + x) a.isLt
  let v := v.set d.val (rotr (v[d.val] ^^^ v[a.val]) 32) d.isLt
  let v := v.set c.val (v[c.val] + v[d.val]) c.isLt
  let v := v.set b.val (rotr (v[b.val] ^^^ v[c.val]) 24) b.isLt
  let v := v.set a.val (v[a.val] + v[b.val] + y) a.isLt
  let v := v.set d.val (rotr (v[d.val] ^^^ v[a.val]) 16) d.isLt
  let v := v.set c.val (v[c.val] + v[d.val]) c.isLt
  v.set b.val (rotr (v[b.val] ^^^ v[c.val]) 63) b.isLt

/-- Pinned EELS `crypto/blake2.py:215–224`, restricted to its sixteen observed words. -/
def initState (h : Vector UInt64 8) (t0 t1 : UInt64) (f : Bool) : Vector UInt64 16 :=
  let v := Vector.ofFn fun i : Fin 16 ↦
    if hi : i.val < 8 then h[i.val] else IV[i.val - 8]
  let v := v.set 12 (t0 ^^^ IV[4])
  let v := v.set 13 (t1 ^^^ IV[5])
  v.set 14 (if f then IV[6] ^^^ 0xffffffffffffffff else IV[6])

/-- One ascending round, indexed modulo ten; pinned EELS `crypto/blake2.py:227–244`. -/
def round (m v : Vector UInt64 16) (r : Nat) : Vector UInt64 16 :=
  let s := sigma[r % 10]
  let v := G v 0 4 8 12 m[s[0].val] m[s[1].val]
  let v := G v 1 5 9 13 m[s[2].val] m[s[3].val]
  let v := G v 2 6 10 14 m[s[4].val] m[s[5].val]
  let v := G v 3 7 11 15 m[s[6].val] m[s[7].val]
  let v := G v 0 5 10 15 m[s[8].val] m[s[9].val]
  let v := G v 1 6 11 12 m[s[10].val] m[s[11].val]
  let v := G v 2 7 8 13 m[s[12].val] m[s[13].val]
  G v 3 4 9 14 m[s[14].val] m[s[15].val]

/-- Structural tail iteration; `start` is the first ascending sigma index. -/
def rounds (m : Vector UInt64 16) :
    (count start : Nat) → Vector UInt64 16 → Vector UInt64 16
  | 0, _, v => v
  | n + 1, start, v => rounds m n (start + 1) (round m v start)

/-- Original-state XOR feed-forward; pinned EELS `crypto/blake2.py:246`. -/
def feedForward (h : Vector UInt64 8) (v : Vector UInt64 16) : Vector UInt64 8 :=
  Vector.ofFn fun i ↦ h[i.val] ^^^ v[i.val] ^^^ v[i.val + 8]

/-- Native low-to-high byte observation of a 64-bit word. -/
def outputByte (x : UInt64) (j : Fin 8) : UInt8 :=
  (x >>> UInt64.ofNat (8 * j.val)).toUInt8

/-- Fixed-width little-endian serialization; pinned EELS `crypto/blake2.py:247`. -/
def serializeWords (h : Vector UInt64 8) : ByteArray :=
  (Base.Bytes.generate 64 fun i ↦
    outputByte h[(i / 8) % 8] ⟨i % 8, by omega⟩).toByteArray

/-- Pinned EELS `crypto/blake2.py:194–247`, all UInt32 counts and Boolean flags.
The precompile must charge gas before evaluation; this function has no gas effects. -/
def compress (count : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t0 t1 : UInt64) (f : Bool) : ByteArray :=
  serializeWords (feedForward h (rounds m count.toNat 0 (initState h t0 t1 f)))

namespace Model

/-- RFC G on standard bitwords, retaining sequential read-after-write semantics. -/
def G (v : Vector (BitVec 64) 16) (a b c d : Fin 16) (x y : BitVec 64) :
    Vector (BitVec 64) 16 :=
  let v := v.set a.val (v[a.val] + v[b.val] + x) a.isLt
  let v := v.set d.val ((v[d.val] ^^^ v[a.val]).rotateRight 32) d.isLt
  let v := v.set c.val (v[c.val] + v[d.val]) c.isLt
  let v := v.set b.val ((v[b.val] ^^^ v[c.val]).rotateRight 24) b.isLt
  let v := v.set a.val (v[a.val] + v[b.val] + y) a.isLt
  let v := v.set d.val ((v[d.val] ^^^ v[a.val]).rotateRight 16) d.isLt
  let v := v.set c.val (v[c.val] + v[d.val]) c.isLt
  v.set b.val ((v[b.val] ^^^ v[c.val]).rotateRight 63) b.isLt

/-- The RFC sixteen-coordinate initial state, with the counter and final-bit XORs. -/
def initState (h : Vector (BitVec 64) 8) (t0 t1 : BitVec 64) (f : Bool) :
    Vector (BitVec 64) 16 :=
  Vector.ofFn fun i ↦
    if hi : i.val < 8 then h[i.val] else
    if i.val = 12 then t0 ^^^ (wordsModel IV)[4] else
    if i.val = 13 then t1 ^^^ (wordsModel IV)[5] else
    if i.val = 14 then
      if f then (wordsModel IV)[6] ^^^ 0xffffffffffffffff#64 else (wordsModel IV)[6]
    else (wordsModel IV)[i.val - 8]

/-- Four model columns and four model diagonals using ascending modulo-ten sigma. -/
def round (m v : Vector (BitVec 64) 16) (r : Nat) : Vector (BitVec 64) 16 :=
  let s := sigma[r % 10]
  let v := G v 0 4 8 12 m[s[0].val] m[s[1].val]
  let v := G v 1 5 9 13 m[s[2].val] m[s[3].val]
  let v := G v 2 6 10 14 m[s[4].val] m[s[5].val]
  let v := G v 3 7 11 15 m[s[6].val] m[s[7].val]
  let v := G v 0 5 10 15 m[s[8].val] m[s[9].val]
  let v := G v 1 6 11 12 m[s[10].val] m[s[11].val]
  let v := G v 2 7 8 13 m[s[12].val] m[s[13].val]
  G v 3 4 9 14 m[s[14].val] m[s[15].val]

/-- Standard finite round sequence; no upper round limit is added. -/
def rounds (m : Vector (BitVec 64) 16) :
    (count start : Nat) → Vector (BitVec 64) 16 → Vector (BitVec 64) 16
  | 0, _, v => v
  | n + 1, start, v => rounds m n (start + 1) (round m v start)

/-- XOR each original word with both final-work-state halves. -/
def feedForward (h : Vector (BitVec 64) 8) (v : Vector (BitVec 64) 16) :
    Vector (BitVec 64) 8 := Vector.ofFn fun i ↦ h[i.val] ^^^ v[i.val] ^^^ v[i.val + 8]

/-- Standard bit extraction into exactly 64 little-endian bytes. -/
def serializeWords (h : Vector (BitVec 64) 8) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 64 ↦ wordByte (n := 8) h[i.val / 8] ⟨i.val % 8, by omega⟩⟩

/-- Separate fixed-bitword model of the complete F compression observation. -/
def compress (count : UInt32) (h : Vector (BitVec 64) 8) (m : Vector (BitVec 64) 16)
    (t0 t1 : BitVec 64) (f : Bool) : ByteArray :=
  serializeWords (feedForward h (rounds m count.toNat 0 (initState h t0 t1 f)))

end Model

/-- Native indexed observations commute with word conversion. -/
theorem wordsModel_get {n : Nat} (v : Vector UInt64 n) (i : Nat) (hi : i < n) :
    (wordsModel v)[i] = v[i].toBitVec := by simp only [wordsModel, Vector.getElem_map]

/-- A vector write commutes with observation independently of index aliasing. -/
theorem wordsModel_set {n : Nat} (v : Vector UInt64 n) (i : Nat) (hi : i < n)
    (x : UInt64) :
    wordsModel (v.set i x hi) = (wordsModel v).set i x.toBitVec hi := by
  simp only [wordsModel, Vector.map_set]

/-- Equal bitword vectors determine equal native vectors. -/
theorem wordsModel_injective {n : Nat} : Function.Injective (@wordsModel n) := by
  intro x y h
  apply Vector.ext
  intro i hi
  apply UInt64.toBitVec_inj.mp
  simpa only [wordsModel_get] using congrArg (fun v ↦ v[i]) h

/-- Native additions are modular BitVec additions, on the entire word domain. -/
theorem toBitVec_add (x y : UInt64) : (x + y).toBitVec = x.toBitVec + y.toBitVec :=
  UInt64.toBitVec_add

/-- Native shifts implement standard right rotation for strictly positive small counts. -/
theorem toBitVec_rotr (x : UInt64) (r : Nat) (hr0 : 0 < r) (hr64 : r < 64) :
    (rotr x r).toBitVec = x.toBitVec.rotateRight r := by
  have h : UInt64.ofBitVec (x.toBitVec.rotateRight r) = rotr x r := by
    rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr64]
    rw [BitVec.rotateRightAux, UInt64.ofBitVec_or,
      UInt64.ofBitVec_shiftRight _ _ hr64,
      UInt64.ofBitVec_shiftLeft _ _ (by omega)]
    simp only [UInt64.ofBitVec_toBitVec, rotr, Nat.mod_eq_of_lt hr64,
      show ¬r = 0 by omega, ↓reduceIte]
  exact (congrArg UInt64.toBitVec h).symm

/-- Disjoint shifted bit ranges make the source's XOR equal the standard rotation. -/
theorem rotateRight_eq_xor (x : BitVec 64) (r : Nat) (hr0 : 0 < r) (hr64 : r < 64) :
    x.rotateRight r = (x >>> r) ^^^ (x <<< (64 - r)) := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr64, BitVec.rotateRightAux]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_ushiftRight,
    BitVec.getElem_shiftLeft]
  by_cases h : i < 64 - r
  · simp [h]
  · have he : x.getLsbD (r + i) = false := BitVec.getLsbD_of_ge x (r + i) (by omega)
    simp [h, he]

/-- Total counts have the same modulo-64 semantics as standard BitVec rotations. -/
theorem toBitVec_rotr_total (x : UInt64) (r : Nat) :
    (rotr x r).toBitVec = x.toBitVec.rotateRight r := by
  by_cases h : r % 64 = 0
  · simp only [rotr, h, ↓reduceIte]
    rw [← BitVec.rotateRight_mod_eq_rotateRight, h]
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
  · have hp : 0 < r % 64 := by omega
    have hl : r % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [← BitVec.rotateRight_mod_eq_rotateRight]
    rw [← toBitVec_rotr x (r % 64) hp hl]
    simp only [rotr, Nat.mod_mod]

/-- Zero or a multiple of 64 rotates to the original word. -/
theorem rotr_of_mod_eq_zero (x : UInt64) (r : Nat) (h : r % 64 = 0) : rotr x r = x := by
  simp only [rotr, h, ↓reduceIte]

/-- The complete sigma row for round index 0 modulo ten. -/
theorem sigma_row_0 : sigma[0] = #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := rfl

/-- The complete sigma row for round index 1 modulo ten. -/
theorem sigma_row_1 : sigma[1] = #v[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3] := rfl

/-- The complete sigma row for round index 2 modulo ten. -/
theorem sigma_row_2 : sigma[2] = #v[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4] := rfl

/-- The complete sigma row for round index 3 modulo ten. -/
theorem sigma_row_3 : sigma[3] = #v[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8] := rfl

/-- The complete sigma row for round index 4 modulo ten. -/
theorem sigma_row_4 : sigma[4] = #v[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13] := rfl

/-- The complete sigma row for round index 5 modulo ten. -/
theorem sigma_row_5 : sigma[5] = #v[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9] := rfl

/-- The complete sigma row for round index 6 modulo ten. -/
theorem sigma_row_6 : sigma[6] = #v[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11] := rfl

/-- The complete sigma row for round index 7 modulo ten. -/
theorem sigma_row_7 : sigma[7] = #v[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10] := rfl

/-- The complete sigma row for round index 8 modulo ten. -/
theorem sigma_row_8 : sigma[8] = #v[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5] := rfl

/-- The complete sigma row for round index 9 modulo ten. -/
theorem sigma_row_9 : sigma[9] = #v[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0] := rfl

/-- G simulation permits all indices to coincide; no disjointness premise is needed. -/
theorem wordsModel_G (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) :
    wordsModel (G v a b c d x y) = Model.G (wordsModel v) a b c d x.toBitVec y.toBitVec := by
  simp only [G, Model.G, wordsModel_set,
    UInt64.toBitVec_add, UInt64.toBitVec_xor,
    toBitVec_rotr _ 32 (by decide) (by decide),
    toBitVec_rotr _ 24 (by decide) (by decide),
    toBitVec_rotr _ 16 (by decide) (by decide),
    toBitVec_rotr _ 63 (by decide) (by decide), ← wordsModel_get]

/-- Every untouched G coordinate is preserved, also when the written indices alias. -/
theorem G_get_of_ne (v : Vector UInt64 16) (a b c d i : Fin 16) (x y : UInt64)
    (ha : a.val ≠ i.val) (hb : b.val ≠ i.val) (hc : c.val ≠ i.val) (hd : d.val ≠ i.val) :
    (G v a b c d x y)[i.val] = v[i.val] := by
  simp only [G, Vector.getElem_set, ha, hb, hc, hd, ↓reduceIte]

/-- Initialization observes exactly the RFC sixteen coordinates. -/
theorem wordsModel_initState (h : Vector UInt64 8) (t0 t1 : UInt64) (f : Bool) :
    wordsModel (initState h t0 t1 f) =
      Model.initState (wordsModel h) t0.toBitVec t1.toBitVec f := by
  apply Vector.ext
  intro i hi
  simp only [wordsModel_get, initState, Model.initState, Vector.getElem_set,
    Vector.getElem_ofFn]
  by_cases h8 : i < 8
  · simp [h8, show ¬14 = i by omega, show ¬13 = i by omega, show ¬12 = i by omega]
  · by_cases h12 : i = 12
    · subst i
      simp
    · by_cases h13 : i = 13
      · subst i
        simp
      · by_cases h14 : i = 14
        · subst i
          cases f <;> simp
        · simp [h8, h12, h13, h14, Ne.symm h12, Ne.symm h13, Ne.symm h14]

/-- Coordinate initialization equation for clients, independent of native write internals. -/
theorem initState_get (h : Vector UInt64 8) (t0 t1 : UInt64) (f : Bool) (i : Fin 16) :
    (initState h t0 t1 f)[i.val].toBitVec =
      (Model.initState (wordsModel h) t0.toBitVec t1.toBitVec f)[i.val] := by
  rw [← wordsModel_get, wordsModel_initState]

/-- Each ascending native round commutes with the bitword model. -/
theorem wordsModel_round (m v : Vector UInt64 16) (r : Nat) :
    wordsModel (round m v r) = Model.round (wordsModel m) (wordsModel v) r := by
  simp only [round, Model.round, wordsModel_G, wordsModel_get]

/-- Sigma repeats after ten rounds; the caller's ascending round index is retained. -/
theorem round_add_ten (m v : Vector UInt64 16) (r : Nat) :
    round m v (r + 10) = round m v r := by
  simp only [round, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- Every finite prefix, at any starting index, commutes with the model. -/
theorem wordsModel_rounds (m v : Vector UInt64 16) (n start : Nat) :
    wordsModel (rounds m n start v) =
      Model.rounds (wordsModel m) n start (wordsModel v) := by
  induction n generalizing start v with
  | zero => rfl
  | succ n ih => simp only [rounds, Model.rounds, ih, wordsModel_round]

/-- Splitting a prefix advances the next segment's ascending sigma index. -/
theorem rounds_add (m v : Vector UInt64 16) (n k start : Nat) :
    rounds m (n + k) start v = rounds m k (start + n) (rounds m n start v) := by
  induction n generalizing start v with
  | zero => simp only [Nat.zero_add, Nat.add_zero, rounds]
  | succ n ih =>
    rw [Nat.succ_add, rounds, ih, rounds]
    simp only [Nat.add_assoc, Nat.add_comm 1 n]

/-- Appending one round uses precisely the next ascending index. -/
theorem rounds_succ (m v : Vector UInt64 16) (n start : Nat) :
    rounds m (n + 1) start v = round m (rounds m n start v) (start + n) := by
  rw [rounds_add]
  rfl

/-- Zero rounds preserve the work vector. -/
theorem rounds_zero (m v : Vector UInt64 16) (start : Nat) : rounds m 0 start v = v := rfl

/-- Feed-forward commutes with standard bitwise XOR. -/
theorem wordsModel_feedForward (h : Vector UInt64 8) (v : Vector UInt64 16) :
    wordsModel (feedForward h v) = Model.feedForward (wordsModel h) (wordsModel v) := by
  apply Vector.ext
  intro i hi
  simp only [wordsModel_get, feedForward, Model.feedForward, Vector.getElem_ofFn,
    UInt64.toBitVec_xor]

/-- Each feed-forward word retains its original and both final work coordinates. -/
theorem feedForward_get (h : Vector UInt64 8) (v : Vector UInt64 16)
    (i : Nat) (hi : i < 8) : (feedForward h v)[i] = h[i] ^^^ v[i] ^^^ v[i + 8] := by
  simp only [feedForward, Vector.getElem_ofFn]

/-- The native serializer byte is the model's low-to-high eight-bit extraction. -/
theorem outputByte_eq_wordByte (x : UInt64) (j : Fin 8) :
    outputByte x j = wordByte (n := 8) x.toBitVec j := by
  apply UInt8.toBitVec_inj.mp
  have he := UInt64.ofBitVec_shiftRight x.toBitVec (8 * j.val) (by omega)
  have hs := (congrArg UInt64.toBitVec he).symm
  simp only [UInt64.ofBitVec_toBitVec] at hs
  simp only [outputByte, UInt64.toBitVec_toUInt8, hs, wordByte,
    UInt8.toBitVec_ofBitVec, BitVec.extractLsb']
  rfl

/-- Native serialization equals fixed-width standard model serialization. -/
theorem serializeWords_model (h : Vector UInt64 8) :
    serializeWords h = Model.serializeWords (wordsModel h) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [serializeWords, Base.Bytes.toList_toByteArray, Base.Bytes.toList_generate,
    Model.serializeWords, Array.toList_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi64 : i < 64 := by simpa using hi
    have hdiv : i / 8 < 8 := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      Nat.mod_eq_of_lt hdiv, wordsModel_get, outputByte_eq_wordByte]

/-- Serialization retains all eight words, including their leading zero bytes. -/
theorem serializeWords_size (h : Vector UInt64 8) : (serializeWords h).size = 64 := by
  simp only [serializeWords, Base.Bytes.size_toByteArray, Base.Bytes.size_generate]

/-- Compression equals its ordinary separate model on the full UInt32 domain. -/
theorem compress_model (count : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t0 t1 : UInt64) (f : Bool) :
    compress count h m t0 t1 f =
      Model.compress count (wordsModel h) (wordsModel m) t0.toBitVec t1.toBitVec f := by
  simp only [compress, Model.compress, serializeWords_model, wordsModel_feedForward,
    wordsModel_rounds, wordsModel_initState]

/-- Public decomposition without unfolding the native word/storage implementation. -/
theorem compress_eq (count : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t0 t1 : UInt64) (f : Bool) :
    compress count h m t0 t1 f =
      serializeWords (feedForward h (rounds m count.toNat 0 (initState h t0 t1 f))) := rfl

/-- The full compression observation is always exactly 64 bytes. -/
theorem compress_size (count : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t0 t1 : UInt64) (f : Bool) : (compress count h m t0 t1 f).size = 64 :=
  serializeWords_size _

end STFSpec.Hash.Blake2b
