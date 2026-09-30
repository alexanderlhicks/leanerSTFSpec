/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.UInt.Bitwise
import Init.Data.Vector.OfFn
import Init.Data.BitVec.Lemmas
import Init.Omega

/-!
# Reference RIPEMD-160 compression

Library `EthHash`. A fixed-word dual-branch reference and separate BitVec model.
EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/ripemd160.py:52`
at the pin delegates to host `hashlib`; it has no raw compression oracle.
This implements the published algorithm unconditionally (R4); DISC-005/O12 stay open.
No digest, padding, byte parser, serialization or precompile effects are defined.
Spec guidance: `STFSpec/informal/modules/EthHash.md`.

## References

* H. Dobbertin, A. Bosselaers and B. Preneel, *RIPEMD-160: A Strengthened Version
  of RIPEMD*, FSE 1996, pp. 71–82; corrected author pseudocode:
  https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt
-/

namespace STFSpec.Hash

/-- Separate bit-vector word model, also used for message blocks. -/
abbrev Ripemd160Model (n : Nat) := Vector (BitVec 32) n

/-- Observe every stored native word without changing its position. -/
def ripemd160ToModel {n : Nat} (a : Vector UInt32 n) : Ripemd160Model n :=
  a.map UInt32.toBitVec

/-- The observer retains each numeric word and bit position. -/
theorem ripemd160ToModel_word {n : Nat} (a : Vector UInt32 n) (i : Fin n) :
    (ripemd160ToModel a)[i] = a[i].toBitVec := by
  simp [ripemd160ToModel]

/-- Equal model observations determine equal stored words. -/
theorem ripemd160ToModel_inj {n : Nat} {a b : Vector UInt32 n}
    (h : ripemd160ToModel a = ripemd160ToModel b) : a = b := by
  apply Vector.ext
  intro i hi
  apply UInt32.toBitVec_inj.mp
  have he := congrArg (fun v : Ripemd160Model n ↦ v[i]) h
  simpa [ripemd160ToModel] using he

/-- Bit zero is the least significant bit of the unsigned word. -/
theorem ripemd160ToModel_bit {n : Nat} (a : Vector UInt32 n) (i : Fin n) (z : Fin 32) :
    ((ripemd160ToModel a)[i]).getLsbD z.val = a[i].toNat.testBit z.val := by
  rw [ripemd160ToModel_word]
  rfl

/-- Rotate left modulo 32; zero avoids the machine's masked shift by 32. -/
def ripemd160Rotl (a : UInt32) (r : Nat) : UInt32 :=
  let k := r % 32
  if k = 0 then a else (a <<< UInt32.ofNat k) ||| (a >>> UInt32.ofNat (32 - k))

/-- Native rotation agrees with BitVec rotation for every amount. -/
theorem toBitVec_ripemd160Rotl (a : UInt32) (r : Nat) :
    (ripemd160Rotl a r).toBitVec = a.toBitVec.rotateLeft r := by
  have hk : r % 32 < 32 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_def]
  simp only [ripemd160Rotl]
  split
  next h => simp [h, BitVec.ushiftRight_eq_zero]
  next h =>
    have hr : 32 - r % 32 < 32 := by omega
    have hl := congrArg UInt32.toBitVec (UInt32.ofBitVec_shiftLeft a.toBitVec (r % 32) hk)
    have hs := congrArg UInt32.toBitVec
      (UInt32.ofBitVec_shiftRight a.toBitVec (32 - r % 32) hr)
    simp only [UInt32.ofBitVec_toBitVec] at hl hs
    rw [UInt32.toBitVec_or, ← hl, ← hs]

/-- Rotation's bit-position contract. -/
theorem ripemd160Rotl_bit (a : UInt32) (r : Nat) (z : Fin 32) :
    (ripemd160Rotl a r).toBitVec.getLsbD z.val =
      if z.val < r % 32 then a.toBitVec.getLsbD (32 - r % 32 + z.val)
      else a.toBitVec.getLsbD (z.val - r % 32) := by
  rw [toBitVec_ripemd160Rotl, BitVec.getLsbD_rotateLeft]
  simp only [z.isLt, decide_true, Bool.true_and]

/-- The five Boolean functions, selected by the ascending round number. -/
def ripemd160F (j : Fin 80) (x y z : UInt32) : UInt32 :=
  if j.val < 16 then x ^^^ y ^^^ z
  else if j.val < 32 then (x &&& y) ||| (~~~x &&& z)
  else if j.val < 48 then (x ||| ~~~y) ^^^ z
  else if j.val < 64 then (x &&& z) ||| (y &&& ~~~z)
  else x ^^^ (y ||| ~~~z)

/-- The five bit-level functions expressed only on BitVec words. -/
def Ripemd160Model.f (j : Fin 80) (x y z : BitVec 32) : BitVec 32 :=
  if j.val < 16 then x ^^^ y ^^^ z
  else if j.val < 32 then (x &&& y) ||| (~~~x &&& z)
  else if j.val < 48 then (x ||| ~~~y) ^^^ z
  else if j.val < 64 then (x &&& z) ||| (y &&& ~~~z)
  else x ^^^ (y ||| ~~~z)

/-- Native Boolean operations preserve the exact bit-vector function. -/
theorem toBitVec_ripemd160F (j : Fin 80) (x y z : UInt32) :
    (ripemd160F j x y z).toBitVec = Ripemd160Model.f j x.toBitVec y.toBitVec z.toBitVec := by
  unfold ripemd160F Ripemd160Model.f
  split <;> (repeat' split) <;> rfl

/-- Original RIPEMD-160 IV. -/
def ripemd160IV : Vector UInt32 5 :=
  #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- Left branch message order, five consecutive 16-round groups. -/
def ripemd160LeftOrder : Vector (Fin 16) 80 :=
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
     7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
     3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
     1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
     4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- Right branch message order; distinct from the left schedule. -/
def ripemd160RightOrder : Vector (Fin 16) 80 :=
  #v[5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
     6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
     15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
     8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
     12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- Left branch rotations. -/
def ripemd160LeftRotations : Vector Nat 80 :=
  #v[11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
     7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
     11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
     11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
     9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- Right branch rotations. -/
def ripemd160RightRotations : Vector Nat 80 :=
  #v[8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
     9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
     9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
     15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
     8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-- Added constants for the left branch groups. -/
def ripemd160LeftConstants : Vector UInt32 5 :=
  #v[0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

/-- Added constants for the right branch groups. -/
def ripemd160RightConstants : Vector UInt32 5 :=
  #v[0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0]

/-- Select the 16-round constant group. -/
def ripemd160Group (j : Fin 80) : Fin 5 := ⟨j.val / 16, by omega⟩

/-- Right-branch Boolean-function index: 79 minus the round index. -/
def ripemd160Reverse (j : Fin 80) : Fin 80 := ⟨79 - j.val, by omega⟩

/-- One simultaneous five-word branch update, storing A,B,C,D,E in that order. -/
def ripemd160Step (q : Vector UInt32 5) (j : Fin 80) (x k : UInt32)
    (s : Nat) : Vector UInt32 5 :=
  let t := ripemd160Rotl (q[0] + ripemd160F j q[1] q[2] q[3] + x + k) s + q[4]
  #v[q[4], t, q[1], ripemd160Rotl q[2] 10, q[3]]

/-- Independent bit-vector branch update, using modulo-2^32 addition. -/
def Ripemd160Model.step (q : Ripemd160Model 5) (j : Fin 80) (x k : BitVec 32)
    (s : Nat) : Ripemd160Model 5 :=
  let t := (q[0] + Ripemd160Model.f j q[1] q[2] q[3] + x + k).rotateLeft s + q[4]
  #v[q[4], t, q[1], q[2].rotateLeft 10, q[3]]

/-- A branch step commutes with the model observation. -/
theorem ripemd160ToModel_step (q : Vector UInt32 5) (j : Fin 80) (x k : UInt32)
    (s : Nat) :
    ripemd160ToModel (ripemd160Step q j x k s) =
      Ripemd160Model.step (ripemd160ToModel q) j x.toBitVec k.toBitVec s := by
  simp [ripemd160Step, Ripemd160Model.step, ripemd160ToModel,
    toBitVec_ripemd160Rotl, toBitVec_ripemd160F, UInt32.toBitVec_add]

/-- The two five-word working branches, initially equal to the chaining state. -/
structure Ripemd160Work where
  /-- Left branch A,B,C,D,E. -/
  left : Vector UInt32 5
  /-- Right branch A',B',C',D',E'. -/
  right : Vector UInt32 5
  deriving DecidableEq

/-- Bit-vector working branches. -/
structure Ripemd160Model.Work where
  /-- Left branch. -/
  left : Ripemd160Model 5
  /-- Right branch. -/
  right : Ripemd160Model 5

/-- Observe both working branches. -/
def ripemd160WorkToModel (q : Ripemd160Work) : Ripemd160Model.Work :=
  ⟨ripemd160ToModel q.left, ripemd160ToModel q.right⟩

/-- Equal working observations determine equal working states. -/
theorem ripemd160WorkToModel_inj {a b : Ripemd160Work}
    (h : ripemd160WorkToModel a = ripemd160WorkToModel b) : a = b := by
  have hl := ripemd160ToModel_inj (congrArg Ripemd160Model.Work.left h)
  have hr := ripemd160ToModel_inj (congrArg Ripemd160Model.Work.right h)
  cases a
  cases b
  simp_all [ripemd160WorkToModel]

/-- One ascending dual round, with separate branch schedules and constants. -/
def ripemd160Round (q : Ripemd160Work) (m : Vector UInt32 16) (j : Fin 80) : Ripemd160Work :=
  ⟨ripemd160Step q.left j m[ripemd160LeftOrder[j]]
      ripemd160LeftConstants[ripemd160Group j] ripemd160LeftRotations[j],
   ripemd160Step q.right (ripemd160Reverse j) m[ripemd160RightOrder[j]]
      ripemd160RightConstants[ripemd160Group j] ripemd160RightRotations[j]⟩

/-- Dual model round; tables are shared standard data, arithmetic uses BitVec. -/
def Ripemd160Model.round (q : Ripemd160Model.Work) (m : Ripemd160Model 16)
    (j : Fin 80) : Ripemd160Model.Work :=
  ⟨Ripemd160Model.step q.left j m[ripemd160LeftOrder[j]]
      ripemd160LeftConstants[ripemd160Group j].toBitVec ripemd160LeftRotations[j],
   Ripemd160Model.step q.right (ripemd160Reverse j) m[ripemd160RightOrder[j]]
      ripemd160RightConstants[ripemd160Group j].toBitVec ripemd160RightRotations[j]⟩

/-- Every dual round follows the bit-vector model. -/
theorem ripemd160WorkToModel_round (q : Ripemd160Work) (m : Vector UInt32 16) (j : Fin 80) :
    ripemd160WorkToModel (ripemd160Round q m j) =
      Ripemd160Model.round (ripemd160WorkToModel q) (ripemd160ToModel m) j := by
  simp only [ripemd160Round, Ripemd160Model.round, ripemd160WorkToModel,
    ripemd160ToModel_step]
  simp [ripemd160ToModel]

/-- First n dual rounds in ascending order, structurally bounded by 80. -/
def ripemd160Rounds (q : Ripemd160Work) (m : Vector UInt32 16) :
    (n : Nat) → n ≤ 80 → Ripemd160Work
  | 0, _ => q
  | n + 1, h => ripemd160Round (ripemd160Rounds q m n (by omega)) m ⟨n, by omega⟩

/-- First n dual model rounds in ascending order. -/
def Ripemd160Model.rounds (q : Ripemd160Model.Work) (m : Ripemd160Model 16) :
    (n : Nat) → n ≤ 80 → Ripemd160Model.Work
  | 0, _ => q
  | n + 1, h => Ripemd160Model.round (Ripemd160Model.rounds q m n (by omega)) m ⟨n, by omega⟩

/-- Induction lifts round correspondence to every bounded prefix. -/
theorem ripemd160WorkToModel_rounds (q : Ripemd160Work) (m : Vector UInt32 16)
    (n : Nat) (h : n ≤ 80) :
    ripemd160WorkToModel (ripemd160Rounds q m n h) =
      Ripemd160Model.rounds (ripemd160WorkToModel q) (ripemd160ToModel m) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ripemd160Rounds, Ripemd160Model.rounds, ripemd160WorkToModel_round, ih]

/-- Cross-branch feedforward using all five original chaining words simultaneously. -/
def ripemd160Feedforward (h : Vector UInt32 5) (q : Ripemd160Work) : Vector UInt32 5 :=
  #v[h[1] + q.left[2] + q.right[3], h[2] + q.left[3] + q.right[4],
     h[3] + q.left[4] + q.right[0], h[4] + q.left[0] + q.right[1],
     h[0] + q.left[1] + q.right[2]]

/-- Bit-vector cross-branch feedforward from the original chaining words. -/
def Ripemd160Model.feedforward (h : Ripemd160Model 5) (q : Ripemd160Model.Work) :
    Ripemd160Model 5 :=
  #v[h[1] + q.left[2] + q.right[3], h[2] + q.left[3] + q.right[4],
     h[3] + q.left[4] + q.right[0], h[4] + q.left[0] + q.right[1],
     h[0] + q.left[1] + q.right[2]]

/-- Original-state feedforward agrees with the bit-vector model. -/
theorem ripemd160ToModel_feedforward (h : Vector UInt32 5) (q : Ripemd160Work) :
    ripemd160ToModel (ripemd160Feedforward h q) =
      Ripemd160Model.feedforward (ripemd160ToModel h) (ripemd160WorkToModel q) := by
  simp [ripemd160Feedforward, Ripemd160Model.feedforward, ripemd160WorkToModel,
    ripemd160ToModel, UInt32.toBitVec_add]

/-- RIPEMD-160 reference compression on every five-word state and 16-word block. -/
def ripemd160Compress (h : Vector UInt32 5) (m : Vector UInt32 16) : Vector UInt32 5 :=
  ripemd160Feedforward h (ripemd160Rounds ⟨h, h⟩ m 80 (by decide))

/-- Complete model compression; neither digest nor padding is included. -/
def Ripemd160Model.compress (h : Ripemd160Model 5) (m : Ripemd160Model 16) :
    Ripemd160Model 5 :=
  Ripemd160Model.feedforward h (Ripemd160Model.rounds ⟨h, h⟩ m 80 (by decide))

/-- Complete correspondence on all inputs, without host or length premises. -/
theorem ripemd160ToModel_compress (h : Vector UInt32 5) (m : Vector UInt32 16) :
    ripemd160ToModel (ripemd160Compress h m) =
      Ripemd160Model.compress (ripemd160ToModel h) (ripemd160ToModel m) := by
  rw [ripemd160Compress, ripemd160ToModel_feedforward, ripemd160WorkToModel_rounds]
  rfl

end STFSpec.Hash
