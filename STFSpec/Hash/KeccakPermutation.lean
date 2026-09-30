/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.UInt.Bitwise
import Init.Data.Vector.OfFn
import Init.Data.BitVec.Lemmas
import Init.Omega

/-!
# Reference Keccak-f[1600] permutation

Library `EthHash`. Array-backed lanes implement the five steps of FIPS 202 §3.2
and its 24-round permutation (§3.3). The coordinate model uses bit-vector lanes;
its step laws are the public correspondence contract. No sponge is defined here.
Spec guidance: `STFSpec/informal/modules/EthHash.md`.

## References

* NIST, *FIPS PUB 202*, 2015, §§3.1–3.3, Table 2 and Algorithm 7.
  https://doi.org/10.6028/NIST.FIPS.202
-/

namespace STFSpec.Hash

/-- Reference state with private storage; use coordinate construction and observation. -/
structure KeccakState where
  private ofVectorRaw ::
  private lanes : Vector UInt64 25
  deriving DecidableEq

/-- Standard coordinate state, with bit zero the least significant lane bit. -/
abbrev KeccakModel := Fin 5 × Fin 5 → BitVec 64

/-- Coordinate to lane index; x varies first. -/
def keccakLaneIndex (x y : Fin 5) : Fin 25 := ⟨x.val + 5 * y.val, by omega⟩

/-- Read a lane through the stable coordinate interface. -/
def keccakLane (a : KeccakState) (x y : Fin 5) : UInt64 := a.lanes[keccakLaneIndex x y]

/-- Bit-vector observation of every coordinate lane. -/
def keccakToModel (a : KeccakState) : KeccakModel :=
  fun p ↦ (keccakLane a p.1 p.2).toBitVec

/-- Construct reference storage from coordinate lanes without a list intermediary. -/
def keccakOfLanes (f : Fin 5 → Fin 5 → UInt64) : KeccakState :=
  KeccakState.ofVectorRaw <|
    Vector.ofFn fun i ↦ f ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 5, by omega⟩

/-- Construction retains exactly the lane at each coordinate. -/
theorem keccakLane_ofLanes (f : Fin 5 → Fin 5 → UInt64) (x y : Fin 5) :
    keccakLane (keccakOfLanes f) x y = f x y := by
  change (Vector.ofFn _)[x.val + 5 * y.val] = f x y
  rw [Vector.getElem_ofFn]
  have hx : (x.val + 5 * y.val) % 5 = x.val := by omega
  have hy : (x.val + 5 * y.val) / 5 = y.val := by omega
  congr 1
  · exact Fin.ext hx
  · exact Fin.ext hy

/-- Equal coordinate-model observations determine equal reference states. -/
theorem keccakToModel_inj {a b : KeccakState}
    (h : keccakToModel a = keccakToModel b) : a = b := by
  suffices hlanes : a.lanes = b.lanes by
    cases a
    cases b
    cases hlanes
    rfl
  apply Vector.ext
  intro i hi
  let x : Fin 5 := ⟨i % 5, Nat.mod_lt _ (by decide)⟩
  let y : Fin 5 := ⟨i / 5, by omega⟩
  have hp := congrFun h (x, y)
  have hindex : (keccakLaneIndex x y).val = i := by
    simp only [keccakLaneIndex, x, y]
    omega
  apply UInt64.toBitVec_inj.mp
  change a.lanes[(keccakLaneIndex x y).val].toBitVec =
    b.lanes[(keccakLaneIndex x y).val].toBitVec at hp
  simpa only [hindex] using hp

/-- Lane observation assigns bit `z` to the natural value's bit `z`.
This is the little-endian lane convention; sponge byte packing is separate. -/
theorem keccakLane_bit (a : KeccakState) (x y : Fin 5) (z : Fin 64) :
    (keccakToModel a (x, y)).getLsbD z.val =
      (keccakLane a x y).toNat.testBit z.val := by
  rfl

/-- Coordinate addition modulo five. -/
def keccakCoord (x : Fin 5) (n : Nat) : Fin 5 :=
  ⟨(x.val + n) % 5, Nat.mod_lt _ (by decide)⟩

/-- Rotate left modulo 64, explicitly handling zero to avoid masked right shift 64. -/
def keccakRotl (a : UInt64) (r : Nat) : UInt64 :=
  let k := r % 64
  if k = 0 then a else (a <<< UInt64.ofNat k) ||| (a >>> UInt64.ofNat (64 - k))

/-- Machine rotation corresponds to the standard bit-vector rotation at every amount. -/
theorem toBitVec_keccakRotl (a : UInt64) (r : Nat) :
    (keccakRotl a r).toBitVec = a.toBitVec.rotateLeft r := by
  have hk : r % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_def]
  simp only [keccakRotl]
  split
  next h => simp [h, BitVec.ushiftRight_eq_zero]
  next h =>
    have hr : 64 - r % 64 < 64 := by omega
    have hl := congrArg UInt64.toBitVec (UInt64.ofBitVec_shiftLeft a.toBitVec (r % 64) hk)
    have hs := congrArg UInt64.toBitVec
      (UInt64.ofBitVec_shiftRight a.toBitVec (64 - r % 64) hr)
    simp only [UInt64.ofBitVec_toBitVec] at hl hs
    rw [UInt64.toBitVec_or, ← hl, ← hs]

/-- Rotation transports each bit by the standard modulo-64 lane rule. -/
theorem keccakRotl_bit (a : UInt64) (r : Nat) (z : Fin 64) :
    (keccakRotl a r).toBitVec.getLsbD z.val =
      if z.val < r % 64 then a.toBitVec.getLsbD (64 - r % 64 + z.val)
      else a.toBitVec.getLsbD (z.val - r % 64) := by
  rw [toBitVec_keccakRotl, BitVec.getLsbD_rotateLeft]
  simp only [z.isLt, decide_true, Bool.true_and]

/-- Rho offsets, Table 2 of FIPS 202, stored in x+5*y order. -/
def keccakRhoOffsets : Vector Nat 25 :=
  #v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
     41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- Iota constants for rounds 0 through 23, FIPS 202 Algorithms 5–6. -/
def keccakRoundConstants : Vector UInt64 24 :=
  #v[0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
     0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
     0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
     0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
     0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
     0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
     0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
     0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Theta: cache the five column parities and the five column corrections. -/
def keccakTheta (a : KeccakState) : KeccakState :=
  let c := Vector.ofFn fun x : Fin 5 ↦
    keccakLane a x 0 ^^^ keccakLane a x 1 ^^^ keccakLane a x 2 ^^^
      keccakLane a x 3 ^^^ keccakLane a x 4
  let d := Vector.ofFn fun x : Fin 5 ↦
    c[keccakCoord x 4] ^^^ keccakRotl c[keccakCoord x 1] 1
  keccakOfLanes fun x y ↦ keccakLane a x y ^^^ d[x]

/-- Rho rotates each lane by its published offset. -/
def keccakRho (a : KeccakState) : KeccakState :=
  keccakOfLanes fun x y ↦ keccakRotl (keccakLane a x y)
    keccakRhoOffsets[keccakLaneIndex x y]

/-- Pi in inverse coordinates: output `(x,y)` takes input `(x+3*y,x)` modulo five. -/
def keccakPi (a : KeccakState) : KeccakState :=
  keccakOfLanes fun x y ↦ keccakLane a (keccakCoord x (3 * y.val)) x

/-- Pi's inverse-coordinate implementation has the standard forward placement
`B[y, 2*x+3*y] = A[x,y]` from FIPS 202 §3.2.3. -/
theorem keccakLane_pi_forward (a : KeccakState) (x y : Fin 5) :
    keccakLane (keccakPi a) y (keccakCoord x (x.val + 3 * y.val)) =
      keccakLane a x y := by
  rw [keccakPi, keccakLane_ofLanes]
  have hc : ∀ x y : Fin 5,
      keccakCoord y (3 * (keccakCoord x (x.val + 3 * y.val)).val) = x := by decide
  rw [hc]

/-- Chi reads the original row for all three lanes, as in FIPS 202 §3.2.4. -/
def keccakChi (a : KeccakState) : KeccakState :=
  keccakOfLanes fun x y ↦ keccakLane a x y ^^^
    ((~~~keccakLane a (keccakCoord x 1) y) &&& keccakLane a (keccakCoord x 2) y)

/-- Iota changes only lane `(0,0)`, using the selected round's constant. -/
def keccakIota (a : KeccakState) (round : Fin 24) : KeccakState :=
  keccakOfLanes fun x y ↦
    if x = 0 ∧ y = 0 then keccakLane a x y ^^^ keccakRoundConstants[round]
    else keccakLane a x y

namespace KeccakModel

/-- The parity of one model column. -/
def column (a : KeccakModel) (x : Fin 5) : BitVec 64 :=
  a (x, 0) ^^^ a (x, 1) ^^^ a (x, 2) ^^^ a (x, 3) ^^^ a (x, 4)

/-- FIPS theta expressed directly on coordinate bit-vector lanes. -/
def theta (a : KeccakModel) : KeccakModel := fun (x, y) ↦
  a (x, y) ^^^ (column a (keccakCoord x 4) ^^^ (column a (keccakCoord x 1)).rotateLeft 1)

/-- FIPS rho expressed on coordinate bit-vector lanes. -/
def rho (a : KeccakModel) : KeccakModel := fun (x, y) ↦
  (a (x, y)).rotateLeft keccakRhoOffsets[keccakLaneIndex x y]

/-- FIPS pi expressed on coordinate bit-vector lanes. -/
def pi (a : KeccakModel) : KeccakModel := fun (x, y) ↦
  a (keccakCoord x (3 * y.val), x)

/-- FIPS chi expressed on coordinate bit-vector lanes. -/
def chi (a : KeccakModel) : KeccakModel := fun (x, y) ↦
  a (x, y) ^^^ ((~~~a (keccakCoord x 1, y)) &&& a (keccakCoord x 2, y))

/-- FIPS iota expressed on coordinate bit-vector lanes. -/
def iota (a : KeccakModel) (round : Fin 24) : KeccakModel := fun (x, y) ↦
  if x = 0 ∧ y = 0 then a (x, y) ^^^ keccakRoundConstants[round].toBitVec else a (x, y)

/-- One model round in theta/rho/pi/chi/iota order. -/
def round (a : KeccakModel) (r : Fin 24) : KeccakModel := iota (chi (pi (rho (theta a)))) r

end KeccakModel

/-- Theta commutes with the bit-vector coordinate observation. -/
theorem keccakToModel_theta (a : KeccakState) :
    keccakToModel (keccakTheta a) = KeccakModel.theta (keccakToModel a) := by
  funext p
  rcases p with ⟨x, y⟩
  simp [keccakToModel, keccakTheta, keccakLane_ofLanes, KeccakModel.theta,
    KeccakModel.column, toBitVec_keccakRotl]

/-- Rho commutes with the bit-vector coordinate observation. -/
theorem keccakToModel_rho (a : KeccakState) :
    keccakToModel (keccakRho a) = KeccakModel.rho (keccakToModel a) := by
  funext p
  rcases p with ⟨x, y⟩
  simp [keccakToModel, keccakRho, keccakLane_ofLanes, KeccakModel.rho,
    toBitVec_keccakRotl]

/-- Pi commutes with the bit-vector coordinate observation. -/
theorem keccakToModel_pi (a : KeccakState) :
    keccakToModel (keccakPi a) = KeccakModel.pi (keccakToModel a) := by
  funext p
  rcases p with ⟨x, y⟩
  simp [keccakToModel, keccakPi, keccakLane_ofLanes, KeccakModel.pi]

/-- Chi commutes with the bit-vector coordinate observation. -/
theorem keccakToModel_chi (a : KeccakState) :
    keccakToModel (keccakChi a) = KeccakModel.chi (keccakToModel a) := by
  funext p
  rcases p with ⟨x, y⟩
  simp [keccakToModel, keccakChi, keccakLane_ofLanes, KeccakModel.chi]

/-- Iota commutes with the bit-vector coordinate observation. -/
theorem keccakToModel_iota (a : KeccakState) (r : Fin 24) :
    keccakToModel (keccakIota a r) = KeccakModel.iota (keccakToModel a) r := by
  funext p
  rcases p with ⟨x, y⟩
  simp [keccakToModel, keccakIota, keccakLane_ofLanes, KeccakModel.iota]
  split <;> simp

/-- One legible reference round, FIPS 202 §3.3. -/
def keccakRound (a : KeccakState) (r : Fin 24) : KeccakState :=
  keccakIota (keccakChi (keccakPi (keccakRho (keccakTheta a)))) r

/-- The complete round follows the coordinate model, using the five step laws. -/
theorem keccakToModel_round (a : KeccakState) (r : Fin 24) :
    keccakToModel (keccakRound a r) = KeccakModel.round (keccakToModel a) r := by
  simp only [keccakRound, KeccakModel.round, keccakToModel_iota, keccakToModel_chi,
    keccakToModel_pi, keccakToModel_rho, keccakToModel_theta]

/-- Execute the first `n` rounds, in ascending round order, structurally over `n`. -/
def keccakRounds (a : KeccakState) : (n : Nat) → n ≤ 24 → KeccakState
  | 0, _ => a
  | n + 1, h => keccakRound (keccakRounds a n (by omega)) ⟨n, by omega⟩

/-- Execute the first `n` coordinate-model rounds in ascending order. -/
def KeccakModel.rounds (a : KeccakModel) : (n : Nat) → n ≤ 24 → KeccakModel
  | 0, _ => a
  | n + 1, h => KeccakModel.round (KeccakModel.rounds a n (by omega)) ⟨n, by omega⟩

/-- Induction lifts the round correspondence to every bounded prefix. -/
theorem keccakToModel_rounds (a : KeccakState) (n : Nat) (h : n ≤ 24) :
    keccakToModel (keccakRounds a n h) = KeccakModel.rounds (keccakToModel a) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [keccakRounds, KeccakModel.rounds, keccakToModel_round, ih]

/-- Keccak-f[1600]: exactly 24 reference rounds (FIPS 202 §3.3). -/
def keccakF1600 (a : KeccakState) : KeccakState := keccakRounds a 24 (by decide)

/-- The reference permutation corresponds to all 24 standard model rounds. -/
theorem keccakToModel_f1600 (a : KeccakState) :
    keccakToModel (keccakF1600 a) = KeccakModel.rounds (keccakToModel a) 24 (by decide) :=
  keccakToModel_rounds a 24 (by decide)

end STFSpec.Hash
