/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.Reference

/-!
# Graph-specified natural-reference inverse

Library `EthField`. Signed Euclidean coefficients specify the complete source result,
including composite nonunits. The executable worker is private; consumers use the graph.
Source: pinned py-ecc 8.0.0 `py_ecc/utils.py:21–39`.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field

/-- Exact finite Euclidean coefficient graph. The loop stops at both zero and one. -/
inductive EuclideanCoefficient : Nat → Nat → Int → Int → Int → Prop where
  /-- Terminal state: retain the current signed coefficient. -/
  | done (low high : Nat) (lm hm : Int) (h : low ≤ 1) :
      EuclideanCoefficient low high lm hm lm
  /-- One simultaneous source transition, allowed only above one. -/
  | step (low high : Nat) (lm hm z : Int) (h : 1 < low)
      (rest : EuclideanCoefficient (high % low) low
        (hm - lm * (high / low : Nat)) lm z) :
      EuclideanCoefficient low high lm hm z

/-- Every coefficient state has a finite graph derivation. -/
theorem euclideanCoefficient_total (low high : Nat) (lm hm : Int) :
    ∃ z, EuclideanCoefficient low high lm hm z := by
  induction low using Nat.strongRecOn generalizing high lm hm with
  | ind low ih =>
    by_cases h : 1 < low
    · obtain ⟨z, hz⟩ := ih (high % low) (Nat.mod_lt high (by omega)) low
        (hm - lm * (high / low : Nat)) lm
      exact ⟨z, .step low high lm hm z h hz⟩
    · exact ⟨lm, .done low high lm hm (by omega)⟩

/-- A coefficient state determines exactly one final signed coefficient. -/
theorem euclideanCoefficient_unique (low high : Nat) (lm hm x y : Int)
    (hx : EuclideanCoefficient low high lm hm x)
    (hy : EuclideanCoefficient low high lm hm y) : x = y := by
  induction hx with
  | done low high lm hm h =>
    cases hy with
    | done => rfl
    | step _ _ _ _ _ h' _ => omega
  | step low high lm hm z h rest ih =>
    cases hy with
    | done _ _ _ _ h' => omega
    | step _ _ _ _ _ _ rest' => exact ih rest'


/-- The terminal low and its signed input coefficient. -/
private def finish (low high : Nat) (lm hm : Int) : Nat × Int :=
  if 1 < low then
    finish (high % low) low (hm - lm * (high / low : Nat)) lm
  else (low, lm)
termination_by low
decreasing_by exact Nat.mod_lt high (by omega)

private def normalize (p : Nat) (z : Int) : Nat := (z % (p : Int)).toNat

/-- Deliberately only a natural-input, positive-modulus completion candidate. -/
private def completion (a p : Nat) : Nat :=
  if a % p = 0 then 0 else normalize p (finish (a % p) p 1 0).2

private theorem finish_terminal (low high : Nat) (lm hm : Int) :
    (finish low high lm hm).1 ≤ 1 := by
  rw [finish]
  split
  next h => exact finish_terminal (high % low) low (hm - lm * (high / low : Nat)) lm
  next h => change low ≤ 1; omega
termination_by low
decreasing_by exact Nat.mod_lt high (by omega)

private theorem normalize_lt (p : Nat) (hp : 0 < p) (z : Int) :
    normalize p z < p := by
  have hn := Int.emod_nonneg z (show (p : Int) ≠ 0 by omega)
  have hb := Int.emod_lt_of_pos z (show (0 : Int) < p by omega)
  unfold normalize
  omega

private theorem completion_lt (a p : Nat) (hp : 0 < p) : completion a p < p := by
  unfold completion
  split
  · exact hp
  · exact normalize_lt p hp _

private theorem completion_of_zero_residue (a p : Nat) (h : a % p = 0) :
    completion a p = 0 := by simp [completion, h]

private theorem completion_zero (p : Nat) : completion 0 p = 0 := by
  exact completion_of_zero_residue 0 p (Nat.zero_mod p)

private theorem completion_reduction (a p : Nat) : completion (a % p) p = completion a p := by
  simp only [completion, Nat.mod_mod]

private theorem completion_one (p : Nat) (hp : 1 < p) : completion 1 p = 1 := by
  have hmod : 1 % p = 1 := Nat.mod_eq_of_lt hp
  simp [completion, hmod, finish, normalize, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1)
    (by omega : (1 : Int) < p)]

private theorem cast_mod (high low : Nat) :
    ((high % low : Nat) : Int) = (high : Int) - (low : Int) * (high / low : Nat) := by
  have h := congrArg (fun n : Nat ↦ (n : Int)) (Nat.mod_add_div high low)
  simp only [Int.natCast_add, Int.natCast_mul] at h
  omega

/-- One exact congruence-preserving Euclidean state transition, without primality. -/
private theorem step_congruence (a p low high : Nat) (lm hm : Int)
    (hl : (lm * (a : Int)) % (p : Int) = (low : Int) % (p : Int))
    (hh : (hm * (a : Int)) % (p : Int) = (high : Int) % (p : Int)) :
    ((hm - lm * (high / low : Nat)) * (a : Int)) % (p : Int) =
      ((high % low : Nat) : Int) % (p : Int) := by
  calc
    _ = (hm * (a : Int) - (lm * (a : Int)) * (high / low : Nat)) % (p : Int) := by
      congr 1
      rw [Int.sub_mul]
      congr 1
      ac_rfl
    _ = ((high : Int) - (low : Int) * (high / low : Nat)) % (p : Int) := by
      rw [Int.sub_emod]
      conv => rhs; rw [Int.sub_emod]
      rw [Int.mul_emod (lm * (a : Int)), Int.mul_emod (low : Int), hl, hh]
    _ = ((high % low : Nat) : Int) % (p : Int) := by rw [cast_mod]

/-- The actual recursive result preserves both initial modular coefficient invariants. -/
private theorem finish_congruence (a p low high : Nat) (lm hm : Int)
    (hl : (lm * (a : Int)) % (p : Int) = (low : Int) % (p : Int))
    (hh : (hm * (a : Int)) % (p : Int) = (high : Int) % (p : Int)) :
    ((finish low high lm hm).2 * (a : Int)) % (p : Int) =
      ((finish low high lm hm).1 : Int) % (p : Int) := by
  rw [finish]
  split
  next h =>
    exact finish_congruence a p (high % low) low (hm - lm * (high / low : Nat)) lm
      (step_congruence a p low high lm hm hl hh) hl
  next h => exact hl
termination_by low
decreasing_by exact Nat.mod_lt high (by omega)

private theorem initial_finish_congruence (a p : Nat) :
    ((finish (a % p) p 1 0).2 * (a : Int)) % (p : Int) =
      ((finish (a % p) p 1 0).1 : Int) % (p : Int) := by
  apply finish_congruence
  · simp only [Int.one_mul, Int.natCast_emod, Int.emod_emod]
  · simp

/-- Precise conditional inverse boundary: reaching one supplies a modular inverse. -/
private theorem completion_inverse_of_terminal_one (a p : Nat) (hp : 1 < p)
    (ha : a % p ≠ 0) (ht : (finish (a % p) p 1 0).1 = 1) :
    (completion a p * a) % p = 1 := by
  have hc := initial_finish_congruence a p
  rw [ht] at hc
  have hn := Int.emod_nonneg (finish (a % p) p 1 0).2
    (show (p : Int) ≠ 0 by omega)
  have hcast : ((completion a p : Nat) : Int) =
      (finish (a % p) p 1 0).2 % (p : Int) := by
    simp only [completion, ite_eq_right ha, normalize]
    exact Int.toNat_of_nonneg hn
  have heq : (((completion a p * a) % p : Nat) : Int) = (1 : Int) := by
    rw [Int.natCast_emod, Int.natCast_mul, hcast, Int.mul_emod, Int.emod_emod,
      ← Int.mul_emod, hc]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  omega

/-- Coprimality forces the terminal low to be one; the high bound excludes (0,1). -/
private theorem finish_one_of_gcd_one (low high : Nat) (lm hm : Int)
    (hhigh : 1 < high) (hg : Nat.gcd low high = 1) :
    (finish low high lm hm).1 = 1 := by
  rw [finish]
  split
  next h =>
    apply finish_one_of_gcd_one (high % low) low (hm - lm * (high / low : Nat)) lm h
    rw [← Nat.gcd_rec]
    exact hg
  next h =>
    change low = 1
    have hne : low ≠ 0 := by
      intro hz
      rw [hz, Nat.gcd_zero_left] at hg
      omega
    omega
termination_by low
decreasing_by exact Nat.mod_lt high (by omega)

/-- Ordinary universal unit law on all moduli >1, including composite moduli. -/
private theorem completion_inverse_of_gcd_one (a p : Nat) (hp : 1 < p)
    (hg : Nat.gcd a p = 1) : (completion a p * a) % p = 1 := by
  have hg' : Nat.gcd (a % p) p = 1 := by
    rw [← Nat.gcd_rec p a, Nat.gcd_comm]
    exact hg
  have ha : a % p ≠ 0 := by
    intro hz
    rw [hz, Nat.gcd_zero_left] at hg'
    omega
  exact completion_inverse_of_terminal_one a p hp ha
    (finish_one_of_gcd_one (a % p) p 1 0 hp hg')


private theorem finish_graph (low high : Nat) (lm hm : Int) :
    EuclideanCoefficient low high lm hm (finish low high lm hm).2 := by
  rw [finish]
  split
  next h =>
    exact .step low high lm hm _ h
      (finish_graph (high % low) low (hm - lm * (high / low : Nat)) lm)
  next h => exact .done low high lm hm (by omega)
termination_by low
decreasing_by exact Nat.mod_lt high (by omega)

namespace PrimeFieldRef

variable {p : Nat} [FieldModulus p]

/-- Complete canonical inverse graph, including source-style completion on nonunits. -/
def Inv0Model (a : PrimeFieldRef p) (y : Nat) : Prop :=
  if a.toNat = 0 then y = 0 else
    ∃ z : Int, EuclideanCoefficient a.toNat p 1 0 z ∧ y = (z % (p : Int)).toNat

private theorem inv0Model_functional (a : PrimeFieldRef p) (x y : Nat)
    (hx : Inv0Model a x) (hy : Inv0Model a y) : x = y := by
  by_cases ha : a.toNat = 0
  · simp only [Inv0Model, ite_eq_left ha] at hx hy
    omega
  · simp only [Inv0Model, ite_eq_right ha] at hx hy
    obtain ⟨u, hu, hxu⟩ := hx
    obtain ⟨v, hv, hyv⟩ := hy
    have huv := euclideanCoefficient_unique a.toNat p 1 0 u v hu hv
    rw [hxu, hyv, huv]

/-- Every canonical input has exactly one natural result in the public model. -/
theorem inv0Model_total (a : PrimeFieldRef p) :
    ∃ y : Nat, Inv0Model a y ∧ ∀ z : Nat, Inv0Model a z → z = y := by
  have hex : ∃ y : Nat, Inv0Model a y := by
    by_cases ha : a.toNat = 0
    · exact ⟨0, by simp [Inv0Model, ha]⟩
    · obtain ⟨z, hz⟩ := euclideanCoefficient_total a.toNat p 1 0
      exact ⟨(z % (p : Int)).toNat, by
        simp only [Inv0Model, ite_eq_right ha]
        exact ⟨z, hz, rfl⟩⟩
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, hy, fun z hz ↦ inv0Model_functional a z y hz hy⟩

/-- Every result in the model is canonical for the existing modulus. -/
theorem inv0Model_lt (a : PrimeFieldRef p) (y : Nat) (hy : Inv0Model a y) : y < p := by
  have hp := FieldModulus.one_lt (p := p)
  by_cases ha : a.toNat = 0
  · simp only [Inv0Model, ite_eq_left ha] at hy
    omega
  · simp only [Inv0Model, ite_eq_right ha] at hy
    obtain ⟨z, _, hyz⟩ := hy
    have hn := Int.emod_nonneg z (show (p : Int) ≠ 0 by omega)
    have hb := Int.emod_lt_of_pos z (show (0 : Int) < p by omega)
    omega

/-- Source-style inverse on every canonical element, as pinned py-ecc 8.0.0
`py_ecc/utils.py:21–39`. Zero returns zero; composite nonunits retain the source
Euclidean completion. Signed remainder precedes natural conversion. Metadata is unread. -/
def inv0 (a : PrimeFieldRef p) : PrimeFieldRef p := ofNat (completion a.toNat p)

private theorem completion_model (a : PrimeFieldRef p) : Inv0Model a (completion a.toNat p) := by
  have hmod : a.toNat % p = a.toNat := Nat.mod_eq_of_lt (toNat_lt a)
  by_cases ha : a.toNat = 0
  · simp [Inv0Model, ha, completion_zero]
  · simp only [Inv0Model, completion, hmod, ite_eq_right ha, normalize]
    exact ⟨_, finish_graph a.toNat p 1 0, rfl⟩

/-- The public model determines the entire observed executable result. -/
theorem toNat_inv0_iff (a : PrimeFieldRef p) (y : Nat) :
    Inv0Model a y ↔ (inv0 a).toNat = y := by
  have hc := completion_model a
  have hr := inv0Model_lt a _ hc
  have he : (inv0 a).toNat = completion a.toNat p := by
    rw [inv0, toNat_ofNat, Nat.mod_eq_of_lt hr]
  rw [he]
  constructor
  · intro hy
    exact inv0Model_functional a _ _ hc hy
  · intro hy
    rw [hy] at hc
    exact hc

/-- Zero inversion agrees with the source's explicit zero branch. -/
theorem inv0_zero : inv0 (zero : PrimeFieldRef p) = zero := by
  apply ext
  rw [toNat_zero]
  exact (toNat_inv0_iff zero 0).mp (by simp [Inv0Model, toNat_zero])

/-- Coprime inputs have a multiplicative inverse, including units modulo composites. -/
theorem mul_inv0_of_gcd_one (a : PrimeFieldRef p) (hg : Nat.gcd a.toNat p = 1) :
    mul a (inv0 a) = one := by
  apply ext
  rw [toNat_mul, toNat_one]
  have hc := completion_model a
  have he := (toNat_inv0_iff a _).mp hc
  rw [he, Nat.mul_comm]
  exact completion_inverse_of_gcd_one a.toNat p (FieldModulus.one_lt (p := p)) hg

end PrimeFieldRef
end STFSpec.Field
