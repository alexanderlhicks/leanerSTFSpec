/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Numeric
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Memory

/-!
# Pure VmConfig memory pricing

Library `EthVmCore`. The private structural fold follows pinned EELS
`src/ethereum/forks/amsterdam/vm/gas.py:749–813`: skip zero windows, price strict rounded growth and retain the
seed once. Nat endpoint observations never wrap. Pricing allocates no `Memory`.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7, Q63.
-/
namespace STFSpec.Vm.Core
open STFSpec.Base

private theorem round_aligned (n : Nat) : ceil32 n % 32 = 0 := ceil32_mod_eq_zero n
private theorem le_round (n : Nat) : n ≤ ceil32 n := le_ceil32 n
private theorem round_self (n : Nat) (h : n % 32 = 0) : ceil32 n = n :=
  ceil32_eq_self_of_mod_eq_zero n h
private theorem round_idem (n : Nat) : ceil32 (ceil32 n) = ceil32 n := ceil32_ceil32 n
private theorem round_mono {n m : Nat} (h : n ≤ m) : ceil32 n ≤ ceil32 m :=
  ceil32_le_of_mod_eq_zero _ _ (Nat.le_trans h (le_ceil32 m)) (ceil32_mod_eq_zero m)
private theorem round_max (n m : Nat) : ceil32 (max n m) = max (ceil32 n) (ceil32 m) := by
  rcases Nat.le_total n m with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (round_mono h)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (round_mono h)]

private def cost (a n : Nat) : Nat :=
  let sizeInWords := ceil32 n / 32
  a * sizeInWords + sizeInWords ^ 2 / 512

private theorem cost_exact (a n : Nat) :
    cost a n = a * (ceil32 n / 32) + (ceil32 n / 32)^2 / 512 := rfl

private theorem cost_source (a n : Nat) :
    cost a n = (ceil32 n / 32) * a + (ceil32 n / 32)^2 / 512 := by
  simp only [cost, Nat.mul_comm a]

private theorem cost_mono (a : Nat) {n m : Nat} (h : n ≤ m) : cost a n ≤ cost a m := by
  have hw : ceil32 n / 32 ≤ ceil32 m / 32 := Nat.div_le_div_right (round_mono h)
  have hm := Nat.mul_le_mul_left a hw
  have hs := Nat.mul_le_mul hw hw
  have hd : (ceil32 n / 32)^2 / 512 ≤ (ceil32 m / 32)^2 / 512 :=
    Nat.div_le_div_right (by simpa [Nat.pow_two] using hs)
  simpa [cost, Nat.pow_two] using Nat.add_le_add hm hd

private theorem cost_round (a n : Nat) : cost a (ceil32 n) = cost a n := by
  simp only [cost, round_idem]

private theorem cost_coefficient_congr (a b n : Nat) (h : a = b) : cost a n = cost b n := by
  subst b
  rfl

/-- Pure memory extension parameters; EELS `src/ethereum/forks/amsterdam/vm/gas.py:341–353`. -/
structure ExtendMemory where
  /-- Complete price, including the supplied seed once. -/
  cost : Nat
  /-- Additional bytes, without performing the allocation. -/
  expandBy : Nat

private def sourceFold (a currentSize sizeToExpand costToCharge : Nat) :
    List (U256 × U256) → ExtendMemory
  | [] => ⟨costToCharge, sizeToExpand⟩
  | (startPosition, size) :: windows =>
    if size.toNat = 0 then sourceFold a currentSize sizeToExpand costToCharge windows
    else
      let beforeSize := ceil32 currentSize
      let afterSize := ceil32 (startPosition.toNat + size.toNat)
      if beforeSize < afterSize then
        sourceFold a afterSize (sizeToExpand + (afterSize - beforeSize))
          (costToCharge + (cost a afterSize - cost a beforeSize)) windows
      else sourceFold a currentSize sizeToExpand costToCharge windows

private def extend (a z l : Nat) (ws : List (U256 × U256)) : ExtendMemory :=
  sourceFold a l 0 z ws

/-- Private proof-only endpoint model; not a runtime accessor. -/
private def endpoint : List (U256 × U256) → Nat
  | [] => 0
  | (s,k)::ws => if k.toNat = 0 then endpoint ws else max (s.toNat+k.toNat) (endpoint ws)

private theorem endpoint_foldr (ws : List (U256 × U256)) :
    endpoint ws = ws.foldr (fun w acc => if w.2.toNat = 0 then acc
      else max (w.1.toNat + w.2.toNat) acc) 0 := by
  induction ws with
  | nil => rfl
  | cons p ws ih => simp only [endpoint, List.foldr_cons, ih]

/-- Logical rounded maximum, with no storage representation claim. -/
private def finalSize (l : Nat) (ws : List (U256 × U256)) : Nat := ceil32 (max l (endpoint ws))

private theorem final_lower (l : Nat) (ws : List (U256 × U256)) : ceil32 l ≤ finalSize l ws :=
  round_mono (Nat.le_max_left _ _)
private theorem final_aligned (l : Nat) (ws : List (U256 × U256)) : finalSize l ws % 32 = 0 :=
  round_aligned _

private theorem final_cons (l : Nat) (s k : U256) (ws : List (U256 × U256)) (hk : k.toNat ≠ 0) :
    finalSize l ((s,k)::ws) =
      if ceil32 l < ceil32 (s.toNat+k.toNat) then finalSize (ceil32 (s.toNat+k.toNat)) ws
      else finalSize l ws := by
  simp only [finalSize, endpoint, ite_eq_right hk, round_max, round_idem]
  split <;> omega

/-- Both subtractions performed in a growing source step have ordered operands. -/
private theorem growth_subtractions_valid (a b d : Nat) (h : b < d) :
    b ≤ d ∧ cost a b ≤ cost a d := ⟨Nat.le_of_lt h, cost_mono a (Nat.le_of_lt h)⟩

private theorem sourceFold_summary (a l e g : Nat) (ws : List (U256 × U256)) :
    sourceFold a l e g ws =
      ⟨g + (cost a (finalSize l ws) - cost a (ceil32 l)),
        e + (finalSize l ws - ceil32 l)⟩ := by
  induction ws generalizing l e g with
  | nil => simp [sourceFold, finalSize, endpoint]
  | cons p ws ih =>
    rcases p with ⟨s,k⟩
    by_cases hk : k.toNat = 0
    · simp only [sourceFold, hk, ite_eq_left, finalSize, endpoint]
      exact ih l e g
    · simp only [sourceFold, ite_eq_right hk]
      rw [final_cons l s k ws hk]
      split
      next h =>
        rw [ih, round_idem]
        have hd := final_lower (ceil32 (s.toNat+k.toNat)) ws
        rw [round_idem] at hd
        have hbd := growth_subtractions_valid a (ceil32 l) (ceil32 (s.toNat+k.toNat)) h
        have hdf := cost_mono a hd
        congr 1 <;> omega
      next h =>
        rw [ih]

private theorem empty_result (a z l : Nat) : extend a z l [] = ⟨z,0⟩ := rfl

private theorem raw_summary (a z l : Nat) (ws : List (U256 × U256)) :
    extend a z l ws =
      ⟨z + (cost a (finalSize l ws) - cost a (ceil32 l)),
        finalSize l ws - ceil32 l⟩ := by
  simpa [extend] using sourceFold_summary a l 0 z ws

private theorem extent_closed (a z l : Nat) (ws : List (U256 × U256)) (hl : l % 32 = 0) :
    (extend a z l ws).expandBy = finalSize l ws - l := by
  rw [raw_summary, round_self l hl]

private theorem cost_closed (a z l : Nat) (ws : List (U256 × U256)) (hl : l % 32 = 0) :
    (extend a z l ws).cost = z + (cost a (finalSize l ws) - cost a l) := by
  rw [raw_summary, round_self l hl]

private theorem sourceFold_zero (a l e g : Nat) (s : U256) (pre post : List (U256 × U256)) :
    sourceFold a l e g (pre ++ (s,U256.zero)::post) = sourceFold a l e g (pre ++ post) := by
  induction pre generalizing l e g with
  | nil => simp [sourceFold, U256.toNat_zero]
  | cons p pre ih =>
    rcases p with ⟨t,k⟩
    simp only [List.cons_append, sourceFold]
    split
    · exact ih _ _ _
    · split <;> exact ih _ _ _

private theorem zero_erasure (a z l : Nat) (s : U256) (pre post : List (U256 × U256)) :
    extend a z l (pre ++ (s,U256.zero)::post) = extend a z l (pre ++ post) :=
  sourceFold_zero a l 0 z s pre post

private theorem extent_alignment (a z l : Nat) (ws : List (U256 × U256)) (hl : l % 32 = 0) :
    (extend a z l ws).expandBy % 32 = 0 := by
  rw [extent_closed a z l ws hl]
  have hf := final_aligned l ws
  have hb := final_lower l ws
  rw [round_self l hl] at hb
  omega

private theorem endpoint_covers (s k : U256) (ws : List (U256 × U256))
    (hm : (s,k) ∈ ws) (hk : k.toNat ≠ 0) : s.toNat+k.toNat ≤ endpoint ws := by
  induction ws with
  | nil => simp at hm
  | cons p ws ih =>
    rcases p with ⟨t,j⟩
    simp only [List.mem_cons] at hm
    rcases hm with he | hm
    · cases he
      simp only [endpoint, ite_eq_right hk]
      exact Nat.le_max_left _ _
    · have hb := ih hm
      simp only [endpoint]
      split
      · exact hb
      · exact Nat.le_trans hb (Nat.le_max_right _ _)

private theorem coverage (a z l : Nat) (s k : U256) (ws : List (U256 × U256)) (hl : l % 32 = 0)
    (hm : (s,k) ∈ ws) (hk : k.toNat ≠ 0) : s.toNat+k.toNat ≤ l + (extend a z l ws).expandBy := by
  rw [extent_closed a z l ws hl]
  have h1 := endpoint_covers s k ws hm hk
  have h2 := le_round (max l (endpoint ws))
  have h3 := Nat.le_max_right l (endpoint ws)
  have h4 := final_lower l ws
  rw [round_self l hl] at h4
  unfold finalSize at *
  omega

private theorem extension_congr (a b z y l : Nat) (ws : List (U256 × U256))
    (ha : a = b) (hz : z = y) : extend a z l ws = extend b y l ws := by
  subst b
  subst y
  rfl


/-- Pure allocation cost, observing only `memoryPerWord`.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:749–773`. -/
def calculateMemoryGasCost (cfg : VmConfig) (n : Nat) : Nat := cost cfg.costs.memoryPerWord n

/-- Complete pure extension price, without expanding `Memory`.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:776–813`. -/
def calculateGasExtendMemory (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) : ExtendMemory :=
  extend cfg.costs.memoryPerWord cfg.costs.zero m.size ws

/-- Exact scalar cost, independent of the zero seed. -/
theorem calculateMemoryGasCost_eq (cfg : VmConfig) (n : Nat) :
    calculateMemoryGasCost cfg n = cfg.costs.memoryPerWord * (ceil32 n / 32) +
      (ceil32 n / 32)^2 / 512 := rfl

/-- Monotone scalar cost for every raw configuration, including zero coefficient. -/
theorem calculateMemoryGasCost_mono (cfg : VmConfig) (n n' : Nat) (h : n ≤ n') :
    calculateMemoryGasCost cfg n ≤ calculateMemoryGasCost cfg n' := by
  exact cost_mono cfg.costs.memoryPerWord h

/-- Empty extension retains the arbitrary seed and returns zero extent. -/
theorem calculateGasExtendMemory_nil (cfg : VmConfig) (m : Memory) :
    calculateGasExtendMemory cfg m [] = { cost := cfg.costs.zero, expandBy := 0 } := rfl

/-- Any zero window can be erased, including at an unused huge start. -/
theorem calculateGasExtendMemory_zero (cfg : VmConfig) (m : Memory)
    (as bs : List (U256 × U256)) (s : U256) :
    calculateGasExtendMemory cfg m (as ++ [(s, U256.zero)] ++ bs) =
      calculateGasExtendMemory cfg m (as ++ bs) := by
  simpa [calculateGasExtendMemory, List.append_assoc] using
    zero_erasure cfg.costs.memoryPerWord cfg.costs.zero m.size s as bs

/-- Rounded maximum nonempty endpoint minus the old aligned memory size. -/
theorem calculateGasExtendMemory_expandBy (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    let F := ceil32 (max m.size (ws.foldr (fun w acc =>
      if w.2.toNat = 0 then acc else max (w.1.toNat + w.2.toNat) acc) 0))
    (calculateGasExtendMemory cfg m ws).expandBy = F - m.size := by
  simpa [calculateGasExtendMemory, finalSize, endpoint_foldr] using
    extent_closed cfg.costs.memoryPerWord cfg.costs.zero m.size ws (Memory.size_mod32 m)

/-- Seed-aware closed cost; the two public cost terms are the exact scalar formula. -/
theorem calculateGasExtendMemory_cost (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    let F := ceil32 (max m.size (ws.foldr (fun w acc =>
      if w.2.toNat = 0 then acc else max (w.1.toNat + w.2.toNat) acc) 0))
    (calculateGasExtendMemory cfg m ws).cost = cfg.costs.zero +
      (calculateMemoryGasCost cfg F - calculateMemoryGasCost cfg m.size) := by
  simpa [calculateGasExtendMemory, calculateMemoryGasCost, finalSize, endpoint_foldr] using
    cost_closed cfg.costs.memoryPerWord cfg.costs.zero m.size ws (Memory.size_mod32 m)

/-- The returned increment supplies the existing local Memory expansion proof. -/
theorem calculateGasExtendMemory_aligned (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    (calculateGasExtendMemory cfg m ws).expandBy % 32 = 0 := by
  exact extent_alignment _ _ _ _ (Memory.size_mod32 m)

/-- Every listed window is empty or covered after the priced increment. -/
theorem calculateGasExtendMemory_covers (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) (s k : U256) (h : (s,k) ∈ ws) :
    k.toNat = 0 ∨ s.toNat + k.toNat ≤
      m.size + (calculateGasExtendMemory cfg m ws).expandBy := by
  by_cases hz : k.toNat = 0
  · exact Or.inl hz
  · exact Or.inr (coverage _ _ _ _ _ _ (Memory.size_mod32 m) h hz)

/-- Only the memory-word coefficient affects scalar cost. -/
theorem calculateMemoryGasCost_congr (cfg cfg' : VmConfig)
    (h : cfg.costs.memoryPerWord = cfg'.costs.memoryPerWord) (n : Nat) :
    calculateMemoryGasCost cfg n = calculateMemoryGasCost cfg' n := by
  exact cost_coefficient_congr _ _ _ h

/-- Only the memory-word coefficient and zero seed affect the full extension result. -/
theorem calculateGasExtendMemory_congr (cfg cfg' : VmConfig)
    (ha : cfg.costs.memoryPerWord = cfg'.costs.memoryPerWord)
    (hz : cfg.costs.zero = cfg'.costs.zero) (m : Memory) (ws : List (U256 × U256)) :
    calculateGasExtendMemory cfg m ws = calculateGasExtendMemory cfg' m ws := by
  exact extension_congr _ _ _ _ _ _ ha hz

end STFSpec.Vm.Core
