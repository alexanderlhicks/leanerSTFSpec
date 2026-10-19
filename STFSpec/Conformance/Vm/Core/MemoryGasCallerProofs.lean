/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core

/-!
# Public-only pure memory-pricing clients

Library `EthConformance`. Only public pricing/Base/Memory laws are used;
local endpoint algebra is proof scaffolding, not a production interface.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7, Q63.
-/
namespace STFSpec.Conformance.Vm.Core.MemoryGasCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def endpoints (ws : List (U256 × U256)) : Nat :=
  ws.foldr (fun w acc => if w.2.toNat = 0 then acc
    else max (w.1.toNat + w.2.toNat) acc) 0
private def finalSize (l : Nat) (ws : List (U256 × U256)) : Nat := ceil32 (max l (endpoints ws))

private theorem round_mono {n m : Nat} (h : n ≤ m) : ceil32 n ≤ ceil32 m :=
  ceil32_le_of_mod_eq_zero _ _ (Nat.le_trans h (le_ceil32 m)) (ceil32_mod_eq_zero m)
private theorem round_max (n m : Nat) : ceil32 (max n m) = max (ceil32 n) (ceil32 m) := by
  rcases Nat.le_total n m with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (round_mono h)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (round_mono h)]
private theorem final_lower (l : Nat) (ws : List (U256 × U256)) : l ≤ finalSize l ws :=
  Nat.le_trans (Nat.le_max_left _ _) (le_ceil32 _)

private theorem extent_spec (cfg : VmConfig) (m : Memory) (ws : List (U256 × U256)) :
    (calculateGasExtendMemory cfg m ws).expandBy = finalSize m.size ws - m.size :=
  calculateGasExtendMemory_expandBy cfg m ws
private theorem cost_spec (cfg : VmConfig) (m : Memory) (ws : List (U256 × U256)) :
    (calculateGasExtendMemory cfg m ws).cost = cfg.costs.zero +
      (calculateMemoryGasCost cfg (finalSize m.size ws) - calculateMemoryGasCost cfg m.size) :=
  calculateGasExtendMemory_cost cfg m ws

private theorem result_ext {x y : ExtendMemory} (hc : x.cost = y.cost)
    (he : x.expandBy = y.expandBy) : x = y := by
  cases x
  cases y
  simp_all

private theorem same_size (cfg : VmConfig) (m n : Memory) (ws : List (U256 × U256))
    (h : m.size = n.size) : calculateGasExtendMemory cfg m ws = calculateGasExtendMemory cfg n ws := by
  apply result_ext
  · rw [cost_spec, cost_spec, h]
  · rw [extent_spec, extent_spec, h]

private theorem endpoints_append (xs ys : List (U256 × U256)) :
    endpoints (xs ++ ys) = max (endpoints xs) (endpoints ys) := by
  induction xs with
  | nil => simp [endpoints]
  | cons p xs ih =>
    rcases p with ⟨s,k⟩
    simp only [endpoints, List.cons_append, List.foldr_cons] at *
    split <;> simp_all only [Nat.max_assoc]
private theorem endpoints_perm {xs ys : List (U256 × U256)} (h : xs.Perm ys) :
    endpoints xs = endpoints ys := by
  induction h with
  | nil => rfl
  | cons p h ih => simp only [endpoints, List.foldr_cons] at *; rw [ih]
  | swap p q ws =>
    rcases p with ⟨s,k⟩
    rcases q with ⟨t,j⟩
    simp only [endpoints, List.foldr_cons]
    split <;> split <;> omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
private theorem final_perm (l : Nat) {xs ys : List (U256 × U256)} (h : xs.Perm ys) :
    finalSize l xs = finalSize l ys := by simp only [finalSize, endpoints_perm h]
private theorem final_append (l : Nat) (xs ys : List (U256 × U256)) :
    finalSize (finalSize l xs) ys = finalSize l (xs ++ ys) := by
  simp only [finalSize, endpoints_append, round_max, ceil32_ceil32, Nat.max_assoc]

private theorem permutation (cfg : VmConfig) (m : Memory) {xs ys : List (U256 × U256)}
    (h : xs.Perm ys) : calculateGasExtendMemory cfg m xs = calculateGasExtendMemory cfg m ys := by
  apply result_ext
  · rw [cost_spec, cost_spec, final_perm _ h]
  · rw [extent_spec, extent_spec, final_perm _ h]
private theorem final_subsumed (l : Nat) (s k : U256) (ws : List (U256 × U256))
    (h : s.toNat + k.toNat ≤ finalSize l ws) :
    finalSize l (ws ++ [(s,k)]) = finalSize l ws := by
  rw [← final_append]
  unfold finalSize endpoints at h
  simp only [finalSize, endpoints, List.foldr_cons, List.foldr_nil]
  split
  · simp only [Nat.max_zero, ceil32_ceil32]
  · simp only [Nat.max_zero]
    rw [Nat.max_eq_left h, ceil32_ceil32]
private theorem subsumed (cfg : VmConfig) (m : Memory) (s k : U256)
    (ws : List (U256 × U256)) (h : s.toNat + k.toNat ≤ finalSize m.size ws) :
    calculateGasExtendMemory cfg m (ws ++ [(s,k)]) = calculateGasExtendMemory cfg m ws := by
  apply result_ext
  · rw [cost_spec, cost_spec, final_subsumed _ _ _ _ h]
  · rw [extent_spec, extent_spec, final_subsumed _ _ _ _ h]
private theorem duplicate (cfg : VmConfig) (m : Memory) (w : U256 × U256)
    (ws : List (U256 × U256)) :
    calculateGasExtendMemory cfg m (w::w::ws) = calculateGasExtendMemory cfg m (w::ws) := by
  apply result_ext
  · rw [cost_spec, cost_spec]
    simp only [finalSize, endpoints, List.foldr_cons]
    split
    · rfl
    · simp only [← Nat.max_assoc, Nat.max_self]
  · rw [extent_spec, extent_spec]
    simp only [finalSize, endpoints, List.foldr_cons]
    split
    · rfl
    · simp only [← Nat.max_assoc, Nat.max_self]

private theorem expanded_size (m : Memory) (n : Nat) (h : n % 32 = 0) :
    (m.expand n h).size = m.size + n := by
  rw [← Memory.length_toBytes, Memory.toBytes_expand]
  simp [Memory.length_toBytes]

private theorem composition (cfg : VmConfig) (m : Memory) (xs ys : List (U256 × U256)) :
    let rA := calculateGasExtendMemory cfg m xs
    let mA := m.expand rA.expandBy (calculateGasExtendMemory_aligned cfg m xs)
    let rB := calculateGasExtendMemory cfg mA ys
    let r := calculateGasExtendMemory cfg m (xs ++ ys)
    r.expandBy = rA.expandBy + rB.expandBy ∧
      r.cost + cfg.costs.zero = rA.cost + rB.cost := by
  dsimp only
  have hi : (m.expand (calculateGasExtendMemory cfg m xs).expandBy
      (calculateGasExtendMemory_aligned cfg m xs)).size = finalSize m.size xs := by
    rw [expanded_size, extent_spec]
    have := final_lower m.size xs
    omega
  have heA := extent_spec cfg m xs
  have heB := extent_spec cfg (m.expand (calculateGasExtendMemory cfg m xs).expandBy
    (calculateGasExtendMemory_aligned cfg m xs)) ys
  have he := extent_spec cfg m (xs ++ ys)
  have hcA := cost_spec cfg m xs
  have hcB := cost_spec cfg (m.expand (calculateGasExtendMemory cfg m xs).expandBy
    (calculateGasExtendMemory_aligned cfg m xs)) ys
  have hc := cost_spec cfg m (xs ++ ys)
  rw [hi, final_append] at heB hcB
  have hb := final_lower m.size xs
  have hf := final_lower (finalSize m.size xs) ys
  rw [final_append] at hf
  have hc1 := calculateMemoryGasCost_mono cfg _ _ hb
  have hc2 := calculateMemoryGasCost_mono cfg _ _ hf
  constructor <;> omega

private theorem zero_seed_composition (cfg : VmConfig) (m : Memory)
    (xs ys : List (U256 × U256)) (hz : cfg.costs.zero = 0) :
    (calculateGasExtendMemory cfg m (xs ++ ys)).cost =
      (calculateGasExtendMemory cfg m xs).cost +
      (calculateGasExtendMemory cfg (m.expand (calculateGasExtendMemory cfg m xs).expandBy
        (calculateGasExtendMemory_aligned cfg m xs)) ys).cost := by
  have h := (composition cfg m xs ys).2
  simpa only [hz, Nat.add_zero] using h

private theorem expanded_window (cfg : VmConfig) (m : Memory) (ws : List (U256 × U256))
    (s k : U256) (h : (s,k) ∈ ws) :
    k.toNat = 0 ∨ s.toNat + k.toNat ≤
      (m.expand (calculateGasExtendMemory cfg m ws).expandBy
        (calculateGasExtendMemory_aligned cfg m ws)).size := by
  rw [expanded_size]
  exact calculateGasExtendMemory_covers cfg m ws s k h

private theorem read_preserved (m : Memory) (n : Nat) (hn : n % 32 = 0) (s k : Nat)
    (h : k = 0 ∨ s+k ≤ m.size) :
    (m.expand n hn).readBytes s k (by rw [expanded_size]; omega) = m.readBytes s k h := by
  apply Bytes.ext
  rw [Memory.readBytes_toList, Memory.readBytes_toList, Memory.toBytes_expand]
  rcases h with hz | hb
  · simp [hz]
  · have hlen : s+k ≤ m.toBytes.length := by rw [Memory.length_toBytes]; exact hb
    rw [List.take_drop, List.take_drop, List.take_append_of_le_length hlen]

private theorem admitted_write (cfg : VmConfig) (m : Memory) (ws : List (U256 × U256))
    (s k : U256) (h : (s,k) ∈ ws) (v : Bytes) (hv : v.size = k.toNat) :
    let m' := m.expand (calculateGasExtendMemory cfg m ws).expandBy
      (calculateGasExtendMemory_aligned cfg m ws)
    let hw : v.size = 0 ∨ s.toNat + v.size ≤ m'.size := by
      rw [hv]; exact expanded_window cfg m ws s k h
    (m'.write s.toNat v hw).readBytes s.toNat v.size
      (by rw [Memory.size_write]; exact hw) = v := by
  exact Memory.readBytes_write _ _ _ _

private theorem scalar_zero (cfg : VmConfig) : calculateMemoryGasCost cfg 0 = 0 := by
  rw [calculateMemoryGasCost_eq, ceil32_zero]
  simp
private theorem scalar_round (cfg : VmConfig) (n : Nat) :
    calculateMemoryGasCost cfg (ceil32 n) = calculateMemoryGasCost cfg n := by
  rw [calculateMemoryGasCost_eq, calculateMemoryGasCost_eq, ceil32_ceil32]


-- MP1
private theorem client_calculateMemoryGasCost_eq (cfg : VmConfig) (n : Nat) :
    calculateMemoryGasCost cfg n = cfg.costs.memoryPerWord * (ceil32 n / 32) +
      (ceil32 n / 32)^2 / 512 :=
  calculateMemoryGasCost_eq cfg n

-- MP2
private theorem client_calculateMemoryGasCost_mono (cfg : VmConfig) (n n' : Nat) (h : n ≤ n') :
    calculateMemoryGasCost cfg n ≤ calculateMemoryGasCost cfg n' :=
  calculateMemoryGasCost_mono cfg n n' h

-- MP3
private theorem client_calculateGasExtendMemory_nil (cfg : VmConfig) (m : Memory) :
    calculateGasExtendMemory cfg m [] = { cost := cfg.costs.zero, expandBy := 0 } :=
  calculateGasExtendMemory_nil cfg m

-- MP4: U256.zero is the existing word zero, not a new OfNat instance.
private theorem client_calculateGasExtendMemory_zero (cfg : VmConfig) (m : Memory)
    (as bs : List (U256 × U256)) (s : U256) :
    calculateGasExtendMemory cfg m (as ++ [(s, U256.zero)] ++ bs) =
      calculateGasExtendMemory cfg m (as ++ bs) :=
  calculateGasExtendMemory_zero cfg m as bs s

-- MP5: local mathematical let bindings.
private theorem client_calculateGasExtendMemory_expandBy (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    let F := ceil32 (max m.size (ws.foldr (fun w acc =>
      if w.2.toNat = 0 then acc else max (w.1.toNat + w.2.toNat) acc) 0))
    (calculateGasExtendMemory cfg m ws).expandBy = F - m.size :=
  calculateGasExtendMemory_expandBy cfg m ws

-- MP6: MP1 makes the two public cost applications exactly C_a(F) and C_a(m.size).
private theorem client_calculateGasExtendMemory_cost (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    let F := ceil32 (max m.size (ws.foldr (fun w acc =>
      if w.2.toNat = 0 then acc else max (w.1.toNat + w.2.toNat) acc) 0))
    (calculateGasExtendMemory cfg m ws).cost = cfg.costs.zero +
      (calculateMemoryGasCost cfg F - calculateMemoryGasCost cfg m.size) :=
  calculateGasExtendMemory_cost cfg m ws

-- MP7
private theorem client_calculateGasExtendMemory_aligned (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) :
    (calculateGasExtendMemory cfg m ws).expandBy % 32 = 0 :=
  calculateGasExtendMemory_aligned cfg m ws

-- MP8: empty sizes remain an explicit admitted alternative, including huge starts.
private theorem client_calculateGasExtendMemory_covers (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) (s k : U256) (h : (s,k) ∈ ws) :
    k.toNat = 0 ∨ s.toNat + k.toNat ≤
      m.size + (calculateGasExtendMemory cfg m ws).expandBy :=
  calculateGasExtendMemory_covers cfg m ws s k h

-- MP9
private theorem client_calculateMemoryGasCost_congr (cfg cfg' : VmConfig)
    (h : cfg.costs.memoryPerWord = cfg'.costs.memoryPerWord) (n : Nat) :
    calculateMemoryGasCost cfg n = calculateMemoryGasCost cfg' n :=
  calculateMemoryGasCost_congr cfg cfg' h n

-- MP10
private theorem client_calculateGasExtendMemory_congr (cfg cfg' : VmConfig)
    (ha : cfg.costs.memoryPerWord = cfg'.costs.memoryPerWord)
    (hz : cfg.costs.zero = cfg'.costs.zero) (m : Memory) (ws : List (U256 × U256)) :
    calculateGasExtendMemory cfg m ws = calculateGasExtendMemory cfg' m ws :=
  calculateGasExtendMemory_congr cfg cfg' ha hz m ws

end STFSpec.Conformance.Vm.Core.MemoryGasCallerProofs
