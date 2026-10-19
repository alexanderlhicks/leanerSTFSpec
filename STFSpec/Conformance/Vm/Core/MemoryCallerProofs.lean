/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core

/-!
# Public-only Memory clients

Library `EthConformance`. All ten ordinary laws and derived post-write read witnesses
are consumed through public APIs; no representation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.MemoryCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem client_1 : Memory.empty.toBytes = [] := Memory.toBytes_empty
private theorem client_2 (m : Memory) : m.toBytes.length = m.size := Memory.length_toBytes m
private theorem client_3 (m : Memory) : m.size % 32 = 0 := Memory.size_mod32 m
private theorem client_4 (m : Memory) (n : Nat) (h : n % 32 = 0) :
    (m.expand n h).toBytes = m.toBytes ++ List.replicate n 0 :=
  Memory.toBytes_expand m n h
private theorem client_5 (m : Memory) (s k : Nat) (h : k = 0 ∨ s + k ≤ m.size) :
    (m.readBytes s k h).toList = (m.toBytes.drop s).take k :=
  Memory.readBytes_toList m s k h
private theorem client_6 (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
    (m.write s v h).toBytes =
      m.toBytes.take s ++ v.toList ++ m.toBytes.drop (s + v.size) :=
  Memory.toBytes_write m s v h
private theorem client_7 (m : Memory) (s : Nat) :
    m.write s Bytes.empty (Or.inl Bytes.size_empty) = m := Memory.write_empty m s
private theorem client_8 (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) : (m.write s v h).size = m.size :=
  Memory.size_write m s v h
private theorem client_9 (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
    (m.write s v h).readBytes s v.size (by rw [Memory.size_write]; exact h) = v :=
  Memory.readBytes_write m s v h
private theorem client_10 (m : Memory) (s : Nat) (v : Bytes) (t k : Nat)
    (hW : v.size = 0 ∨ s + v.size ≤ m.size)
    (hR : k = 0 ∨ t + k ≤ m.size)
    (hD : k = 0 ∨ v.size = 0 ∨ t + k ≤ s ∨ s + v.size ≤ t) :
    (m.write s v hW).readBytes t k (by rw [Memory.size_write]; exact hR) =
      m.readBytes t k hR :=
  Memory.readBytes_write_disjoint m s v t k hW hR hD

/-- A caller derives expansion size from model laws alone. -/
private theorem expanded_size (m : Memory) (n : Nat) (h : n % 32 = 0) :
    (m.expand n h).size = m.size + n := by
  rw [← Memory.length_toBytes, Memory.toBytes_expand]
  simp [Memory.length_toBytes]

/-- A caller derives admitted read length, including empty windows beyond memory. -/
private theorem read_size (m : Memory) (s k : Nat) (h : k = 0 ∨ s + k ≤ m.size) :
    (m.readBytes s k h).size = k := by
  rw [← Bytes.length_toList, Memory.readBytes_toList]
  simp only [List.length_take, List.length_drop, Memory.length_toBytes]
  rcases h with hz | hb
  · simp [hz]
  · omega

/-- Arbitrary overlap is accepted when copying an immutable read snapshot. -/
private theorem copy_snapshot (m : Memory) (s t k : Nat)
    (hR : k = 0 ∨ s + k ≤ m.size) (hW : k = 0 ∨ t + k ≤ m.size) :
    let v := m.readBytes s k hR
    let hV : v.size = 0 ∨ t + v.size ≤ m.size := by rw [read_size]; exact hW
    let after := m.write t v hV
    after.readBytes t v.size (by rw [Memory.size_write]; exact hV) = v := by
  exact Memory.readBytes_write m t (m.readBytes s k hR) _

private theorem client_11 (m : Memory) :
    m.write (2^100 + 17) Bytes.empty (Or.inl Bytes.size_empty) = m :=
  Memory.write_empty m _

private theorem empty_inside (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
    (m.write s v h).readBytes (s + 1) 0 (Or.inl rfl) =
      m.readBytes (s + 1) 0 (Or.inl rfl) :=
  Memory.readBytes_write_disjoint m s v (s + 1) 0 h (Or.inl rfl) (Or.inl rfl)

private theorem empty_write_inside (m : Memory) (s t k : Nat)
    (hR : k = 0 ∨ t + k ≤ m.size) :
    (m.write s Bytes.empty (Or.inl Bytes.size_empty)).readBytes t k
      (by rw [Memory.size_write]; exact hR) = m.readBytes t k hR :=
  Memory.readBytes_write_disjoint m s Bytes.empty t k (Or.inl Bytes.size_empty) hR
    (Or.inr (Or.inl Bytes.size_empty))

private theorem both_empty (m : Memory) :
    (m.write (2^4096) Bytes.empty (Or.inl Bytes.size_empty)).readBytes (2^4096) 0
      (Or.inl rfl) = m.readBytes (2^4096) 0 (Or.inl rfl) :=
  Memory.readBytes_write_disjoint m _ Bytes.empty _ 0 (Or.inl Bytes.size_empty)
    (Or.inl rfl) (Or.inl rfl)

private theorem adjacent_before (m : Memory) (s : Nat) (v : Bytes) (t k : Nat)
    (hW : v.size = 0 ∨ s + v.size ≤ m.size)
    (hR : k = 0 ∨ t + k ≤ m.size) (h : t + k = s) :
    (m.write s v hW).readBytes t k (by rw [Memory.size_write]; exact hR) =
      m.readBytes t k hR :=
  Memory.readBytes_write_disjoint m s v t k hW hR (Or.inr (Or.inr (Or.inl (by omega))))

private theorem adjacent_after (m : Memory) (s : Nat) (v : Bytes) (t k : Nat)
    (hW : v.size = 0 ∨ s + v.size ≤ m.size)
    (hR : k = 0 ∨ t + k ≤ m.size) (h : s + v.size = t) :
    (m.write s v hW).readBytes t k (by rw [Memory.size_write]; exact hR) =
      m.readBytes t k hR :=
  Memory.readBytes_write_disjoint m s v t k hW hR (Or.inr (Or.inr (Or.inr (by omega))))

end STFSpec.Conformance.Vm.Core.MemoryCallerProofs
