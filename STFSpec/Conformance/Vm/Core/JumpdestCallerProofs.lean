/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core

/-!
# Public-only jump-destination clients

Library `EthConformance`. These private clients consume all three ordinary equations
and existing Base laws without unfolding the scanner, bitmap or provider storage.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.JumpdestCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem ofList_nil : Bytes.ofList [] = Bytes.empty := by
  apply Bytes.ext
  rw [Bytes.toList_ofList, Bytes.toList_empty]

private theorem empty_arbitrary (i : Nat) :
    (validJumpDestinations Bytes.empty).contains i = false :=
  validJumpDestinations_contains_empty i

private theorem hit_lt (c : Bytes) (i : Nat)
    (hit : (validJumpDestinations c).contains i = true) : i < c.size := by
  by_cases hi : i < c.size
  · exact hi
  · have absent := validJumpDestinations_contains_of_size_le c i (by omega)
    rw [absent] at hit
    contradiction

private theorem huge_absent (c : Bytes) (h : c.size ≤ 2 ^ 4096) :
    (validJumpDestinations c).contains (2 ^ 4096) = false :=
  validJumpDestinations_contains_of_size_le c _ h

private theorem head (b : UInt8) (xs : List UInt8) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains 0 = (b == 0x5b) := by
  simpa using validJumpDestinations_contains_cons b xs 0

private theorem push_excluded (b : UInt8) (xs : List UInt8) (i : Nat)
    (hp : 96 ≤ b.toNat ∧ b.toNat ≤ 127) (h0 : 0 < i) (hi : i ≤ b.toNat - 95) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains i = false := by
  simpa [hp, Nat.ne_of_gt h0, hi] using
    validJumpDestinations_contains_cons b xs i

private theorem push_resumes (b : UInt8) (xs : List UInt8) (i : Nat)
    (hp : 96 ≤ b.toNat ∧ b.toNat ≤ 127) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains (i + (b.toNat - 95 + 1)) =
      (validJumpDestinations (Bytes.ofList (xs.drop (b.toNat - 95)))).contains i := by
  have h0 : i + (b.toNat - 95 + 1) ≠ 0 := by omega
  have hi : ¬ i + (b.toNat - 95 + 1) ≤ b.toNat - 95 := by omega
  simpa [hp, h0, hi] using
    validJumpDestinations_contains_cons b xs (i + (b.toNat - 95 + 1))

private theorem push_truncated (b : UInt8) (xs : List UInt8) (i : Nat)
    (hp : 96 ≤ b.toNat ∧ b.toNat ≤ 127) (hs : xs.length ≤ b.toNat - 95)
    (h0 : 0 < i) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains i = false := by
  have hd : xs.drop (b.toNat - 95) = [] := List.drop_eq_nil_iff.mpr hs
  simpa [hp, Nat.ne_of_gt h0, hd, ofList_nil, validJumpDestinations_contains_empty] using
    validJumpDestinations_contains_cons b xs i

private theorem nonpush_resumes (b : UInt8) (xs : List UInt8) (i : Nat)
    (hp : ¬ (96 ≤ b.toNat ∧ b.toNat ≤ 127)) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains (i + 1) =
      (validJumpDestinations (Bytes.ofList xs)).contains i := by
  have h0 : i + 1 ≠ 0 := by omega
  simpa [hp, h0] using validJumpDestinations_contains_cons b xs (i + 1)

private theorem push0_resumes (xs : List UInt8) (i : Nat) :
    (validJumpDestinations (Bytes.ofList (95 :: xs))).contains (i + 1) =
      (validJumpDestinations (Bytes.ofList xs)).contains i :=
  nonpush_resumes 95 xs i (by decide)

private theorem invalid_resumes (xs : List UInt8) (i : Nat) :
    (validJumpDestinations (Bytes.ofList (254 :: xs))).contains (i + 1) =
      (validJumpDestinations (Bytes.ofList xs)).contains i :=
  nonpush_resumes 254 xs i (by decide)

private theorem extended_resumes (b : UInt8) (xs : List UInt8) (i : Nat)
    (hb : b = 230 ∨ b = 231 ∨ b = 232) :
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains (i + 1) =
      (validJumpDestinations (Bytes.ofList xs)).contains i := by
  apply nonpush_resumes b xs i
  rcases hb with rfl | rfl | rfl <;> decide

private theorem hidden_jumpdest (xs : List UInt8) :
    (validJumpDestinations (Bytes.ofList (96 :: 91 :: xs))).contains 1 = false :=
  push_excluded 96 (91 :: xs) 1 (by decide) (by decide) (by decide)

private theorem hit_list (n : Nat) (xs : List UInt8) (hl : xs.length = n) (i : Nat)
    (hit : (validJumpDestinations (Bytes.ofList xs)).contains i = true) :
    xs[i]? = some (0x5b : UInt8) := by
  induction n using Nat.strongRecOn generalizing xs i with
  | ind n ih =>
    cases xs with
    | nil =>
      rw [ofList_nil, validJumpDestinations_contains_empty] at hit
      contradiction
    | cons b xs =>
      rw [validJumpDestinations_contains_cons] at hit
      let k := if 96 ≤ b.toNat ∧ b.toNat ≤ 127 then b.toNat - 95 else 0
      change (if i = 0 then b == (0x5b : UInt8) else if i ≤ k then false
        else (validJumpDestinations (Bytes.ofList (xs.drop k))).contains (i - (k + 1))) =
          true at hit
      by_cases h0 : i = 0
      · subst i
        have hb : b = (0x5b : UInt8) := by simpa using hit
        simp [hb]
      · rw [ite_eq_right h0] at hit
        by_cases hk : i ≤ k
        · simp [hk] at hit
        · rw [ite_eq_right hk] at hit
          have small : (xs.drop k).length < n := by
            simp only [List.length_cons] at hl
            rw [List.length_drop]
            omega
          have tailHit := ih _ small (xs.drop k) rfl (i - (k + 1)) hit
          rw [List.getElem?_drop] at tailHit
          cases i with
          | zero => contradiction
          | succ i =>
            have he : k + (i + 1 - (k + 1)) = i := by omega
            simpa only [he, List.getElem?_cons_succ] using tailHit

private theorem hit_byte (c : Bytes) (i : Nat)
    (hit : (validJumpDestinations c).contains i = true) :
    c[i]'(hit_lt c i hit) = (0x5b : UInt8) := by
  have h := hit_list c.toList.length c.toList rfl i (by
    rw [Bytes.ofList_toList]
    exact hit)
  have hi := hit_lt c i hit
  rw [List.getElem?_eq_getElem (by rw [Bytes.length_toList]; exact hi)] at h
  rw [Bytes.getElem_toList c i hi] at h
  exact Option.some.inj h

private theorem code_observation_congr (a b : Bytes) (h : a.toList = b.toList) (i : Nat) :
    (validJumpDestinations a).contains i = (validJumpDestinations b).contains i := by
  have he : a = b := Bytes.ext h
  rw [he]

end STFSpec.Conformance.Vm.Core.JumpdestCallerProofs
