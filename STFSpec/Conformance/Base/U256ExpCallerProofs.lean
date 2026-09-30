/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Modular U256 exponentiation caller proofs

Library `EthConformance`: fixed scripts through public observers/model laws only.
The examples use public operation laws and reference equality without unfolding
EXP, its reference, or word storage.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (a b : U256) : (U256.exp a b).toNat = a.toNat ^ b.toNat % 2 ^ 256 :=
  U256.toNat_exp a b

example (a : U256) : U256.exp a U256.zero = U256.one := U256.exp_zero a

example (a : U256) : U256.exp a U256.one = a := U256.exp_one a

example (b : U256) : U256.exp U256.one b = U256.one := U256.one_exp b

example (b : U256) (h : b.toNat ≠ 0) : U256.exp U256.zero b = U256.zero :=
  U256.zero_exp b h

example (a b : U256) : (U256.exp a b).toNat < 2 ^ 256 := U256.toNat_lt _

example (a b c d : U256) (hab : a.toNat = b.toNat) (hcd : c.toNat = d.toNat) :
    U256.exp a c = U256.exp b d := by
  apply U256.toNat_inj.mp
  rw [U256.toNat_exp, U256.toNat_exp, hab, hcd]

example (a b c d : U256) (h : a.toNat ^ b.toNat % 2 ^ 256 =
    c.toNat ^ d.toNat % 2 ^ 256) : U256.exp a b = U256.exp c d := by
  apply U256.toNat_inj.mp
  rw [U256.toNat_exp, U256.toNat_exp, h]

example (a b : U256) (h : a.toNat ^ b.toNat < 2 ^ 256) :
    (U256.exp a b).toNat = a.toNat ^ b.toNat := by
  rw [U256.toNat_exp, Nat.mod_eq_of_lt h]

example (a b : U256) : U256.ofNat? (a.toNat ^ b.toNat % 2 ^ 256) =
    some (U256.exp a b) := by
  apply (U256.ofNat?_eq_some_iff _ _).mpr
  exact ⟨by rw [← U256.toNat_exp]; exact U256.toNat_lt _, U256.toNat_exp a b⟩

example (a b c : U256) (h : b.toNat + c.toNat < 2 ^ 256) :
    U256.exp a (U256.add b c) = U256.mul (U256.exp a b) (U256.exp a c) := by
  apply U256.toNat_inj.mp
  rw [U256.toNat_exp, U256.toNat_add, Nat.mod_eq_of_lt h, Nat.pow_add,
    U256.toNat_mul, U256.toNat_exp, U256.toNat_exp]
  exact Nat.mul_mod _ _ _

example (a b : U256) : U256.exp a b = U256.expReference a b :=
  U256.exp_eq_reference a b
