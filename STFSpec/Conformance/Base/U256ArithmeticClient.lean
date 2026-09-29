/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Unsigned U256 arithmetic client proof tests

Library `EthConformance`: fixed caller proofs use only public observer and operation
laws. No stored fields, operation definitions or BitVec instances are unfolded.
These extend the baseline caller scripts for REVIEW §7 R4; full replacement and
opcode-loop measurements remain open.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (a b : U256) : U256.add a b = U256.add b a := U256.add_comm a b

example (a b c : U256) : U256.add (U256.add a b) c = U256.add a (U256.add b c) :=
  U256.add_assoc a b c

example (a b : U256) : U256.add (U256.sub a b) b = a := U256.sub_add_cancel a b

example (a b : U256) : U256.sub (U256.add a b) b = a := U256.add_sub_cancel a b

example (a b c : U256) :
    U256.mul a (U256.add b c) = U256.add (U256.mul a b) (U256.mul a c) :=
  U256.mul_add a b c

example (a b : U256) (h : b.toNat ≠ 0) :
    U256.add (U256.mul b (U256.div a b)) (U256.mod a b) = a := U256.div_mod_eq a b h

example (a b : U256) (h : b.toNat ≠ 0) : (U256.mod a b).toNat < b.toNat :=
  U256.mod_lt a b h

example (a b n : U256) (h : n.toNat ≠ 0) : (U256.addmod a b n).toNat < n.toNat :=
  U256.addmod_lt a b n h

example (a b n : U256) (h : n.toNat ≠ 0) : (U256.mulmod a b n).toNat < n.toNat :=
  U256.mulmod_lt a b n h

example (a : U256) : U256.div a U256.zero = U256.zero := U256.div_zero a

example (a : U256) : U256.mod a U256.zero = U256.zero := U256.mod_zero a

example (a b c : U256) (h : U256.checkedAdd a b = some c) :
    c.toNat = a.toNat + b.toNat := ((U256.checkedAdd_eq_some_iff a b c).mp h).2

example (a b : U256) (h : a.toNat < b.toNat) : U256.checkedSub a b = none :=
  (U256.checkedSub_eq_none_iff a b).mpr h

example (a b c : U256) (h : U256.checkedSub a b = some c) : b.toNat ≤ a.toNat :=
  ((U256.checkedSub_eq_some_iff a b c).mp h).1

example (a b c : U256) (h : U256.checkedMul a b = some c) :
    c.toNat = a.toNat * b.toNat := ((U256.checkedMul_eq_some_iff a b c).mp h).2

example (a b c : U256) (h : U256.checkedDiv a b = some c) : b.toNat ≠ 0 :=
  ((U256.checkedDiv_eq_some_iff a b c).mp h).1

example (a b c : U256) (h : U256.checkedMod a b = some c) : c.toNat = a.toNat % b.toNat :=
  ((U256.checkedMod_eq_some_iff a b c).mp h).2
