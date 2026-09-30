/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256

/-!
# Unsigned U256 arithmetic

Library `EthBase`: wrapping EVM arithmetic, unsigned division/remainder, modular
arithmetic with unbounded intermediates, and checked Python-operator arithmetic.
Inputs follow EELS pop order. These primitives have no stack, gas or frame effects;
`EthVmInstructions` owns those effects and consumers own checked-failure projection.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
EELS citations are at the commit in `reference.toml`.
Dependency citations follow the convention in EthBase §3.
Signed division/remainder are defined in `STFSpec.Base.U256Signed`.
-/

namespace STFSpec.Base.U256

/-- Wrapping addition; EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:28`,
`ethereum_types/numeric.py:614` (`wrapping_add`). -/
def add (a b : U256) : U256 := ofBitVec (a.toBitVec + b.toBitVec)

/-- Wrapping subtraction, first operand minus second;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:55`,
`ethereum_types/numeric.py:625` (`wrapping_sub`). -/
def sub (a b : U256) : U256 := ofBitVec (a.toBitVec - b.toBitVec)

/-- Wrapping multiplication;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:82`,
`ethereum_types/numeric.py:636` (`wrapping_mul`). -/
def mul (a b : U256) : U256 := ofBitVec (a.toBitVec * b.toBitVec)

/-- Unsigned EVM division returns zero for a zero divisor;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:109`. -/
def div (a b : U256) : U256 :=
  if b.toNat = 0 then zero else ofNat (a.toNat / b.toNat)

/-- Unsigned EVM remainder returns zero for a zero divisor;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:175`. -/
def mod (a b : U256) : U256 :=
  if b.toNat = 0 then zero else ofNat (a.toNat % b.toNat)

/-- Modular addition uses an unbounded sum before reduction, returning zero for modulus zero;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:235`. -/
def addmod (a b n : U256) : U256 :=
  if n.toNat = 0 then zero else ofNat ((a.toNat + b.toNat) % n.toNat)

/-- Modular multiplication uses an unbounded product before reduction, returning zero
for modulus zero; EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:266`. -/
def mulmod (a b n : U256) : U256 :=
  if n.toNat = 0 then zero else ofNat ((a.toNat * b.toNat) % n.toNat)

/-- Checked Python addition; `ethereum_types/numeric.py:91,44,611`.
Unsigned overflow returns `none`; the caller maps it to its enclosing EELS handler's error (D14). -/
def checkedAdd (a b : U256) : Option U256 := ofNat? (a.toNat + b.toNat)

/-- Checked Python subtraction; `ethereum_types/numeric.py:103`.
Returns `none` exactly when the second unsigned value exceeds the first. -/
def checkedSub (a b : U256) : Option U256 :=
  if b.toNat ≤ a.toNat then some (ofNat (a.toNat - b.toNat)) else none

/-- Checked Python multiplication; `ethereum_types/numeric.py:131,44,611`.
Unsigned overflow returns `none`. -/
def checkedMul (a b : U256) : Option U256 := ofNat? (a.toNat * b.toNat)

/-- Checked Python floor division; `ethereum_types/numeric.py:158`.
Zero division returns `none`; every nonzero-divisor quotient fits in a word. -/
def checkedDiv (a b : U256) : Option U256 :=
  if b.toNat = 0 then none else some (div a b)

/-- Checked Python remainder; `ethereum_types/numeric.py:178`.
Zero division returns `none`; every nonzero-divisor remainder fits in a word. -/
def checkedMod (a b : U256) : Option U256 :=
  if b.toNat = 0 then none else some (mod a b)

/-! ### EVM model equations -/

/-- Wrapping addition commutes with the bit-vector model. -/
theorem toBitVec_add (a b : U256) : (add a b).toBitVec = a.toBitVec + b.toBitVec :=
  toBitVec_ofBitVec _

/-- Wrapping subtraction commutes with the bit-vector model. -/
theorem toBitVec_sub (a b : U256) : (sub a b).toBitVec = a.toBitVec - b.toBitVec :=
  toBitVec_ofBitVec _

/-- Wrapping multiplication commutes with the bit-vector model. -/
theorem toBitVec_mul (a b : U256) : (mul a b).toBitVec = a.toBitVec * b.toBitVec :=
  toBitVec_ofBitVec _

/-- Unsigned addition reduces its unbounded sum modulo 2²⁵⁶. -/
theorem toNat_add (a b : U256) : (add a b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  rw [toNat_def, toBitVec_add, BitVec.toNat_add]
  rfl

/-- Word addition retains the sum when it is below the word modulus. -/
theorem toNat_add_of_lt (a b : U256) (h : a.toNat + b.toNat < 2 ^ 256) :
    (add a b).toNat = a.toNat + b.toNat := by
  rw [toNat_add, Nat.mod_eq_of_lt h]

/-- Unsigned subtraction is `(2²⁵⁶ − b.toNat + a.toNat) mod 2²⁵⁶`. -/
theorem toNat_sub (a b : U256) :
    (sub a b).toNat = (2 ^ 256 - b.toNat + a.toNat) % 2 ^ 256 := by
  rw [toNat_def, toBitVec_sub, BitVec.toNat_sub]
  rfl

/-- Unsigned multiplication reduces its unbounded product modulo 2²⁵⁶. -/
theorem toNat_mul (a b : U256) : (mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  rw [toNat_def, toBitVec_mul, BitVec.toNat_mul]
  rfl

/-- EVM unsigned division has the explicit zero-divisor branch. -/
theorem toNat_div (a b : U256) :
    (div a b).toNat = if b.toNat = 0 then 0 else a.toNat / b.toNat := by
  unfold div
  split
  · exact toNat_zero
  · apply toNat_ofNat_of_lt
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (toNat_lt a)

/-- EVM unsigned remainder has the explicit zero-divisor branch. -/
theorem toNat_mod (a b : U256) :
    (mod a b).toNat = if b.toNat = 0 then 0 else a.toNat % b.toNat := by
  unfold mod
  split
  · exact toNat_zero
  next h =>
    apply toNat_ofNat_of_lt
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) (toNat_lt b)

/-- ADDMOD reduces the unbounded sum, without a word-sized intermediate. -/
theorem toNat_addmod (a b n : U256) :
    (addmod a b n).toNat = if n.toNat = 0 then 0 else
      (a.toNat + b.toNat) % n.toNat := by
  unfold addmod
  split
  · exact toNat_zero
  next h =>
    apply toNat_ofNat_of_lt
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) (toNat_lt n)

/-- MULMOD reduces the unbounded product, without a word-sized intermediate. -/
theorem toNat_mulmod (a b n : U256) :
    (mulmod a b n).toNat = if n.toNat = 0 then 0 else
      (a.toNat * b.toNat) % n.toNat := by
  unfold mulmod
  split
  · exact toNat_zero
  next h =>
    apply toNat_ofNat_of_lt
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) (toNat_lt n)

/-! ### Checked model equations -/

/-- Checked addition succeeds exactly when the unreduced sum fits. -/
theorem checkedAdd_eq_some_iff (a b c : U256) :
    checkedAdd a b = some c ↔ a.toNat + b.toNat < 2 ^ 256 ∧
      c.toNat = a.toNat + b.toNat := ofNat?_eq_some_iff _ _

/-- Checked addition fails exactly on unsigned overflow. -/
theorem checkedAdd_eq_none_iff (a b : U256) :
    checkedAdd a b = none ↔ 2 ^ 256 ≤ a.toNat + b.toNat := ofNat?_eq_none_iff _

/-- Checked multiplication succeeds exactly when the unreduced product fits. -/
theorem checkedMul_eq_some_iff (a b c : U256) :
    checkedMul a b = some c ↔ a.toNat * b.toNat < 2 ^ 256 ∧
      c.toNat = a.toNat * b.toNat := ofNat?_eq_some_iff _ _

/-- Checked multiplication fails exactly on unsigned overflow. -/
theorem checkedMul_eq_none_iff (a b : U256) :
    checkedMul a b = none ↔ 2 ^ 256 ≤ a.toNat * b.toNat := ofNat?_eq_none_iff _

/-- Checked subtraction succeeds exactly without underflow, retaining the difference. -/
theorem checkedSub_eq_some_iff (a b c : U256) :
    checkedSub a b = some c ↔ b.toNat ≤ a.toNat ∧ c.toNat = a.toNat - b.toNat := by
  unfold checkedSub
  split
  next h =>
    have hr : a.toNat - b.toNat < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (toNat_lt a)
    simp only [Option.some.injEq, ← toNat_inj, toNat_ofNat_of_lt hr, h, true_and,
      eq_comm]
  next h => simp [h]

/-- Checked subtraction fails exactly on underflow. -/
theorem checkedSub_eq_none_iff (a b : U256) :
    checkedSub a b = none ↔ a.toNat < b.toNat := by
  simp [checkedSub, Nat.not_le]

/-- Checked division succeeds exactly for a nonzero divisor, retaining the quotient. -/
theorem checkedDiv_eq_some_iff (a b c : U256) :
    checkedDiv a b = some c ↔ b.toNat ≠ 0 ∧ c.toNat = a.toNat / b.toNat := by
  unfold checkedDiv
  split
  next h => simp [h]
  next h =>
    have hm : (div a b).toNat = a.toNat / b.toNat := by
      simp only [toNat_div, h, ite_false]
    simp only [Option.some.injEq, ← toNat_inj, hm, ne_eq, h, not_false_eq_true, true_and, eq_comm]

/-- Checked division fails exactly on zero division, never on quotient overflow. -/
theorem checkedDiv_eq_none_iff (a b : U256) : checkedDiv a b = none ↔ b.toNat = 0 := by
  simp [checkedDiv]

/-- Checked remainder succeeds exactly for a nonzero divisor, retaining the remainder. -/
theorem checkedMod_eq_some_iff (a b c : U256) :
    checkedMod a b = some c ↔ b.toNat ≠ 0 ∧ c.toNat = a.toNat % b.toNat := by
  unfold checkedMod
  split
  next h => simp [h]
  next h =>
    have hm : (mod a b).toNat = a.toNat % b.toNat := by
      simp only [toNat_mod, h, ite_false]
    simp only [Option.some.injEq, ← toNat_inj, hm, ne_eq, h, not_false_eq_true, true_and, eq_comm]

/-- Checked remainder fails exactly on zero division, never on remainder overflow. -/
theorem checkedMod_eq_none_iff (a b : U256) : checkedMod a b = none ↔ b.toNat = 0 := by
  simp [checkedMod]

/-! ### Derived modular algebra -/

/-- Word addition is commutative. -/
theorem add_comm (a b : U256) : add a b = add b a := by
  apply ext
  simp only [toBitVec_add]
  exact BitVec.add_comm _ _

/-- Word addition is associative. -/
theorem add_assoc (a b c : U256) : add (add a b) c = add a (add b c) := by
  apply ext
  simp only [toBitVec_add]
  exact BitVec.add_assoc _ _ _

/-- Zero is a right additive identity. -/
theorem add_zero (a : U256) : add a zero = a := by
  apply ext
  simp only [toBitVec_add, toBitVec_zero, BitVec.add_zero]

/-- Zero is a left additive identity. -/
theorem zero_add (a : U256) : add zero a = a := by
  rw [add_comm, add_zero]

/-- Word multiplication is commutative. -/
theorem mul_comm (a b : U256) : mul a b = mul b a := by
  apply ext
  simp only [toBitVec_mul]
  exact BitVec.mul_comm _ _

/-- Word multiplication is associative. -/
theorem mul_assoc (a b c : U256) : mul (mul a b) c = mul a (mul b c) := by
  apply ext
  simp only [toBitVec_mul]
  exact BitVec.mul_assoc _ _ _

/-- One is a right multiplicative identity. -/
theorem mul_one (a : U256) : mul a one = a := by
  apply ext
  simp only [toBitVec_mul, toBitVec_one, BitVec.mul_one]

/-- One is a left multiplicative identity. -/
theorem one_mul (a : U256) : mul one a = a := by
  rw [mul_comm, mul_one]

/-- Multiplication by zero on the right yields zero. -/
theorem mul_zero (a : U256) : mul a zero = zero := by
  apply ext
  simp only [toBitVec_mul, toBitVec_zero, BitVec.mul_zero]

/-- Multiplication by zero on the left yields zero. -/
theorem zero_mul (a : U256) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

/-- Multiplication distributes over addition on the left. -/
theorem mul_add (a b c : U256) : mul a (add b c) = add (mul a b) (mul a c) := by
  apply ext
  simp only [toBitVec_mul, toBitVec_add]
  exact BitVec.mul_add

/-- Multiplication distributes over addition on the right. -/
theorem add_mul (a b c : U256) : mul (add a b) c = add (mul a c) (mul b c) := by
  apply ext
  simp only [toBitVec_mul, toBitVec_add]
  exact BitVec.add_mul

/-- Modular subtraction is addition of the additive inverse, expressed as `sub zero b`. -/
theorem sub_eq_add_sub_zero (a b : U256) : sub a b = add a (sub zero b) := by
  apply ext
  simp only [toBitVec_sub, toBitVec_add, toBitVec_zero, BitVec.zero_sub]
  exact BitVec.sub_eq_add_neg _ _

/-- Adding the modular additive inverse yields zero. -/
theorem add_sub_zero (a : U256) : add a (sub zero a) = zero := by
  apply ext
  simp only [toBitVec_add, toBitVec_sub, toBitVec_zero, BitVec.zero_sub,
    BitVec.add_right_neg]

/-- Subtracting a value from itself yields zero. -/
theorem sub_self (a : U256) : sub a a = zero := by
  apply ext
  simp only [toBitVec_sub, toBitVec_zero, BitVec.sub_self]

/-- Subtracting the second summand cancels it even across overflow. -/
theorem add_sub_cancel (a b : U256) : sub (add a b) b = a := by
  apply ext
  simp only [toBitVec_sub, toBitVec_add]
  exact BitVec.add_sub_cancel _ _

/-- Adding back the subtrahend cancels modular subtraction even across underflow. -/
theorem sub_add_cancel (a b : U256) : add (sub a b) b = a := by
  apply ext
  simp only [toBitVec_sub, toBitVec_add]
  exact BitVec.sub_add_cancel _ _

/-- With a nonzero divisor, quotient and remainder decompose the unsigned value exactly,
using an unbounded product and sum. -/
theorem toNat_div_add_toNat_mod (a b : U256) (h : b.toNat ≠ 0) :
    b.toNat * (div a b).toNat + (mod a b).toNat = a.toNat := by
  simp only [toNat_div, toNat_mod, h, ite_false]
  exact Nat.div_add_mod _ _

/-- Quotient and remainder also reconstruct the word through its wrapping operations;
the natural decomposition ensures no reduction changes the final result. -/
theorem div_add_mod (a b : U256) (h : b.toNat ≠ 0) :
    add (mul b (div a b)) (mod a b) = a := by
  apply toNat_inj.mp
  have hd := toNat_div_add_toNat_mod a b h
  have hp : b.toNat * (div a b).toNat < 2 ^ 256 := by
    have hr := toNat_lt a
    omega
  rw [toNat_add, toNat_mul, Nat.mod_eq_of_lt hp, hd, Nat.mod_eq_of_lt (toNat_lt a)]

/-- For a nonzero modulus, ADDMOD returns a value strictly below that modulus. -/
theorem addmod_lt (a b n : U256) (h : n.toNat ≠ 0) : (addmod a b n).toNat < n.toNat := by
  simp only [toNat_addmod, h, ite_false]
  exact Nat.mod_lt _ (by omega)

/-- For a nonzero modulus, MULMOD returns a value strictly below that modulus. -/
theorem mulmod_lt (a b n : U256) (h : n.toNat ≠ 0) : (mulmod a b n).toNat < n.toNat := by
  simp only [toNat_mulmod, h, ite_false]
  exact Nat.mod_lt _ (by omega)

/-- With a nonzero divisor, the EVM remainder is strictly less than the divisor. -/
theorem mod_lt (a b : U256) (h : b.toNat ≠ 0) : (mod a b).toNat < b.toNat := by
  simp only [toNat_mod, h, ite_false]
  exact Nat.mod_lt _ (by omega)

/-- EVM division by zero returns the zero word. -/
theorem div_zero (a : U256) : div a zero = zero := by
  apply toNat_inj.mp
  simp only [toNat_div, toNat_zero, ite_true]

/-- EVM remainder by zero returns the zero word, unlike `Nat.mod` and `BitVec` remainder. -/
theorem mod_zero (a : U256) : mod a zero = zero := by
  apply toNat_inj.mp
  simp only [toNat_mod, toNat_zero, ite_true]

end STFSpec.Base.U256
