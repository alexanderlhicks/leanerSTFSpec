/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256

/-!
# Transaction gas settlement

Library `EthVmCore`. Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1157–1243`.
Exactly three local bounds justify the source subtractions; the raw result is unrestricted.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7 (Q66).
-/

namespace STFSpec.Vm.Core

open STFSpec.Base

/-- Complete raw sender and block gas observations, in source constructor order. -/
structure TransactionGasSettlement where
  /-- Sender gas used after capped refund and calldata floor. -/
  gasUsed : Nat
  /-- Gas returned to the sender. -/
  gasLeft : Nat
  /-- Pre-refund execution gas used, with its independent floor. -/
  executionGasUsed : Nat
  /-- Nonnegative part of signed transaction state usage. -/
  stateGasUsed : Nat

/-- All four observations determine the complete raw result. -/
theorem TransactionGasSettlement.ext (a b : TransactionGasSettlement)
    (hUsed : a.gasUsed = b.gasUsed) (hLeft : a.gasLeft = b.gasLeft)
    (hExecution : a.executionGasUsed = b.executionGasUsed)
    (hState : a.stateGasUsed = b.stateGasUsed) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction retains every coordinate in constructor order. -/
theorem TransactionGasSettlement.eta (a : TransactionGasSettlement) :
    TransactionGasSettlement.mk a.gasUsed a.gasLeft
      a.executionGasUsed a.stateGasUsed = a := by
  cases a
  rfl

/-- Source-ordered pure settlement; EELS `gas.py:1178–1243` at the pin.
The refund is already an unsigned word; its upstream checked conversion is caller-owned. -/
def settleTransactionGas
    (txGas calldataFloor gasLeft stateGasLeft : Nat)
    (refund : U256) (stateGasUsed : Int)
    (_hReturned : gasLeft + stateGasLeft ≤ txGas)
    (_hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
    (_hFloor : calldataFloor ≤ txGas) : TransactionGasSettlement :=
  let p := txGas - gasLeft - stateGasLeft
  let c := min (p / 5) refund.toNat
  let postRefund := p - c
  let gasUsed := max postRefund calldataFloor
  let stateUsed := stateGasUsed.toNat
  let executionUsed := max (p - stateUsed) calldataFloor
  { gasUsed := gasUsed
    gasLeft := txGas - gasUsed
    executionGasUsed := executionUsed
    stateGasUsed := stateUsed }

section
variable (txGas calldataFloor gasLeft stateGasLeft : Nat)
variable (refund : U256) (stateGasUsed : Int)
variable (hReturned : gasLeft + stateGasLeft ≤ txGas)
variable (hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
variable (hFloor : calldataFloor ≤ txGas)

/-- Complete sender and pre-refund block observations on the local success domain. -/
theorem settleTransactionGas_eq :
    settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor =
    let p := txGas - gasLeft - stateGasLeft
    let c := min (p / 5) refund.toNat
    { gasUsed := max (p - c) calldataFloor
      gasLeft := txGas - max (p - c) calldataFloor
      executionGasUsed := max (p - stateGasUsed.toNat) calldataFloor
      stateGasUsed := stateGasUsed.toNat } := rfl

/-- Sender gas usage never exceeds the supplied transaction gas. -/
theorem settleTransactionGas_gasUsed_le :
    (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor).gasUsed ≤ txGas := by
  rw [settleTransactionGas_eq]
  exact Nat.max_le.mpr ⟨(Nat.le_trans (Nat.sub_le _ _)
    (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))), hFloor⟩

/-- The execution dimension independently includes the calldata floor. -/
theorem settleTransactionGas_executionGasUsed_ge_floor :
    calldataFloor ≤
      (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
        hReturned hState hFloor).executionGasUsed := by
  rw [settleTransactionGas_eq]
  exact Nat.le_max_right _ _

end
end STFSpec.Vm.Core
