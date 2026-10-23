/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256

/-!
# Local transaction gas settlement

Library `EthVmCore`. Pure sender and pre-refund block accounting on exactly the
three local source-subtraction bounds, with a validated U256 refund (Q66).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Complete gas figures; pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1157–1175`.
Raw records admit arbitrary Nat fields independently of produced settlements. -/
structure TransactionGasSettlement where
  /-- Sender charge, `gas.py:1166` at the pin. -/
  gasUsed : Nat
  /-- Sender return, `gas.py:1169` at the pin. -/
  gasLeft : Nat
  /-- Pre-refund execution dimension, `gas.py:1172` at the pin. -/
  executionGasUsed : Nat
  /-- Nonnegative state dimension, `gas.py:1175` at the pin. -/
  stateGasUsed : Nat

/-- Equality of all four complete projections determines the raw result. -/
theorem TransactionGasSettlement.ext (a b : TransactionGasSettlement)
    (hUsed : a.gasUsed = b.gasUsed) (hLeft : a.gasLeft = b.gasLeft)
    (hExecution : a.executionGasUsed = b.executionGasUsed)
    (hState : a.stateGasUsed = b.stateGasUsed) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruct every result field in source constructor order. -/
theorem TransactionGasSettlement.eta (a : TransactionGasSettlement) :
    TransactionGasSettlement.mk a.gasUsed a.gasLeft
      a.executionGasUsed a.stateGasUsed = a := by
  cases a
  rfl

/-- Settle without fees or block mutation; pinned EELS
`src/ethereum/forks/amsterdam/vm/gas.py:1178–1242`.
The three proofs protect the ordered source subtractions; refund conversion is upstream. -/
def settleTransactionGas
    (txGas calldataFloor gasLeft stateGasLeft : Nat)
    (refund : U256) (stateGasUsed : Int)
    (_hReturned : gasLeft + stateGasLeft ≤ txGas)
    (_hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
    (_hFloor : calldataFloor ≤ txGas) : TransactionGasSettlement :=
  let preRefund := txGas - gasLeft - stateGasLeft
  let cappedRefund := min (preRefund / 5) refund.toNat
  let postRefund := preRefund - cappedRefund
  let used := max postRefund calldataFloor
  let stateUsed := stateGasUsed.toNat
  let executionUsed := max (preRefund - stateUsed) calldataFloor
  { gasUsed := used
    gasLeft := txGas - used
    executionGasUsed := executionUsed
    stateGasUsed := stateUsed }

section
variable (txGas calldataFloor gasLeft stateGasLeft : Nat)
variable (refund : U256) (stateGasUsed : Int)
variable (hReturned : gasLeft + stateGasLeft ≤ txGas)
variable (hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
variable (hFloor : calldataFloor ≤ txGas)

/-- Complete source-ordered equation on the three local arithmetic bounds. -/
theorem settleTransactionGas_eq :
    settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor =
    let p := txGas - gasLeft - stateGasLeft
    let c := min (p / 5) refund.toNat
    { gasUsed := max (p - c) calldataFloor
      gasLeft := txGas - max (p - c) calldataFloor
      executionGasUsed := max (p - stateGasUsed.toNat) calldataFloor
      stateGasUsed := stateGasUsed.toNat } := rfl

/-- The sender charge stays within the supplied transaction gas. -/
theorem settleTransactionGas_gasUsed_le :
    (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor).gasUsed ≤ txGas := by
  rw [settleTransactionGas_eq]
  dsimp only
  omega

/-- The execution block dimension carries the calldata floor. -/
theorem settleTransactionGas_executionGasUsed_ge_floor :
    calldataFloor ≤
      (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
        hReturned hState hFloor).executionGasUsed := by
  rw [settleTransactionGas_eq]
  exact Nat.le_max_right _ _

end
end STFSpec.Vm.Core
