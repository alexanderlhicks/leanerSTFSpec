/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Config

/-!
# Transaction EVM gas allocation

Library `EthVmCore`. Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1106–1152`.
The two source subtraction bounds are local proofs; raw records remain unrestricted.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7 (Q65).
-/

namespace STFSpec.Vm.Core

/-- Complete raw allocation, execution grant before state reservoir.
EELS `src/ethereum/forks/amsterdam/vm/gas.py:1106–1117` at the pin. -/
structure EvmGasAllocation where
  /-- Execution grant after intrinsic execution gas. -/
  executionGas : Nat
  /-- Remaining state reservoir. -/
  stateGasReservoir : Nat

/-- Equality of both stored coordinates determines the complete raw record. -/
theorem EvmGasAllocation.ext (a b : EvmGasAllocation)
    (h_executionGas : a.executionGas = b.executionGas)
    (h_stateGasReservoir : a.stateGasReservoir = b.stateGasReservoir) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction preserves both coordinates in constructor order. -/
theorem EvmGasAllocation.eta (allocation : EvmGasAllocation) :
    EvmGasAllocation.mk allocation.executionGas allocation.stateGasReservoir = allocation := by
  cases allocation
  rfl

/-- Source-ordered allocation on exactly the two local subtraction bounds.
EELS `src/ethereum/forks/amsterdam/vm/gas.py:1120–1152` at the pin. -/
def allocateEvmGas (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (_hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (_hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) : EvmGasAllocation :=
  let available := txGas - intrinsicExecution
  let executionGasBudget := cfg.costs.txMaxGasLimit - intrinsicExecution
  let executionGas := min executionGasBudget available
  { executionGas := executionGas
    stateGasReservoir := available - executionGas }

/-- Complete source-shaped allocation equation. -/
theorem allocateEvmGas_eq (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg txGas intrinsicExecution hIntrinsicLeTxGas hIntrinsicLeCap =
      (let available := txGas - intrinsicExecution
       let executionGas := min (cfg.costs.txMaxGasLimit - intrinsicExecution) available
       { executionGas := executionGas
         stateGasReservoir := available - executionGas } : EvmGasAllocation) := rfl

/-- Only the relevant cap is read; each call supplies its own local proofs. -/
theorem allocateEvmGas_congr (a b : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGasA : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCapA : intrinsicExecution ≤ a.costs.txMaxGasLimit)
    (hIntrinsicLeTxGasB : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCapB : intrinsicExecution ≤ b.costs.txMaxGasLimit)
    (hCap : a.costs.txMaxGasLimit = b.costs.txMaxGasLimit) :
    allocateEvmGas a txGas intrinsicExecution hIntrinsicLeTxGasA hIntrinsicLeCapA =
      allocateEvmGas b txGas intrinsicExecution hIntrinsicLeTxGasB hIntrinsicLeCapB := by
  rw [allocateEvmGas_eq, allocateEvmGas_eq, hCap]

end STFSpec.Vm.Core
