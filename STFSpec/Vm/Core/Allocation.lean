/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Config

/-!
# Local EVM gas allocation

Library `EthVmCore`. Pure allocation from transaction and intrinsic execution
gas, with exactly the two local source-subtraction bounds (Q65).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core

/-- Complete allocation; pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1108–1117`.
Raw records admit arbitrary Nat fields independently of produced allocations. -/
structure EvmGasAllocation where
  /-- `execution_gas` at pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1113`. -/
  executionGas : Nat
  /-- `state_gas_reservoir` at pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:1116`. -/
  stateGasReservoir : Nat

/-- Equality of both complete projections determines the raw result. -/
theorem EvmGasAllocation.ext (a b : EvmGasAllocation)
    (h_executionGas : a.executionGas = b.executionGas)
    (h_stateGasReservoir : a.stateGasReservoir = b.stateGasReservoir) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruct the result in source constructor order. -/
theorem EvmGasAllocation.eta (allocation : EvmGasAllocation) :
    EvmGasAllocation.mk allocation.executionGas allocation.stateGasReservoir = allocation := by
  cases allocation
  rfl

/-- Allocate without charging a meter; pinned EELS
`src/ethereum/forks/amsterdam/vm/gas.py:1120–1152`.
The two local proofs protect the source's ordered checked subtractions. -/
def allocateEvmGas (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (_hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (_hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) :
    EvmGasAllocation :=
  let available := txGas - intrinsicExecution
  let executionGas := min (cfg.costs.txMaxGasLimit - intrinsicExecution) available
  { executionGas := executionGas
    stateGasReservoir := available - executionGas }

/-- Complete source-ordered allocation equation on the two local bounds. -/
theorem allocateEvmGas_eq (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg txGas intrinsicExecution hIntrinsicLeTxGas hIntrinsicLeCap =
      (let available := txGas - intrinsicExecution
       let executionGas := min (cfg.costs.txMaxGasLimit - intrinsicExecution) available
       { executionGas := executionGas
         stateGasReservoir := available - executionGas } : EvmGasAllocation) := rfl

/-- Equal relevant caps preserve the complete result for independently admitted calls. -/
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
