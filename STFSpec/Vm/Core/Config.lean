/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.GasCosts

/-!
# Raw VM policy configuration data

Library `EthVmCore`. Core owns these data types;
EthFork owns actual values and configuration consistency. StateGasCosts holds four inputs;
the three state-gas amount observations are specified separately.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core

/-- Raw state-pricing inputs; EELS `src/ethereum/forks/amsterdam/vm/gas.py:56–59`.
The rate's Nat representation follows the existing public data contract. -/
structure StateGasCosts where
  /-- `StateGasCosts.COST_PER_STATE_BYTE`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/gas.py:56`.
  Interpreted by the existing Base rate wrapper. -/
  costPerStateByte : Nat
  /-- `StateGasCosts.STATE_BYTES_PER_NEW_ACCOUNT`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/gas.py:57`. Bytes associated with a new account. -/
  bytesPerNewAccount : Nat
  /-- `StateGasCosts.STATE_BYTES_PER_STORAGE_SET`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/gas.py:58`. Bytes associated with setting storage. -/
  bytesPerStorageSet : Nat
  /-- `StateGasCosts.STATE_BYTES_PER_AUTH_BASE`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/gas.py:59`.
  Bytes associated with a new authorization delegation. -/
  bytesPerAuthBase : Nat

/-- Equality of every stored projection determines the raw state-cost record. -/
theorem StateGasCosts.ext (a b : StateGasCosts)
    (h_costPerStateByte : a.costPerStateByte = b.costPerStateByte)
    (h_bytesPerNewAccount : a.bytesPerNewAccount = b.bytesPerNewAccount)
    (h_bytesPerStorageSet : a.bytesPerStorageSet = b.bytesPerStorageSet)
    (h_bytesPerAuthBase : a.bytesPerAuthBase = b.bytesPerAuthBase) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction uses all four stored projections in constructor order. -/
theorem StateGasCosts.eta (c : StateGasCosts) :
    StateGasCosts.mk c.costPerStateByte c.bytesPerNewAccount
      c.bytesPerStorageSet c.bytesPerAuthBase = c := by
  cases c
  rfl

/-- Raw VM-limit data; EELS `src/ethereum/forks/amsterdam/vm/interpreter.py:84–86`.
No raw-record equation changes the existing literal Stack/depth contract. -/
structure VmLimits where
  /-- `STACK_DEPTH_LIMIT`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/interpreter.py:84`.
  F8 specialization remains EthFork's obligation. -/
  stackDepthLimit : Nat
  /-- `MAX_CODE_SIZE`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/interpreter.py:85`. Maximum code-size data. -/
  maxCodeSize : Nat
  /-- `MAX_INIT_CODE_SIZE`; pinned EELS
  `src/ethereum/forks/amsterdam/vm/interpreter.py:86`.
  Maximum init-code-size data, independent in the raw record. -/
  maxInitCodeSize : Nat

/-- Equality of every stored projection determines the raw limits record. -/
theorem VmLimits.ext (a b : VmLimits)
    (h_stackDepthLimit : a.stackDepthLimit = b.stackDepthLimit)
    (h_maxCodeSize : a.maxCodeSize = b.maxCodeSize)
    (h_maxInitCodeSize : a.maxInitCodeSize = b.maxInitCodeSize) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction uses all three stored projections in constructor order. -/
theorem VmLimits.eta (c : VmLimits) :
    VmLimits.mk c.stackDepthLimit c.maxCodeSize c.maxInitCodeSize = c := by
  cases c
  rfl

/-- The existing B8 grouping of complete raw execution/state/limit records. -/
structure VmConfig where
  /-- Complete supplied execution-cost record, retaining its original domains. -/
  costs : GasCosts
  /-- Complete supplied four-input state-cost record. -/
  stateCosts : StateGasCosts
  /-- Complete supplied limits record. -/
  limits : VmLimits

/-- Actual whole-field equalities determine the complete configuration record. -/
theorem VmConfig.ext (a b : VmConfig)
    (h_costs : a.costs = b.costs)
    (h_stateCosts : a.stateCosts = b.stateCosts)
    (h_limits : a.limits = b.limits) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction retains each complete stored record. -/
theorem VmConfig.eta (c : VmConfig) :
    VmConfig.mk c.costs c.stateCosts c.limits = c := by
  cases c
  rfl

end STFSpec.Vm.Core
