/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U64

/-!
# Raw block-gas counters

Library `EthVmCore`. These are the three VM-visible projections of the pinned
`BlockOutput`; EthBlock owns the full output record (D27/R-ENV-4).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core

/-- Raw gas-counter projections of EELS `BlockOutput`,
`src/ethereum/forks/amsterdam/vm/__init__.py:72–120` at the pin.
All Nat/Nat/U64 records are admitted; no block-capacity premise is imposed. -/
structure BlockGasCounters where
  /-- Execution usage, `block_gas_used` at pinned EELS
  `src/ethereum/forks/amsterdam/vm/__init__.py:104`. -/
  blockGasUsed : Nat
  /-- State usage, `block_state_gas_used` at pinned EELS
  `src/ethereum/forks/amsterdam/vm/__init__.py:105`. -/
  blockStateGasUsed : Nat
  /-- Blob usage, `blob_gas_used` at pinned EELS
  `src/ethereum/forks/amsterdam/vm/__init__.py:118`. -/
  blobGasUsed : STFSpec.Base.U64

/-- Equality of all three projections determines the complete raw counter record. -/
theorem BlockGasCounters.ext (a b : BlockGasCounters)
    (hExecution : a.blockGasUsed = b.blockGasUsed)
    (hState : a.blockStateGasUsed = b.blockStateGasUsed)
    (hBlob : a.blobGasUsed = b.blobGasUsed) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruction retains execution, state and blob usage in constructor order. -/
theorem BlockGasCounters.eta (c : BlockGasCounters) :
    BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed c.blobGasUsed = c := by
  cases c
  rfl

end STFSpec.Vm.Core
