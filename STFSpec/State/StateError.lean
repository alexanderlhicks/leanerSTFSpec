/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.WitnessError

/-!
# Nominal state-error carrier

Library `EthState`: the four supplied error variants specified by R29.
Construction and elimination implement no tracker operation, forwarding adapter or outcome
projection. The failure-ledger and freezing obligations remain open.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§5/10.
-/

namespace STFSpec.State

/-- Nominal state failures; operation semantics and error freezing remain separate obligations. -/
inductive StateError where
  /-- Retain the complete supplied witness error. -/
  | witness (e : WitnessError)
  /-- Insufficient balance for a future state operation (R29). -/
  | balanceUnderflow
  /-- Balance overflow in a future state operation (R29). -/
  | balanceOverflow
  /-- A future storage write targets a missing account (R29). -/
  | storageOnMissingAccount

end STFSpec.State
