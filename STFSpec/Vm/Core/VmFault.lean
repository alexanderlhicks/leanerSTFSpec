/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.StateError

/-!
# Nominal VM fault carriers

Library `EthVmCore`: named non-frame fault values with complete supplied payloads.
These carriers implement no fault producer, propagation adapter or outcome projection.
Failure-ledger classification and freezing remain separate obligations (B14).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.6/5/10.
-/

namespace STFSpec.Vm.Core

/-- The two supplied VM-local unsigned conversion sites (R-EXC-2). -/
inductive OverflowSite where
  /-- The BLOBBASEFEE price conversion; the actual check remains unimplemented. -/
  | blobBaseFee
  /-- A top-level refund-counter conversion; the actual checks remain unimplemented. -/
  | refundCounter

/-- Nominal non-frame faults, distinct from exceptional halts and internal failures. -/
inductive VmFault where
  /-- Retain the complete supplied state failure, including any nested witness error. -/
  | state (e : STFSpec.State.StateError)
  /-- Retain the raw supplied ancestor offset, without an admissibility premise. -/
  | ancestorHashUnavailable (offset : Nat)
  /-- Retain the supplied unsigned conversion site. -/
  | u256Overflow (site : OverflowSite)

end STFSpec.Vm.Core
