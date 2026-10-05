/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Nominal witness-error carriers

Library `EthState`: commitment-agnostic items and coarse errors supplied to provider actions.
These constructors implement no backend, diagnostic adapter, outcome projection or error freeze.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§5/10.
-/

namespace STFSpec.State

open Base

/-- Commitment-agnostic witness item; the constructor retains its complete supplied payload. -/
inductive WitnessItem where
  /-- A node identified by its supplied hash. -/
  | node (h : Hash32)
  /-- Code identified by its supplied hash. -/
  | code (h : Hash32)
  /-- A leaf item, without an additional diagnostic payload. -/
  | leaf

/-- Current coarse witness errors; site-specific refinement and adapters remain open. -/
inductive WitnessError where
  /-- The supplied witness item is missing. -/
  | missing (what : WitnessItem)
  /-- The supplied witness item is malformed. -/
  | malformed (what : WitnessItem)
  /-- The supplied hash identifies an unresolved reference. -/
  | unresolved (h : Hash32)

end STFSpec.State
