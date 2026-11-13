/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockState
import STFSpec.State.TxRevertible
import STFSpec.State.TxObs
import STFSpec.State.StateError
import Init.Control.State

/-!
# Raw transaction state and state monad

Library `EthState`: the guided D22/D23 partition into complete block, revertible and
observation values, with the §5 transformer order and hash-only code observations.
This is nominal assembly;
tracker operations, initialization, lifetimes and source refinement remain separate.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7/10.
-/

namespace STFSpec.State

/-- Raw D22/D23 assembly of EELS `src/ethereum/forks/amsterdam/state_tracker.py:78–104`.
`block` represents the source parent; the other fields partition transaction data.
Every complete supplied provider value is retained without a class or validity premise.
Source refinement and tracker lifetimes remain separate. -/
structure TxState (m : Type → Type) where
  /-- Complete supplied block context. -/
  block : BlockState m
  /-- Complete supplied revertible data, including raw order indexes and transient writes. -/
  rev : TxRevertible
  /-- Complete supplied observations and created-account set. -/
  obs : TxObs

/-- State and typed-error transformer wiring from EthState §5.
Running yields `m (Except StateError (α × TxState m))`: failure returns no transaction
state. This alias alone supplies no tracker rollback or interpretation of underlying effects. -/
abbrev StateM (m : Type → Type) := StateT (TxState m) (ExceptT StateError m)

end STFSpec.State
