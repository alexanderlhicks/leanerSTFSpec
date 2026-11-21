/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

namespace STFSpec.Conformance.State.TransientStorageCallerProofs

open STFSpec.Base STFSpec.State

private def exactType :
    {m : Type → Type} → [Monad m] → Address → Bytes32 → STFSpec.State.StateM m U256 :=
  @getTransientStorage

private theorem literalAction {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (k : Bytes32) :
    ((getTransientStorage a k).run t).run =
      pure (.ok ((t.rev.transient[(a, k)]?).getD U256.zero, t)) :=
  getTransientStorage_action t a k

private theorem retainedState (t next : TxState Id) (a : Address) (k : Bytes32) (value : U256)
    (h : ((getTransientStorage a k).run t).run = .ok (value, next)) : next = t := by
  rw [getTransientStorage_action] at h
  exact (Prod.mk.inj (Except.ok.inj h)).2.symm

end STFSpec.Conformance.State.TransientStorageCallerProofs
