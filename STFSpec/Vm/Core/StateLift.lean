/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.World

/-!
# State action lifting

Library `EthVmCore`: run a supplied State action on the world's transaction and
route its complete result into the VM error layer. Underlying effects remain in `m`.
This Lean-only operation implements EthVmCore §5; it has no separate EELS function.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7/10.
-/

namespace STFSpec.Vm.Core

/-- Run the supplied action on exactly `world.tx`, retaining its whole value and
updated transaction, or wrapping its complete error in `VmFault.state`.
Failure returns no world; this operation supplies no underlying-effect rollback. -/
def liftState {m : Type → Type} [Monad m] {α : Type}
    (action : STFSpec.State.StateM m α) : VmM m α := fun world ↦
  show m (Except VmFault (α × VmWorld m)) from
    (action.run world.tx).run >>= fun result ↦
      pure (match result with
        | .ok (value, tx) => .ok (value, { world with tx := tx })
        | .error error => .error (.state error))

/-- Complete literal run equation, requiring only the operation's `Monad` premise.
Simplifying the underlying bind and pure for an arbitrary monad can require laws. -/
theorem liftState_run {m : Type → Type} [Monad m] {α : Type}
    (action : STFSpec.State.StateM m α) (world : VmWorld m) :
    ((liftState action).run world).run =
      ((action.run world.tx).run >>= fun result ↦
        pure (match result with
          | .ok (value, tx) => .ok (value, { world with tx := tx })
          | .error error => .error (.state error))) := rfl

end STFSpec.Vm.Core
