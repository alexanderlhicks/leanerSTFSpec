/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public stack depth literal clients

Library `EthConformance`. Private facade clients check the Nat signature, literal
reduction, an indexed bound and, at reducible transparency, the literal and a numeric
`Fin STACK_DEPTH_LIMIT` value, without provider internals.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5.
-/

namespace STFSpec.Conformance.Vm.Core.StackDepthLimitCallerProofs
open STFSpec.Vm.Core

private def natSignature : Nat := STACK_DEPTH_LIMIT

private theorem literal : STACK_DEPTH_LIMIT = 1024 := rfl

-- The next two clients fail if the limit stops being reducible (for example, if it
-- becomes a `def`).
private theorem reducible_literal : STACK_DEPTH_LIMIT = 1024 := by with_reducible rfl

private def literalIndex : Fin STACK_DEPTH_LIMIT := 5

private def indexedBound (i : Fin 1024) : Fin STACK_DEPTH_LIMIT := i

private theorem indexed_value (i : Fin 1024) : (indexedBound i).val = i.val := rfl

#guard STACK_DEPTH_LIMIT == 1024

end STFSpec.Conformance.Vm.Core.StackDepthLimitCallerProofs
