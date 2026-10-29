/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public stack depth literal clients

Library `EthConformance`. Private facade clients check the Nat signature,
reflexive literal reduction and reducible indexed bound without provider internals.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5.
-/

namespace STFSpec.Conformance.Vm.Core.StackDepthLimitCallerProofs
open STFSpec.Vm.Core

private def nat_signature : Nat := STACK_DEPTH_LIMIT

private theorem literal : STACK_DEPTH_LIMIT = 1024 := rfl

private def indexed_bound (i : Fin 1024) : Fin STACK_DEPTH_LIMIT := i

private theorem indexed_value (i : Fin 1024) : (indexed_bound i).val = i.val := rfl

#guard STACK_DEPTH_LIMIT == 1024

end STFSpec.Conformance.Vm.Core.StackDepthLimitCallerProofs
