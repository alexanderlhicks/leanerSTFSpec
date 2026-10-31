/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Kernel-reducible stack depth limit

Library `EthVmCore`. The literal depth bound supports proofs and indexed types (F8).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5.
-/

namespace STFSpec.Vm.Core

/-- Literal call-depth bound; pinned EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:84`. -/
abbrev STACK_DEPTH_LIMIT : Nat := 1024

end STFSpec.Vm.Core
