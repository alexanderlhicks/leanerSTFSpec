/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Frame

/-!
# Mutable child frame initialization

Library `EthVmInstructions`. CALL and CREATE use the same initialization
for their mutable child frames.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

/-- Initialize a child frame with the supplied execution gas and state reservoir.
The child inherits the parent's warm address and storage-key sets. Pinned EELS
(`59c1473d`), `src/ethereum/forks/amsterdam/vm/instructions/system.py:151–165,420–434`
and `src/ethereum/forks/amsterdam/vm/gas.py:295–311`. -/
def childFrame (parent : Frame) (gas reservoir : Nat) : Frame :=
  { pc := 0
    stack := Stack.empty
    memory := Memory.empty
    gasMeter :=
      { gasLeft := gas
        stateGasLeft := reservoir
        stateGasBaseline := reservoir
        refundCounter := 0
        stateGasSpilled := 0
        stateGasCommittedSpill := 0 }
    logs := LogRope.empty
    accountsToDelete := ∅
    returnData := Bytes.empty
    accessedAddresses := parent.accessedAddresses
    accessedStorageKeys := parent.accessedStorageKeys }

end STFSpec.Vm.Instructions
