/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.SatisfiesM
import STFSpec.Vm.Core.Precompile
import STFSpec.Vm.Core.TransactionGasSettlement
import STFSpec.Vm.Core.TransactionGasAllocation
import STFSpec.Vm.Core.Exceptions
import STFSpec.Vm.Core.Limits
import STFSpec.Vm.Core.GasMeter
import STFSpec.Vm.Core.GasCosts
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.BlockGas
import STFSpec.Vm.Core.Logs
import STFSpec.Vm.Core.Sets
import STFSpec.Vm.Core.Frame
import STFSpec.Vm.Core.TransferLog
import STFSpec.Vm.Core.Environments
import STFSpec.Vm.Core.Context
import STFSpec.Vm.Core.CallGas
import STFSpec.Vm.Core.Jumpdest
import STFSpec.Vm.Core.Memory
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Core.Stack
import STFSpec.Vm.Core.StackDecoders

/-!
# STFSpec.Vm.Core

The `Evm` frame, `Message`, environments, operand stack, memory, gas meter and gas
parameters, raw exceptional-halt/revert vocabulary, and jumpdest analysis.

Library `EthVmCore`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Implementation and ordinary-law status
are owned by `STFSpec/informal/modules/EthVmCore.md` §§3/7/10.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md`.
-/
