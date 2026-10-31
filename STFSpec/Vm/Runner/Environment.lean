/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Precompile
import STFSpec.Vm.Core.Config

/-!
# Raw runner environment

Library `EthVmRunner`. Source-free storage of the complete supplied precompile
table, VM configuration and system address. Assembly and execution remain separate.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner

/-- Raw Runner-owned storage for supplied policy and certified precompile data.
The Fork-owned system address follows F8; this carrier performs no assembly or execution. -/
structure RunnerEnv (m : Type → Type) [Monad m] where
  /-- Complete supplied table, including its lookup-domain and action certificates. -/
  precompiles : STFSpec.Vm.Core.PrecompileTable m
  /-- Complete supplied execution costs, state costs and VM limits. -/
  vm : STFSpec.Vm.Core.VmConfig
  /-- Supplied immutable system address, without a selected literal or coherence premise. -/
  systemAddress : STFSpec.Base.Address

end STFSpec.Vm.Runner
