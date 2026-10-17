/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Exceptional halt vocabulary

Library `EthVmCore`. The complete nominal carrier from pinned EELS
`src/ethereum/forks/amsterdam/vm/exceptions.py:17–139` and bare precompile halts
at `vm/precompiled_contracts/modexp.py:34,38,42`. Revert is a separate channel.
Supplying this vocabulary does not implement its producers or frame settlement.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.6/5.
-/

namespace STFSpec.Vm.Core

/-- Prescribed exceptional halts, retaining opcode and bare-precompile diagnostics. -/
inductive ExceptionalHalt where
  | stackUnderflow
  | stackOverflow
  | outOfGas
  | invalidOpcode (code : UInt8)
  | invalidJumpDest
  | stackDepthLimit
  | writeInStaticContext
  | outOfBoundsRead
  | invalidParameter
  | invalidContractPrefix
  | addressCollision
  | kzgProofError
  | precompileHalt (reason : String)

end STFSpec.Vm.Core
