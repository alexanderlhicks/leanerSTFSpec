/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Frame
import STFSpec.Vm.Core.Exceptions

/-!
# Raw runner output carriers

Library `EthVmRunner`. Store complete frame and transaction results without
settlement, conversion or execution. Source correspondence belongs to producers.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner
open STFSpec.Base STFSpec.Vm.Core

/-- Raw project result partition for EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:395–469`.
Error presence supplies no settlement proof; output is independent of frame return data. -/
structure FrameResult where
  /-- Complete supplied mutable frame. -/
  frame : Frame
  /-- Complete output bytes, independent of the frame's most recent child return data. -/
  output : Bytes
  /-- Optional complete halt or revert value, without a settlement premise. -/
  error : Option FrameError

/-- Raw storage corresponding to EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:86–116`.
The Nat refund performs no U256 conversion or range check (Q66). -/
structure TransactionOutput where
  /-- Supplied execution gas remaining, without a bound. -/
  gasLeft : Nat
  /-- Supplied natural refund, without an unsigned-word bound. -/
  refundCounter : Nat
  /-- Complete raw chronological rope, independent of error presence. -/
  logs : LogRope
  /-- Complete supplied deletion set, independent of error presence. -/
  accountsToDelete : AddrSet
  /-- Optional complete halt or revert value. -/
  error : Option FrameError
  /-- Complete supplied execution output. -/
  returnData : Bytes
  /-- Supplied remaining state gas, independent of other gas fields. -/
  stateGasLeft : Nat
  /-- Signed net state gas usage, including negative values. -/
  stateGasUsed : Int

end STFSpec.Vm.Runner
