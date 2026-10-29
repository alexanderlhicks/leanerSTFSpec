/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete raw frame error controls

Library `EthConformance`. Private observations retain both branches, every nested
halt tag, all 256 opcode bytes and complete empty, NUL, Unicode and long reasons.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5.
-/

namespace STFSpec.Conformance.Vm.Core.FrameErrorGuards
open STFSpec.Vm.Core

private def observe : FrameError → String × Option UInt8 × Option String
  | .revert => ("revert", none, none)
  | .halt .stackUnderflow => ("halt.stackUnderflow", none, none)
  | .halt .stackOverflow => ("halt.stackOverflow", none, none)
  | .halt .outOfGas => ("halt.outOfGas", none, none)
  | .halt (.invalidOpcode code) => ("halt.invalidOpcode", some code, none)
  | .halt .invalidJumpDest => ("halt.invalidJumpDest", none, none)
  | .halt .stackDepthLimit => ("halt.stackDepthLimit", none, none)
  | .halt .writeInStaticContext => ("halt.writeInStaticContext", none, none)
  | .halt .outOfBoundsRead => ("halt.outOfBoundsRead", none, none)
  | .halt .invalidParameter => ("halt.invalidParameter", none, none)
  | .halt .invalidContractPrefix => ("halt.invalidContractPrefix", none, none)
  | .halt .addressCollision => ("halt.addressCollision", none, none)
  | .halt .kzgProofError => ("halt.kzgProofError", none, none)
  | .halt (.precompileHalt reason) => ("halt.precompileHalt", none, some reason)

#guard observe .revert == ("revert", none, none)
#guard observe (.halt .stackUnderflow) == ("halt.stackUnderflow", none, none)
#guard observe (.halt .stackOverflow) == ("halt.stackOverflow", none, none)
#guard observe (.halt .outOfGas) == ("halt.outOfGas", none, none)
#guard observe (.halt .invalidJumpDest) == ("halt.invalidJumpDest", none, none)
#guard observe (.halt .stackDepthLimit) == ("halt.stackDepthLimit", none, none)
#guard observe (.halt .writeInStaticContext) == ("halt.writeInStaticContext", none, none)
#guard observe (.halt .outOfBoundsRead) == ("halt.outOfBoundsRead", none, none)
#guard observe (.halt .invalidParameter) == ("halt.invalidParameter", none, none)
#guard observe (.halt .invalidContractPrefix) == ("halt.invalidContractPrefix", none, none)
#guard observe (.halt .addressCollision) == ("halt.addressCollision", none, none)
#guard observe (.halt .kzgProofError) == ("halt.kzgProofError", none, none)

#guard (List.range 256).map (fun n => observe (.halt (.invalidOpcode n.toUInt8))) ==
  (List.range 256).map (fun n => ("halt.invalidOpcode", some n.toUInt8, none))

#guard observe (.halt (.precompileHalt "")) == ("halt.precompileHalt", none, some "")
#guard observe (.halt (.precompileHalt "a\x00b")) ==
  ("halt.precompileHalt", none, some "a\x00b")
#guard observe (.halt (.precompileHalt "é λ 以太坊 🚀")) ==
  ("halt.precompileHalt", none, some "é λ 以太坊 🚀")
#guard observe (.halt (.precompileHalt (String.ofList (List.replicate 1024 'z')))) ==
  ("halt.precompileHalt", none, some (String.ofList (List.replicate 1024 'z')))

end STFSpec.Conformance.Vm.Core.FrameErrorGuards
