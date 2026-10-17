/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Lean
import STFSpec.Vm.Core

/-!
# Complete charge-kernel regressions

Library `EthConformance`. Frozen literal whole-result expectations cover every charge branch,
raw unusual meters, signed refunds, both spill pools and amounts beyond 64 bits.
Nominal exceptions cover every UInt8 payload and complete String payloads.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasMeterGuards
open STFSpec.Vm.Core

-- BEGIN charge-kernel observers
private def fields (g : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (g.gasLeft, g.stateGasLeft, g.stateGasBaseline, g.refundCounter,
   g.stateGasSpilled, g.stateGasCommittedSpill)
private def observeCheck (g : GasMeter) (a : Nat) : String × (Nat × Nat × Nat × Int × Nat × Nat) :=
  match checkGas g a with
  | .ok () => ("ok", fields g)
  | .error .outOfGas => ("oog", fields g)
  | .error _ => ("unexpected", fields g)
private def observeCharge (g : GasMeter) (a : Nat) :
    String × (Nat × Nat × Nat × Int × Nat × Nat) :=
  match chargeGas g a with
  | .ok g' => ("ok", fields g')
  | .error .outOfGas => ("oog", fields g)
  | .error _ => ("unexpected", fields g)
private def observeState (g : GasMeter) (a : Nat) : String × (Nat × Nat × Nat × Int × Nat × Nat) :=
  match chargeStateGas g a with
  | .ok g' => ("ok", fields g')
  | .error .outOfGas => ("oog", fields g)
  | .error _ => ("unexpected", fields g)
private def fieldsJson (f : Nat × Nat × Nat × Int × Nat × Nat) : Lean.Json :=
  Lean.toJson ([Lean.toJson f.1, Lean.toJson f.2.1, Lean.toJson f.2.2.1,
    Lean.toJson f.2.2.2.1, Lean.toJson f.2.2.2.2.1, Lean.toJson f.2.2.2.2.2] : List Lean.Json)
private def meterJson (g : GasMeter) : Lean.Json := fieldsJson (fields g)
private def exceptionJson (e : ExceptionalHalt) : Lean.Json :=
  let (tag, payload) : String × Lean.Json := match e with
    | .stackUnderflow => ("stackUnderflow", .null)
    | .stackOverflow => ("stackOverflow", .null)
    | .outOfGas => ("outOfGas", .null)
    | .invalidOpcode code => ("invalidOpcode", Lean.toJson code.toNat)
    | .invalidJumpDest => ("invalidJumpDest", .null)
    | .stackDepthLimit => ("stackDepthLimit", .null)
    | .writeInStaticContext => ("writeInStaticContext", .null)
    | .outOfBoundsRead => ("outOfBoundsRead", .null)
    | .invalidParameter => ("invalidParameter", .null)
    | .invalidContractPrefix => ("invalidContractPrefix", .null)
    | .addressCollision => ("addressCollision", .null)
    | .kzgProofError => ("kzgProofError", .null)
    | .precompileHalt reason => ("precompileHalt", Lean.toJson reason)
  Lean.Json.mkObj [("tag", Lean.toJson tag), ("payload", payload)]
-- END charge-kernel observers

private def unusualMeter : GasMeter :=
  { gasLeft := 10,
    stateGasLeft := 7,
    stateGasBaseline := 3,
    refundCounter := (-11),
    stateGasSpilled := 13,
    stateGasCommittedSpill := 17 }

private def emptyMeter : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 0,
    stateGasBaseline := 0,
    refundCounter := (0),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }

private def reservoirOnlyMeter : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 5,
    stateGasBaseline := 0,
    refundCounter := (-1),
    stateGasSpilled := 2,
    stateGasCommittedSpill := 3 }

private def executionOnlyMeter : GasMeter :=
  { gasLeft := 5,
    stateGasLeft := 0,
    stateGasBaseline := 9,
    refundCounter := (23),
    stateGasSpilled := 7,
    stateGasCommittedSpill := 8 }

private def largeCheckMeter : GasMeter :=
  { gasLeft := 18446744073709551617,
    stateGasLeft := 18446744073709551618,
    stateGasBaseline := 1,
    refundCounter := (-18446744073709551619),
    stateGasSpilled := 18446744073709551620,
    stateGasCommittedSpill := 18446744073709551621 }

private def largeChargeMeter : GasMeter :=
  { gasLeft := 18446744073709551617,
    stateGasLeft := 2,
    stateGasBaseline := 0,
    refundCounter := (-5),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 4 }

private def largeReservoirMeter : GasMeter :=
  { gasLeft := 3,
    stateGasLeft := 18446744073709551618,
    stateGasBaseline := 0,
    refundCounter := (-7),
    stateGasSpilled := 9,
    stateGasCommittedSpill := 11 }

private def largeSpillMeter : GasMeter :=
  { gasLeft := 18446744073709551617,
    stateGasLeft := 2,
    stateGasBaseline := 0,
    refundCounter := (-7),
    stateGasSpilled := 9,
    stateGasCommittedSpill := 11 }

-- check-zero
#guard observeCheck unusualMeter 0 ==
  ("ok", (10, 7, 3, (-11), 13, 17))
-- check-exact
#guard observeCheck unusualMeter 10 ==
  ("ok", (10, 7, 3, (-11), 13, 17))
-- check-over
#guard observeCheck unusualMeter 11 ==
  ("oog", (10, 7, 3, (-11), 13, 17))
-- charge-zero
#guard observeCharge unusualMeter 0 ==
  ("ok", (10, 7, 3, (-11), 13, 17))
-- charge-small
#guard observeCharge unusualMeter 4 ==
  ("ok", (6, 7, 3, (-11), 13, 17))
-- charge-exact
#guard observeCharge unusualMeter 10 ==
  ("ok", (0, 7, 3, (-11), 13, 17))
-- charge-over
#guard observeCharge unusualMeter 11 ==
  ("oog", (10, 7, 3, (-11), 13, 17))
-- state-zero
#guard observeState unusualMeter 0 ==
  ("ok", (10, 7, 3, (-11), 13, 17))
-- state-small
#guard observeState unusualMeter 3 ==
  ("ok", (10, 4, 3, (-11), 13, 17))
-- state-exact-reservoir
#guard observeState unusualMeter 7 ==
  ("ok", (10, 0, 3, (-11), 13, 17))
-- state-first-spill
#guard observeState unusualMeter 8 ==
  ("ok", (9, 0, 3, (-11), 14, 17))
-- state-exact-total
#guard observeState unusualMeter 17 ==
  ("ok", (0, 0, 3, (-11), 23, 17))
-- state-over-total
#guard observeState unusualMeter 18 ==
  ("oog", (10, 7, 3, (-11), 13, 17))
-- empty-check-zero
#guard observeCheck emptyMeter 0 ==
  ("ok", (0, 0, 0, 0, 0, 0))
-- empty-check-one
#guard observeCheck emptyMeter 1 ==
  ("oog", (0, 0, 0, 0, 0, 0))
-- empty-charge-zero
#guard observeCharge emptyMeter 0 ==
  ("ok", (0, 0, 0, 0, 0, 0))
-- empty-charge-one
#guard observeCharge emptyMeter 1 ==
  ("oog", (0, 0, 0, 0, 0, 0))
-- empty-state-zero
#guard observeState emptyMeter 0 ==
  ("ok", (0, 0, 0, 0, 0, 0))
-- empty-state-one
#guard observeState emptyMeter 1 ==
  ("oog", (0, 0, 0, 0, 0, 0))
-- no-exec-reservoir
#guard observeState reservoirOnlyMeter 5 ==
  ("ok", (0, 0, 0, (-1), 2, 3))
-- no-exec-over
#guard observeState reservoirOnlyMeter 6 ==
  ("oog", (0, 5, 0, (-1), 2, 3))
-- no-reservoir-spill
#guard observeState executionOnlyMeter 1 ==
  ("ok", (4, 0, 9, 23, 8, 8))
-- no-reservoir-exact
#guard observeState executionOnlyMeter 5 ==
  ("ok", (0, 0, 9, 23, 12, 8))
-- no-reservoir-over
#guard observeState executionOnlyMeter 6 ==
  ("oog", (5, 0, 9, 23, 7, 8))
-- large-check
#guard observeCheck largeCheckMeter 18446744073709551617 ==
  ("ok",
    (18446744073709551617,
    18446744073709551618,
    1,
    (-18446744073709551619),
    18446744073709551620,
    18446744073709551621))
-- large-charge
#guard observeCharge largeChargeMeter 18446744073709551616 ==
  ("ok", (1, 2, 0, (-5), 3, 4))
-- large-charge-over
#guard observeCharge largeChargeMeter 18446744073709551618 ==
  ("oog", (18446744073709551617, 2, 0, (-5), 3, 4))
-- large-state-reservoir
#guard observeState largeReservoirMeter 18446744073709551617 ==
  ("ok", (3, 1, 0, (-7), 9, 11))
-- large-state-spill
#guard observeState largeSpillMeter 18446744073709551618 ==
  ("ok", (1, 0, 0, (-7), 18446744073709551625, 11))
-- large-state-exact
#guard observeState largeSpillMeter 18446744073709551619 ==
  ("ok", (0, 0, 0, (-7), 18446744073709551626, 11))
-- large-state-over
#guard observeState largeSpillMeter 18446744073709551620 ==
  ("oog", (18446744073709551617, 2, 0, (-7), 9, 11))
#guard exceptionJson (.stackUnderflow) == Lean.Json.mkObj
  [("tag", Lean.toJson "stackUnderflow"), ("payload", Lean.Json.null)]
#guard exceptionJson (.stackOverflow) == Lean.Json.mkObj
  [("tag", Lean.toJson "stackOverflow"), ("payload", Lean.Json.null)]
#guard exceptionJson (.outOfGas) == Lean.Json.mkObj
  [("tag", Lean.toJson "outOfGas"), ("payload", Lean.Json.null)]
#guard exceptionJson (.invalidJumpDest) == Lean.Json.mkObj
  [("tag", Lean.toJson "invalidJumpDest"), ("payload", Lean.Json.null)]
#guard exceptionJson (.stackDepthLimit) == Lean.Json.mkObj
  [("tag", Lean.toJson "stackDepthLimit"), ("payload", Lean.Json.null)]
#guard exceptionJson (.writeInStaticContext) == Lean.Json.mkObj
  [("tag", Lean.toJson "writeInStaticContext"), ("payload", Lean.Json.null)]
#guard exceptionJson (.outOfBoundsRead) == Lean.Json.mkObj
  [("tag", Lean.toJson "outOfBoundsRead"), ("payload", Lean.Json.null)]
#guard exceptionJson (.invalidParameter) == Lean.Json.mkObj
  [("tag", Lean.toJson "invalidParameter"), ("payload", Lean.Json.null)]
#guard exceptionJson (.invalidContractPrefix) == Lean.Json.mkObj
  [("tag", Lean.toJson "invalidContractPrefix"), ("payload", Lean.Json.null)]
#guard exceptionJson (.addressCollision) == Lean.Json.mkObj
  [("tag", Lean.toJson "addressCollision"), ("payload", Lean.Json.null)]
#guard exceptionJson (.kzgProofError) == Lean.Json.mkObj
  [("tag", Lean.toJson "kzgProofError"), ("payload", Lean.Json.null)]
-- Exhaustive nominal serialization over every UInt8 payload.
#guard (List.range 256).all fun n =>
  exceptionJson (.invalidOpcode (UInt8.ofNat n)) == Lean.Json.mkObj
    [("tag", Lean.toJson "invalidOpcode"), ("payload", Lean.toJson n)]
#guard exceptionJson (.precompileHalt "") == Lean.Json.mkObj
  [("tag", Lean.toJson "precompileHalt"), ("payload", Lean.toJson "")]
#guard exceptionJson (.precompileHalt "MODEXP input error") == Lean.Json.mkObj
  [("tag", Lean.toJson "precompileHalt"), ("payload", Lean.toJson "MODEXP input error")]
#guard exceptionJson (.precompileHalt "a\x00b\n\"\\") == Lean.Json.mkObj
  [("tag", Lean.toJson "precompileHalt"), ("payload", Lean.toJson "a\x00b\n\"\\")]
#guard exceptionJson (.precompileHalt "λ🙂") == Lean.Json.mkObj
  [("tag", Lean.toJson "precompileHalt"), ("payload", Lean.toJson "λ🙂")]
#guard exceptionJson (.precompileHalt "negative exponent") == Lean.Json.mkObj
  [("tag", Lean.toJson "precompileHalt"), ("payload", Lean.toJson "negative exponent")]
#guard fields ({ gasLeft := 2, stateGasLeft := 3, stateGasBaseline := 4 } : GasMeter) ==
  (2, 3, 4, 0, 0, 0)

end STFSpec.Conformance.Vm.Core.GasMeterGuards
