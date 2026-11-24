/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Precompiles

/-!
# Standalone IDENTITY controls

Library `EthConformance`. Check the actual facade with complete success
outputs, all meter fields and the nominal halt.
-/

namespace STFSpec.Conformance.Precompiles

open STFSpec.Base STFSpec.Hash STFSpec.Precompiles STFSpec.Vm.Core

private def amsterdam := STFSpec.Fork.Amsterdam.vmConfig

private def input (size : Nat) : Bytes :=
  Bytes.ofList ((List.range size).map fun i ↦ UInt8.ofNat (i * 109 + 161))

private def meter (gasLeft : Nat) : GasMeter :=
  ⟨gasLeft, 2^259 + 13, 11, -19, 17, 2^257 + 23⟩

private def check (cfg : VmConfig) (size budget : Nat) (expectedGas : Option Nat) : Bool :=
  let data := input size
  let entryMeter := meter budget
  let result : PrecompileResult := identity (m := Id) cfg data entryMeter
  match result, expectedGas with
  | .ok charged output, some gasLeft =>
    charged.gasLeft == gasLeft &&
      charged.stateGasLeft == entryMeter.stateGasLeft &&
      charged.stateGasBaseline == entryMeter.stateGasBaseline &&
      charged.refundCounter == entryMeter.refundCounter &&
      charged.stateGasSpilled == entryMeter.stateGasSpilled &&
      charged.stateGasCommittedSpill == entryMeter.stateGasCommittedSpill &&
      output.toList == data.toList
  | .halt .outOfGas, none => true
  | _, _ => false

private def raw (base perWord : Nat) : VmConfig :=
  { amsterdam with
    costs := { amsterdam.costs with
      precompileIdentityBase := base
      precompileIdentityPerWord := perWord
      opcodeCodeCopyBase := 2^273 + 41 }
    stateCosts := ⟨0, 31, 9, 77⟩
    limits := ⟨8, 99, 4⟩ }

#guard check amsterdam 0 14 none
#guard check amsterdam 0 15 (some 0)
#guard check amsterdam 1 17 none
#guard check amsterdam 1 18 (some 0)
#guard check amsterdam 31 18 (some 0)
#guard check amsterdam 32 18 (some 0)
#guard check amsterdam 33 20 none
#guard check amsterdam 33 21 (some 0)
#guard check amsterdam 63 21 (some 0)
#guard check amsterdam 64 25 (some 4)
#guard check amsterdam 65 23 none
#guard check amsterdam 65 24 (some 0)
#guard check (raw 0 0) 65 0 (some 0)
#guard check (raw 0 17) 0 0 (some 0)
#guard check (raw 41 0) 65 40 none
#guard check (raw 41 0) 65 42 (some 1)

private def largeBase : Nat := 2^269 + 27
private def largePerWord : Nat := 2^258 + 7

#guard check (raw largeBase largePerWord) 33 (largeBase + 2 * largePerWord - 1) none
#guard check (raw largeBase largePerWord) 33 (largeBase + 2 * largePerWord) (some 0)

private def retainsQueryCounter (budget : Nat) (paid : Bool) : Bool :=
  letI : KeccakQuery (StateM Nat) := ⟨fun _ ↦ do
    modify (· + 1)
    pure (Hash32.ofBytes32 (FixedBytes.ofNat 0))⟩
  let (result, counter) := (identity (m := StateM Nat) amsterdam (input 1) (meter budget)).run 73
  counter == 73 && match result with
    | .ok _ _ => paid
    | .halt .outOfGas => !paid
    | .halt _ => false

#guard retainsQueryCounter 18 true
#guard retainsQueryCounter 17 false

end STFSpec.Conformance.Precompiles
