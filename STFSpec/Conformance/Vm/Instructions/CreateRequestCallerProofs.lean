/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Raw creation request clients

Library `EthConformance`. Private public-facade clients retain every independent
field by constructor, projections, reconstruction and record updates.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.CreateRequestCallerProofs
open STFSpec.Base STFSpec.Vm.Instructions

private def construct (gas reservoir : Nat) (endowment : U256)
    (caller target : Address) (initCode : Bytes) (charged : Bool) : CreateRequest :=
  CreateRequest.mk gas reservoir endowment caller target initCode charged

private def fields (r : CreateRequest) :
    Nat × Nat × U256 × Address × Address × Bytes × Bool :=
  (r.gas, r.stateGasReservoir, r.endowment, r.caller, r.contractAddress,
    r.initCode, r.newAccountCharged)

private theorem constructor_fields (gas reservoir : Nat) (endowment : U256)
    (caller target : Address) (initCode : Bytes) (charged : Bool) :
    fields (construct gas reservoir endowment caller target initCode charged) =
      (gas, reservoir, endowment, caller, target, initCode, charged) := rfl

private theorem reconstruction (r : CreateRequest) :
    CreateRequest.mk r.gas r.stateGasReservoir r.endowment r.caller r.contractAddress
      r.initCode r.newAccountCharged = r := rfl

private theorem all_fields_determine (r s : CreateRequest) (h : fields r = fields s) :
    r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem updates (r : CreateRequest) (gas reservoir : Nat) (endowment : U256)
    (caller target : Address) (initCode : Bytes) (charged : Bool) :
    fields { r with gas := gas } =
      (gas, r.stateGasReservoir, r.endowment, r.caller, r.contractAddress,
        r.initCode, r.newAccountCharged) ∧
    fields { r with stateGasReservoir := reservoir } =
      (r.gas, reservoir, r.endowment, r.caller, r.contractAddress,
        r.initCode, r.newAccountCharged) ∧
    fields { r with endowment := endowment } =
      (r.gas, r.stateGasReservoir, endowment, r.caller, r.contractAddress,
        r.initCode, r.newAccountCharged) ∧
    fields { r with caller := caller } =
      (r.gas, r.stateGasReservoir, r.endowment, caller, r.contractAddress,
        r.initCode, r.newAccountCharged) ∧
    fields { r with contractAddress := target } =
      (r.gas, r.stateGasReservoir, r.endowment, r.caller, target,
        r.initCode, r.newAccountCharged) ∧
    fields { r with initCode := initCode } =
      (r.gas, r.stateGasReservoir, r.endowment, r.caller, r.contractAddress,
        initCode, r.newAccountCharged) ∧
    fields { r with newAccountCharged := charged } =
      (r.gas, r.stateGasReservoir, r.endowment, r.caller, r.contractAddress,
        r.initCode, charged) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def observe (r : CreateRequest) :
    Nat × Nat × Nat × Nat × Nat × List UInt8 × Bool :=
  (r.gas, r.stateGasReservoir, r.endowment.toNat, r.caller.toNat,
    r.contractAddress.toNat, r.initCode.toList, r.newAccountCharged)

private theorem complete_observation (gas reservoir : Nat) (endowment : U256)
    (caller target : Address) (initCode : Bytes) (charged : Bool) :
    observe (construct gas reservoir endowment caller target initCode charged) =
      (gas, reservoir, endowment.toNat, caller.toNat, target.toNat,
        initCode.toList, charged) := rfl

private theorem byte_construction (gas reservoir : Nat) (endowment : U256)
    (caller target : Address) (bytes : List UInt8) (charged : Bool) :
    (construct gas reservoir endowment caller target (Bytes.ofList bytes) charged).initCode.toList =
      bytes := Bytes.toList_ofList bytes

private def control (gas reservoir word caller target : Nat) (bytes : List UInt8)
    (charged : Bool) : CreateRequest :=
  construct gas reservoir (U256.ofNat word) (Address.ofNat caller) (Address.ofNat target)
    (Bytes.ofList bytes) charged

private theorem control_observation (gas reservoir word caller target : Nat)
    (bytes : List UInt8) (charged : Bool) :
    observe (control gas reservoir word caller target bytes charged) =
      (gas, reservoir, word % 2 ^ 256, caller % 2 ^ 160, target % 2 ^ 160, bytes, charged) := by
  simp only [control, complete_observation, U256.toNat_ofNat, Address.toNat_ofNat,
    Bytes.toList_ofList]

-- Complete deterministic observations include both booleans, zero/huge independent
-- grants, distinct/full-width addresses, full-width words and ordered duplicate bytes.
#guard observe (control 0 0 0 0 0 [] false) == (0, 0, 0, 0, 0, [], false)
#guard observe (control (2 ^ 300 + 7) 0 (2 ^ 256 - 1) (2 ^ 160 - 1) 1
  [0, 255, 1, 0, 128, 255] true) ==
  (2 ^ 300 + 7, 0, 2 ^ 256 - 1, 2 ^ 160 - 1, 1, [0, 255, 1, 0, 128, 255], true)
#guard observe (control 0 (2 ^ 400 + 11) (2 ^ 255 + 3) 2 (2 ^ 159 + 5)
  [255, 0, 0, 254, 1] false) ==
  (0, 2 ^ 400 + 11, 2 ^ 255 + 3, 2, 2 ^ 159 + 5, [255, 0, 0, 254, 1], false)
#guard observe (control 9 31 1 7 7 [1, 0, 1] true) == (9, 31, 1, 7, 7, [1, 0, 1], true)

end STFSpec.Conformance.Vm.Instructions.CreateRequestCallerProofs
