/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Raw call request clients

Library `EthConformance`. Private public-facade clients check all independent
fields through complete values, reconstruction and updates.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.CallRequestCallerProofs
open STFSpec.Base STFSpec.Vm.Instructions

private def construct (gas : Nat)
    (stateGasReservoir : Nat)
    (value : U256)
    (caller : Address)
    (to : Address)
    (codeAddress : Address)
    (shouldTransferValue : Bool)
    (isStatic : Bool)
    (disablePrecompiles : Bool)
    (newAccountCharged : Bool)
    (callData : Bytes)
    (code : Bytes)
    (outOffset : U256)
    (outSize : U256) : CallRequest :=
  CallRequest.mk gas stateGasReservoir value caller to codeAddress
    shouldTransferValue isStatic disablePrecompiles newAccountCharged callData code outOffset outSize

private def fields (r : CallRequest) :
    Nat × Nat × U256 × Address × Address × Address × Bool × Bool × Bool × Bool ×
      Bytes × Bytes × U256 × U256 :=
  (r.gas, r.stateGasReservoir, r.value, r.caller,
    r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
    r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
    r.outOffset, r.outSize)

private theorem constructor_fields (gas : Nat)
    (stateGasReservoir : Nat)
    (value : U256)
    (caller : Address)
    (to : Address)
    (codeAddress : Address)
    (shouldTransferValue : Bool)
    (isStatic : Bool)
    (disablePrecompiles : Bool)
    (newAccountCharged : Bool)
    (callData : Bytes)
    (code : Bytes)
    (outOffset : U256)
    (outSize : U256) :
    fields (construct gas stateGasReservoir value caller to codeAddress
      shouldTransferValue isStatic disablePrecompiles newAccountCharged callData code outOffset outSize) =
      (gas, stateGasReservoir, value, caller,
        to, codeAddress, shouldTransferValue, isStatic,
        disablePrecompiles, newAccountCharged, callData, code,
        outOffset, outSize) := rfl

private theorem reconstruction (r : CallRequest) :
    CallRequest.mk r.gas r.stateGasReservoir r.value r.caller r.to r.codeAddress
      r.shouldTransferValue r.isStatic r.disablePrecompiles r.newAccountCharged
      r.callData r.code r.outOffset r.outSize = r := rfl

private theorem all_fields_determine (r s : CallRequest) (h : fields r = fields s) :
    r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem updates (r : CallRequest) (gas : Nat)
    (stateGasReservoir : Nat)
    (value : U256)
    (caller : Address)
    (to : Address)
    (codeAddress : Address)
    (shouldTransferValue : Bool)
    (isStatic : Bool)
    (disablePrecompiles : Bool)
    (newAccountCharged : Bool)
    (callData : Bytes)
    (code : Bytes)
    (outOffset : U256)
    (outSize : U256) :
    fields { r with gas := gas } =
      (gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with stateGasReservoir := stateGasReservoir } =
      (r.gas, stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with value := value } =
      (r.gas, r.stateGasReservoir, value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with caller := caller } =
      (r.gas, r.stateGasReservoir, r.value, caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with to := to } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with codeAddress := codeAddress } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with shouldTransferValue := shouldTransferValue } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with isStatic := isStatic } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with disablePrecompiles := disablePrecompiles } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with newAccountCharged := newAccountCharged } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, newAccountCharged, r.callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with callData := callData } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, callData, r.code,
        r.outOffset, r.outSize) ∧
    fields { r with code := code } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, code,
        r.outOffset, r.outSize) ∧
    fields { r with outOffset := outOffset } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        outOffset, r.outSize) ∧
    fields { r with outSize := outSize } =
      (r.gas, r.stateGasReservoir, r.value, r.caller,
        r.to, r.codeAddress, r.shouldTransferValue, r.isStatic,
        r.disablePrecompiles, r.newAccountCharged, r.callData, r.code,
        r.outOffset, outSize) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def observe (r : CallRequest) :
    Nat × Nat × Nat × Nat × Nat × Nat × Bool × Bool × Bool × Bool ×
      List UInt8 × List UInt8 × Nat × Nat :=
  (r.gas, r.stateGasReservoir, r.value.toNat, r.caller.toNat, r.to.toNat,
    r.codeAddress.toNat, r.shouldTransferValue, r.isStatic, r.disablePrecompiles,
    r.newAccountCharged, r.callData.toList, r.code.toList, r.outOffset.toNat, r.outSize.toNat)

private theorem complete_observation (r : CallRequest) :
    observe r =
      (r.gas, r.stateGasReservoir, r.value.toNat, r.caller.toNat, r.to.toNat,
            r.codeAddress.toNat, r.shouldTransferValue, r.isStatic, r.disablePrecompiles,
            r.newAccountCharged, r.callData.toList, r.code.toList, r.outOffset.toNat,
            r.outSize.toNat) := rfl

private theorem complete_bytes (r : CallRequest) (input program : List UInt8) :
    ({ r with callData := Bytes.ofList input, code := Bytes.ofList program }).callData.toList =
      input ∧
    ({ r with callData := Bytes.ofList input, code := Bytes.ofList program }).code.toList =
      program := ⟨Bytes.toList_ofList input, Bytes.toList_ofList program⟩

private def control (gas reservoir value caller target codeAddress : Nat)
    (transfer static disabled charged : Bool) (input program : List UInt8)
    (offset size : Nat) : CallRequest :=
  construct gas reservoir (U256.ofNat value) (Address.ofNat caller) (Address.ofNat target)
    (Address.ofNat codeAddress) transfer static disabled charged
    (Bytes.ofList input) (Bytes.ofList program) (U256.ofNat offset) (U256.ofNat size)

private theorem control_observation (gas reservoir value caller target codeAddress : Nat)
    (transfer static disabled charged : Bool) (input program : List UInt8)
    (offset size : Nat) :
    observe (control gas reservoir value caller target codeAddress transfer static disabled
      charged input program offset size) =
      (gas, reservoir, value % 2 ^ 256, caller % 2 ^ 160, target % 2 ^ 160,
            codeAddress % 2 ^ 160, transfer, static, disabled, charged, input, program,
            offset % 2 ^ 256, size % 2 ^ 256) := by
  simp only [control, construct, observe, U256.toNat_ofNat, Address.toNat_ofNat,
    Bytes.toList_ofList]

-- Complete observations keep grants independent, every Bool unrestricted, all
-- three addresses distinct/equal, raw bytes ordered and output windows unbounded.
#guard observe (control 0 0 0 0 0 0 false false false false [] [] 0 0) ==
  (0, 0, 0, 0, 0, 0, false, false, false, false, [], [], 0, 0)
#guard observe (control (2 ^ 300 + 7) 0 (2 ^ 256 - 1) (2 ^ 160 - 1) 1 (2 ^ 159 + 5)
  true false true false [0, 255, 1, 0, 128, 255] [255, 0, 254] (2 ^ 256 - 1) 0) ==
  (2 ^ 300 + 7, 0, 2 ^ 256 - 1, 2 ^ 160 - 1, 1, 2 ^ 159 + 5,
    true, false, true, false, [0, 255, 1, 0, 128, 255], [255, 0, 254], 2 ^ 256 - 1, 0)
#guard observe (control 0 (2 ^ 400 + 11) (2 ^ 255 + 3) 2 (2 ^ 159 + 7) 3
  false true false true [] [0, 0, 255, 1] 1 (2 ^ 256 - 1)) ==
  (0, 2 ^ 400 + 11, 2 ^ 255 + 3, 2, 2 ^ 159 + 7, 3,
    false, true, false, true, [], [0, 0, 255, 1], 1, 2 ^ 256 - 1)
#guard observe (control 9 31 1 7 7 7 true true true true [1, 0, 1] [] 29 3) ==
  (9, 31, 1, 7, 7, 7, true, true, true, true, [1, 0, 1], [], 29, 3)

-- Negative controls distinguish bytes, addresses, independent flags and windows;
-- raw construction does not reinterpret a static transfer or clamp an output size.
#guard observe (control 9 31 5 2 3 4 true true false true [0, 1, 0] [255, 0] 29 37) !=
  (9, 31, 5, 2, 4, 3, true, true, false, true, [0, 1, 0], [255, 0], 29, 37)
#guard observe (control 9 31 5 2 3 4 true true false true [0, 1, 0] [255, 0] 29 37) !=
  (9, 31, 5, 2, 3, 4, true, false, true, true, [255, 0], [0, 1, 0], 37, 29)

end STFSpec.Conformance.Vm.Instructions.CallRequestCallerProofs
