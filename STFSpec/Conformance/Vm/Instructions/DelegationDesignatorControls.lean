/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Delegation designator controls

Library `EthConformance`. Compare exact result bytes and exercise both
ordinary model laws through the Instructions facade. See EthVmInstructions §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.DelegationDesignatorControls

open STFSpec.Base STFSpec.Vm.Instructions

private def observe (code : Bytes) : Bool × Option (List UInt8) :=
  ⟨isValidDelegation code, (getDelegatedCodeAddress code).map (fun address ↦ address.toBytes.toList)⟩

private def zeroTarget : List UInt8 := List.replicate 20 0
private def varied : List UInt8 := [0, 0, 0x98, 0x71, 0x80, 0, 0x81, 7, 11, 0, 17, 0xff, 23, 0, 0, 31, 0xa1, 3, 6, 0xed]
private def designator (target : List UInt8) : Bytes :=
  EOA_DELEGATION_MARKER ++ Bytes.ofList target

private theorem accepts_exact (code : Bytes) :
    isValidDelegation code = true ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00] :=
  isValidDelegation_iff code

private theorem exact_suffix (code : Bytes) (address : Address) :
    getDelegatedCodeAddress code = some address ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00] ∧
        code.toList.drop 3 = address.toBytes.toList :=
  getDelegatedCodeAddress_eq_some_iff code address

#guard EOA_DELEGATION_MARKER.toList == [0xef, 0x01, 0x00]
#guard observe Bytes.empty == (false, none)
#guard observe (Bytes.ofList [0xef]) == (false, none)
#guard observe (Bytes.ofList [0xef, 0x01]) == (false, none)
#guard observe EOA_DELEGATION_MARKER == (false, none)
#guard observe (designator (List.replicate 19 0x94)) == (false, none)
#guard observe (designator (List.replicate 21 0)) == (false, none)
#guard observe (designator (List.replicate 22 0)) == (false, none)
#guard observe (Bytes.ofList ([0xee, 0x01, 0x00] ++ varied)) == (false, none)
#guard observe (Bytes.ofList ([0xef, 0x81, 0x00] ++ varied)) == (false, none)
#guard observe (Bytes.ofList ([0xef, 0x01, 0x80] ++ varied)) == (false, none)
#guard observe (designator zeroTarget) == (true, some zeroTarget)
#guard observe (designator varied) == (true, some varied)
#guard observe (designator varied.reverse) == (true, some varied.reverse)
#guard observe (designator (List.replicate 20 0xff)) == (true, some (List.replicate 20 0xff))
#guard observe (designator ([0xef, 0x01, 0x00] ++ List.replicate 17 0x80)) ==
  (true, some ([0xef, 0x01, 0x00] ++ List.replicate 17 0x80))
#guard observe (designator (List.replicate 2048 0x7f)) == (false, none)

end STFSpec.Conformance.Vm.Instructions.DelegationDesignatorControls
