/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Delegation designators

Library `EthVmInstructions`. Recognize and extract an EIP-7702 designator
from its bytes. Spec guidance in `STFSpec/informal/modules/EthVmInstructions.md` R-DEL-1.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base

/-- The three-byte prefix in EELS `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:36`. -/
def EOA_DELEGATION_MARKER : Bytes := Bytes.ofList [0xef, 0x01, 0x00]

private def EOA_DELEGATION_MARKER_LENGTH : Nat := EOA_DELEGATION_MARKER.size
private def EOA_DELEGATED_CODE_LENGTH : Nat := 23

private theorem code_index {code : Bytes} (length : code.size = EOA_DELEGATED_CODE_LENGTH)
    (i : Nat) (index : i < 3) : i < code.size := by
  rw [length]
  unfold EOA_DELEGATED_CODE_LENGTH
  omega

private def matchesMarker (code : Bytes) (length : code.size = EOA_DELEGATED_CODE_LENGTH) : Bool :=
  code[0]'(code_index length 0 (by decide)) == EOA_DELEGATION_MARKER[0]'(by decide) &&
  code[1]'(code_index length 1 (by decide)) == EOA_DELEGATION_MARKER[1]'(by decide) &&
  code[2]'(code_index length 2 (by decide)) == EOA_DELEGATION_MARKER[2]'(by decide)

/-- Accept the exact designator length and marker.
EELS `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:42–61`. -/
def isValidDelegation (code : Bytes) : Bool :=
  if length : code.size = EOA_DELEGATED_CODE_LENGTH then matchesMarker code length else false

/-- Return the complete address suffix of a valid designator.
EELS `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:64–81`. -/
def getDelegatedCodeAddress (code : Bytes) : Option Address :=
  if isValidDelegation code then
    Address.ofBytes? (code.extract EOA_DELEGATION_MARKER_LENGTH EOA_DELEGATED_CODE_LENGTH)
  else none

private theorem take_three (code : Bytes) (length : code.size = EOA_DELEGATED_CODE_LENGTH) :
    code.toList.take 3 =
      [code[0]'(code_index length 0 (by decide)), code[1]'(code_index length 1 (by decide)),
        code[2]'(code_index length 2 (by decide))] := by
  apply List.ext_getElem
  · simp [List.length_take, Bytes.length_toList, length, EOA_DELEGATED_CODE_LENGTH]
  · intro i hi hj
    rw [List.getElem_take]
    rcases i with _ | _ | _ | i
    · exact Bytes.getElem_toList code 0 (code_index length 0 (by decide))
    · exact Bytes.getElem_toList code 1 (code_index length 1 (by decide))
    · exact Bytes.getElem_toList code 2 (code_index length 2 (by decide))
    · simp only [List.length_cons, List.length_nil] at hj
      omega

private theorem marker_length : EOA_DELEGATION_MARKER_LENGTH = 3 := by decide

private theorem marker_get_zero : EOA_DELEGATION_MARKER[0]'(by decide) = 0xef := by decide
private theorem marker_get_one : EOA_DELEGATION_MARKER[1]'(by decide) = 0x01 := by decide
private theorem marker_get_two : EOA_DELEGATION_MARKER[2]'(by decide) = 0x00 := by decide

/-- Recognition holds exactly for a 23-byte sequence with the three marker bytes. -/
theorem isValidDelegation_iff (code : Bytes) :
    isValidDelegation code = true ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00] := by
  by_cases length : code.size = EOA_DELEGATED_CODE_LENGTH
  · simp [isValidDelegation, length, matchesMarker, take_three code length, Bytes.length_toList,
      EOA_DELEGATED_CODE_LENGTH, marker_get_zero, marker_get_one, marker_get_two, and_assoc]
  · have notLength : code.toList.length ≠ 23 := by
      rw [Bytes.length_toList]
      exact length
    simp [isValidDelegation, length, notLength]

/-- A returned address has exactly the 20-byte suffix after a valid marker. -/
theorem getDelegatedCodeAddress_eq_some_iff (code : Bytes) (address : Address) :
    getDelegatedCodeAddress code = some address ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00] ∧
        code.toList.drop 3 = address.toBytes.toList := by
  unfold getDelegatedCodeAddress
  by_cases valid : isValidDelegation code = true
  · obtain ⟨length, mark⟩ := (isValidDelegation_iff code).mp valid
    have size : code.size = 23 := (Bytes.length_toList code).symm.trans length
    have dropLength : (code.toList.drop 3).length = 20 := by simp [List.length_drop, length]
    simp only [valid, ↓reduceIte, Address.ofBytes?_eq_some_iff, marker_length, EOA_DELEGATED_CODE_LENGTH,
      Bytes.size_extract, size, Nat.min_self]
    have suffix : (code.extract 3 23).toList = code.toList.drop 3 := by
      rw [Bytes.toList_extract]
      exact List.take_of_length_le (by rw [dropLength]; decide)
    simp [length, mark, ← Bytes.toList_inj, suffix, eq_comm]
  · have invalid := mt (isValidDelegation_iff code).mpr valid
    simp only [valid, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun complete ↦ invalid ⟨complete.1, complete.2.1⟩

end STFSpec.Vm.Instructions
