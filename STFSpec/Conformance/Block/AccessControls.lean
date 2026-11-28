/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Raw transaction access entry controls

Library `EthConformance`. Private facade clients check both fields on arbitrary
inputs. Interpreted controls compare the complete address and slot bytes.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5 and 7.
-/

namespace STFSpec.Conformance.Block.AccessControls

open STFSpec.Base STFSpec.Block

private def constructorType : Address → Array Bytes32 → Access := Access.mk
private def accountType : Access → Address := Access.account
private def slotsType : Access → Array Bytes32 := Access.slots

private def fields (entry : Access) : Address × Array Bytes32 := (entry.account, entry.slots)

private theorem constructor_fields (account : Address) (slots : Array Bytes32) :
    fields (Access.mk account slots) = (account, slots) := rfl

private theorem reconstruction (entry : Access) :
    Access.mk entry.account entry.slots = entry := rfl

private theorem update_account (entry : Access) (account : Address) :
    fields { entry with account := account } = (account, entry.slots) := rfl

private theorem update_slots (entry : Access) (slots : Array Bytes32) :
    fields { entry with slots := slots } = (entry.account, slots) := rfl

private def observe (entry : Access) : List UInt8 × List (List UInt8) :=
  (entry.account.toBytes.toList, entry.slots.toList.map fun slot ↦ slot.toBytes.toList)

private def sampleAccount : Address :=
  Address.ofNat 0x000102030405060708090a0b0c0d0e0f10111213

private def accountBytes : List UInt8 :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

private def lowSlot : Bytes32 :=
  FixedBytes.ofNat 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f

private def highSlot : Bytes32 :=
  FixedBytes.ofNat 0xfffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0

private def lowSlotBytes : List UInt8 :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

private def highSlotBytes : List UInt8 :=
  [255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240,
    239, 238, 237, 236, 235, 234, 233, 232, 231, 230, 229, 228, 227, 226, 225, 224]

#guard observe (Access.mk sampleAccount #[]) == (accountBytes, [])

#guard observe (Access.mk sampleAccount #[highSlot, lowSlot, highSlot]) ==
  (accountBytes, [highSlotBytes, lowSlotBytes, highSlotBytes])

end STFSpec.Conformance.Block.AccessControls
