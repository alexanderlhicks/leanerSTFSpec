/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Public raw withdrawal clients

Library `EthConformance`. Private clients check complete arbitrary construction,
projection, reconstruction, equality and independent updates through the Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Conformance.Block.WithdrawalCallerProofs

open STFSpec.Base STFSpec.Block

private def constructorType : U64 → U64 → Address → U64 → Withdrawal := Withdrawal.mk
private def indexType : Withdrawal → U64 := Withdrawal.index
private def validatorIndexType : Withdrawal → U64 := Withdrawal.validatorIndex
private def addressType : Withdrawal → Address := Withdrawal.address
private def amountType : Withdrawal → U64 := Withdrawal.amount

private def fields (w : Withdrawal) : U64 × U64 × Address × U64 :=
  (w.index, w.validatorIndex, w.address, w.amount)

private theorem constructor_fields (index validatorIndex : U64) (address : Address) (amount : U64) :
    fields (Withdrawal.mk index validatorIndex address amount) =
      (index, validatorIndex, address, amount) := rfl

private theorem reconstruction (w : Withdrawal) :
    Withdrawal.mk w.index w.validatorIndex w.address w.amount = w := rfl

private theorem all_fields_determine (w v : Withdrawal) : fields w = fields v ↔ w = v := by
  constructor
  · intro h
    cases w
    cases v
    cases h
    rfl
  · exact congrArg fields

private theorem update_index (w : Withdrawal) (index : U64) :
    fields { w with index := index } = (index, w.validatorIndex, w.address, w.amount) := rfl

private theorem update_validatorIndex (w : Withdrawal) (validatorIndex : U64) :
    fields { w with validatorIndex := validatorIndex } =
      (w.index, validatorIndex, w.address, w.amount) := rfl

private theorem update_address (w : Withdrawal) (address : Address) :
    fields { w with address := address } = (w.index, w.validatorIndex, address, w.amount) := rfl

private theorem update_amount (w : Withdrawal) (amount : U64) :
    fields { w with amount := amount } = (w.index, w.validatorIndex, w.address, amount) := rfl

end STFSpec.Conformance.Block.WithdrawalCallerProofs
