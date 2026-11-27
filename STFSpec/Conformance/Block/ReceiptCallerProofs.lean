/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Raw receipt clients

Library `EthConformance`. Private clients check the raw record and both envelope variants
through the Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Conformance.Block.ReceiptCallerProofs

open STFSpec.Base STFSpec.Block STFSpec.Vm.Core

private def receiptConstructorType : Bool → Nat → Bloom → Array Log → Receipt := Receipt.mk
private def succeededType : Receipt → Bool := Receipt.succeeded
private def cumulativeGasUsedType : Receipt → Nat := Receipt.cumulativeGasUsed
private def bloomType : Receipt → Bloom := Receipt.bloom
private def logsType : Receipt → Array Log := Receipt.logs
private def legacyConstructorType : Receipt → EncodedReceipt := EncodedReceipt.legacy
private def typedConstructorType : ByteArray → EncodedReceipt := EncodedReceipt.typed

private def fields (r : Receipt) : Bool × Nat × Bloom × Array Log :=
  (r.succeeded, r.cumulativeGasUsed, r.bloom, r.logs)

private theorem constructor_fields (succeeded : Bool) (gas : Nat) (bloom : Bloom)
    (logs : Array Log) :
    fields (Receipt.mk succeeded gas bloom logs) = (succeeded, gas, bloom, logs) := rfl

private theorem receipt_reconstruct (r : Receipt) :
    Receipt.mk r.succeeded r.cumulativeGasUsed r.bloom r.logs = r := rfl

private theorem update_succeeded (r : Receipt) (succeeded : Bool) :
    fields { r with succeeded := succeeded } =
      (succeeded, r.cumulativeGasUsed, r.bloom, r.logs) := rfl

private theorem update_cumulativeGasUsed (r : Receipt) (gas : Nat) :
    fields { r with cumulativeGasUsed := gas } = (r.succeeded, gas, r.bloom, r.logs) := rfl

private theorem update_bloom (r : Receipt) (bloom : Bloom) :
    fields { r with bloom := bloom } = (r.succeeded, r.cumulativeGasUsed, bloom, r.logs) := rfl

private theorem update_logs (r : Receipt) (logs : Array Log) :
    fields { r with logs := logs } = (r.succeeded, r.cumulativeGasUsed, r.bloom, logs) := rfl

private def payload (encoded : EncodedReceipt) : Receipt ⊕ ByteArray :=
  match encoded with
  | .legacy r => .inl r
  | .typed b => .inr b

private theorem legacy_payload (r : Receipt) : payload (.legacy r) = .inl r := rfl

private theorem typed_payload (b : ByteArray) : payload (.typed b) = .inr b := rfl

private theorem envelope_reconstruct (encoded : EncodedReceipt) :
    (match payload encoded with
      | .inl r => EncodedReceipt.legacy r
      | .inr b => EncodedReceipt.typed b) = encoded := by
  cases encoded <;> rfl

private theorem variants_distinct (r : Receipt) (b : ByteArray) :
    EncodedReceipt.legacy r ≠ EncodedReceipt.typed b := by
  intro equal
  cases equal

end STFSpec.Conformance.Block.ReceiptCallerProofs
