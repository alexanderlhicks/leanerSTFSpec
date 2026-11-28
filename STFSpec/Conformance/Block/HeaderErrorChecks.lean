/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Header error carrier checks

Library `EthConformance`. Check the complete nominal constructor inventory
and order through the Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–4.
-/

namespace STFSpec.Conformance.Block.HeaderErrorChecks

open STFSpec.Block

private def sourceOrder : List HeaderError :=
  [.numberZero, .excessBlobGas, .gasUsedExceedsGasLimit, .gasLimit, .baseFee, .timestamp,
    .number, .extraData, .difficulty, .nonce, .ommersHash, .parentHash]

private theorem constructorOrder :
    sourceOrder.map (fun e ↦ HeaderError.rec (motive := fun _ ↦ Nat) 0 1 2 3 4 5 6 7 8 9 10 11 e) =
      List.range 12 := rfl

private def raiseLine : HeaderError → Nat
  | .numberZero => 446
  | .excessBlobGas => 450
  | .gasUsedExceedsGasLimit => 453
  | .gasLimit => 389
  | .baseFee => 462
  | .timestamp => 464
  | .number => 466
  | .extraData => 468
  | .difficulty => 470
  | .nonce => 472
  | .ommersHash => 474
  | .parentHash => 478

private theorem exhaustive (e : HeaderError) : e ∈ sourceOrder := by
  cases e <;> simp [sourceOrder]

#guard sourceOrder.map raiseLine == [446, 450, 453, 389, 462, 464, 466, 468, 470, 472, 474, 478]

end STFSpec.Conformance.Block.HeaderErrorChecks
