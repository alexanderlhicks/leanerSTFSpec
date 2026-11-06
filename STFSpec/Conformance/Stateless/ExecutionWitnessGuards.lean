/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete raw execution witness controls

Library `EthConformance`. Small controls inspect every byte and array occurrence.
The quantified clients cover arbitrary lengths without allocating large fixtures.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionWitnessGuards

open STFSpec.Stateless

private def observe (w : ExecutionWitness) :
    List (List UInt8) × List (List UInt8) × List (List UInt8) :=
  (w.state.toList.map (fun b ↦ b.data.toList),
    w.codes.toList.map (fun b ↦ b.data.toList),
    w.headers.toList.map (fun b ↦ b.data.toList))

private def empty : ExecutionWitness := ⟨#[], #[], #[]⟩

private def mixed : ExecutionWitness :=
  ⟨#[⟨#[0, 255, 1, 128]⟩, ⟨#[]⟩, ⟨#[0, 255, 1, 128]⟩],
    #[⟨#[255, 0]⟩],
    #[⟨#[1, 0, 254]⟩, ⟨#[128]⟩, ⟨#[]⟩, ⟨#[1, 0, 254]⟩]⟩

#guard observe empty == ([], [], [])
#guard observe mixed ==
  ([[0, 255, 1, 128], [], [0, 255, 1, 128]],
    [[255, 0]], [[1, 0, 254], [128], [], [1, 0, 254]])
#guard observe { mixed with state := #[⟨#[]⟩] } ==
  ([[]], [[255, 0]], [[1, 0, 254], [128], [], [1, 0, 254]])
#guard observe { mixed with codes := #[⟨#[0, 255]⟩, ⟨#[255, 0]⟩, ⟨#[0, 255]⟩] } ==
  ([[0, 255, 1, 128], [], [0, 255, 1, 128]],
    [[0, 255], [255, 0], [0, 255]], [[1, 0, 254], [128], [], [1, 0, 254]])
#guard observe { mixed with headers := #[⟨#[128]⟩, ⟨#[1, 0, 254]⟩] } ==
  ([[0, 255, 1, 128], [], [0, 255, 1, 128]], [[255, 0]], [[128], [1, 0, 254]])
#guard observe (ExecutionWitness.mk #[⟨#[]⟩] #[] #[]) == ([[]], [], [])
#guard observe (ExecutionWitness.mk #[] #[⟨#[]⟩] #[]) == ([], [[]], [])
#guard observe (ExecutionWitness.mk #[] #[] #[⟨#[]⟩]) == ([], [], [[]])

end STFSpec.Conformance.Stateless.ExecutionWitnessGuards
