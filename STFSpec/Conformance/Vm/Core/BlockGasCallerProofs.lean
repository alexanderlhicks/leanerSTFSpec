/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public raw block-gas counter clients

Library `EthConformance`. Private clients retain complete independent execution,
state and blob values through construction, public record laws and Base U64 laws.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.BlockGasCallerProofs
open STFSpec.Vm.Core
open STFSpec.Base

private theorem supplied_constructor (execution state : Nat) (blob : U64) :
    let c := BlockGasCounters.mk execution state blob
    (c.blockGasUsed, c.blockStateGasUsed, c.blobGasUsed) = (execution, state, blob) ∧
      BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed c.blobGasUsed = c := by
  constructor
  · rfl
  · exact BlockGasCounters.eta _

private theorem reconstruct (c : BlockGasCounters) :
    BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed c.blobGasUsed = c := by
  exact BlockGasCounters.eta c

private theorem independent_constructor_ext
    (execution execution' state state' : Nat) (blob blob' : U64)
    (hExecution : execution = execution') (hState : state = state')
    (hBlob : blob = blob') :
    BlockGasCounters.mk execution state blob =
      BlockGasCounters.mk execution' state' blob' := by
  exact BlockGasCounters.ext _ _ hExecution hState hBlob

private theorem observed_ext (a b : BlockGasCounters)
    (hExecution : a.blockGasUsed = b.blockGasUsed)
    (hState : a.blockStateGasUsed = b.blockStateGasUsed)
    (hBlob : a.blobGasUsed.toNat = b.blobGasUsed.toNat) : a = b := by
  exact BlockGasCounters.ext a b hExecution hState (U64.toNat_inj.mp hBlob)

private theorem equal_observations (a b : BlockGasCounters) (h : a = b) :
    (a.blockGasUsed, a.blockStateGasUsed, a.blobGasUsed.toNat) =
      (b.blockGasUsed, b.blockStateGasUsed, b.blobGasUsed.toNat) := by
  exact congrArg
    (fun (c : BlockGasCounters) ↦ (c.blockGasUsed, c.blockStateGasUsed, c.blobGasUsed.toNat)) h

private theorem replace_execution (c : BlockGasCounters) (execution execution' : Nat)
    (h : execution = execution') :
    let a := BlockGasCounters.mk execution c.blockStateGasUsed c.blobGasUsed
    let b := BlockGasCounters.mk execution' c.blockStateGasUsed c.blobGasUsed
    (a.blockGasUsed, a.blockStateGasUsed, a.blobGasUsed) =
      (execution, c.blockStateGasUsed, c.blobGasUsed) ∧ a = b := by
  constructor
  · rfl
  · exact BlockGasCounters.ext _ _ h rfl rfl

private theorem replace_state (c : BlockGasCounters) (state state' : Nat)
    (h : state = state') :
    let a := BlockGasCounters.mk c.blockGasUsed state c.blobGasUsed
    let b := BlockGasCounters.mk c.blockGasUsed state' c.blobGasUsed
    (a.blockGasUsed, a.blockStateGasUsed, a.blobGasUsed) =
      (c.blockGasUsed, state, c.blobGasUsed) ∧ a = b := by
  constructor
  · rfl
  · exact BlockGasCounters.ext _ _ rfl h rfl

private theorem replace_blob (c : BlockGasCounters) (blob blob' : U64)
    (h : blob.toNat = blob'.toNat) :
    let a := BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed blob
    let b := BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed blob'
    (a.blockGasUsed, a.blockStateGasUsed, a.blobGasUsed) =
      (c.blockGasUsed, c.blockStateGasUsed, blob) ∧ a = b := by
  constructor
  · rfl
  · exact BlockGasCounters.ext _ _ rfl rfl (U64.toNat_inj.mp h)

private theorem nested_replacements (c : BlockGasCounters) (execution state : Nat)
    (blob : U64) :
    let a := BlockGasCounters.mk execution c.blockStateGasUsed c.blobGasUsed
    let b := BlockGasCounters.mk a.blockGasUsed state a.blobGasUsed
    let d := BlockGasCounters.mk b.blockGasUsed b.blockStateGasUsed blob
    d = BlockGasCounters.mk execution state blob := by
  exact BlockGasCounters.ext _ _ rfl rfl rfl

private theorem nested_reconstruction (c : BlockGasCounters) :
    BlockGasCounters.mk
      (BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed c.blobGasUsed).blockGasUsed
      c.blockStateGasUsed c.blobGasUsed = c := by
  exact BlockGasCounters.eta c

end STFSpec.Conformance.Vm.Core.BlockGasCallerProofs
