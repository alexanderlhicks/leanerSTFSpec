/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public transaction state-gas usage clients

Library `EthConformance`. Private callers use only the ordinary public equation.
No caller reachability, transaction conservation or settlement claim follows.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.TxStateGasUsageCallerProofs
open STFSpec.Vm.Core

private theorem ignored_fields (m : GasMeter) (T E B : Nat) (q : Int)
    (h : m.stateGasBaseline ≤ T) (h' : B ≤ T) :
    txStateGasUsed { m with gasLeft := E, stateGasBaseline := B, refundCounter := q }
      T h' = txStateGasUsed m T h := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]

private theorem pending_addition (m : GasMeter) (T a : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed { m with stateGasSpilled := m.stateGasSpilled + a } T h =
      txStateGasUsed m T h + (a : Int) := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  dsimp only
  omega

private theorem committed_addition (m : GasMeter) (T a : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed { m with stateGasCommittedSpill := m.stateGasCommittedSpill + a } T h =
      txStateGasUsed m T h + (a : Int) := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  dsimp only
  omega

private theorem both_spills (m : GasMeter) (T a b : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed
      { m with
        stateGasSpilled := m.stateGasSpilled + a,
        stateGasCommittedSpill := m.stateGasCommittedSpill + b } T h =
      txStateGasUsed m T h + (a : Int) + (b : Int) := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  dsimp only
  omega

private theorem grant_addition (m : GasMeter) (T a : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed m (T + a) (by omega) = txStateGasUsed m T h + (a : Int) := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  omega

private theorem reservoir_addition (m : GasMeter) (T a : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed { m with stateGasLeft := m.stateGasLeft + a } T h =
      txStateGasUsed m T h - (a : Int) := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  dsimp only
  omega

private theorem grant_mono (m : GasMeter) (T U : Nat)
    (hT : m.stateGasBaseline ≤ T) (hU : m.stateGasBaseline ≤ U) (h : T ≤ U) :
    txStateGasUsed m T hT ≤ txStateGasUsed m U hU := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  omega

private theorem reservoir_antitone (m : GasMeter) (T R : Nat)
    (h : m.stateGasBaseline ≤ T) (hR : m.stateGasLeft ≤ R) :
    txStateGasUsed { m with stateGasLeft := R } T h ≤ txStateGasUsed m T h := by
  rw [txStateGasUsed_eq, txStateGasUsed_eq]
  dsimp only
  omega

private theorem negative_usage :
    txStateGasUsed
      { gasLeft := 13, stateGasLeft := 21, stateGasBaseline := 9, refundCounter := 99,
        stateGasSpilled := 3, stateGasCommittedSpill := 5 }
      10 (by decide) = -3 := by
  rw [txStateGasUsed_eq]
  decide

end STFSpec.Conformance.Vm.Core.TxStateGasUsageCallerProofs
