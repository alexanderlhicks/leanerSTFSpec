/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Private ordinary preparation-failure gas handoff

Library `EthConformance`. These public-law compositions retain the local preparation
assertions and ordinary admission hypotheses; they implement no Runner or checked cast.
Pinned EELS `src/ethereum/forks/amsterdam/vm/interpreter.py:267–294`,
`vm/gas.py:555–603,674–675,1120–1243`.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7/10.
-/

namespace STFSpec.Conformance.Vm.Core.PreparationFailureGasCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def afterPreparation (m : GasMeter) (R₀ : Nat)
    (hBaseline : m.stateGasBaseline ≤ R₀) (hRefund : m.refundCounter = 0) : GasMeter :=
  forfeitRemainingGas (restoreStateGasToEntry m R₀ hBaseline hRefund)
    (restoreStateGasToEntry_post m R₀ hBaseline hRefund).1

-- PF1: complete erasure of execution and both spill pools, with the entry reservoir restored.
private theorem partial_complete (m : GasMeter) (R₀ : Nat)
    (hBaseline : m.stateGasBaseline ≤ R₀) (hRefund : m.refundCounter = 0) :
    afterPreparation m R₀ hBaseline hRefund = GasMeter.mk 0 R₀ R₀ 0 0 0 := by
  unfold afterPreparation
  rw [forfeitRemainingGas_eq, restoreStateGasToEntry_eq]
  cases m
  simp only at hRefund
  simp only [hRefund]

private abbrev entryMeter (a : EvmGasAllocation) : GasMeter :=
  GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0

-- PF2: constructing the ordinary entry meter gives the same complete result as any partial meter.
private theorem entry_agreement (cfg : VmConfig) (T I : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (m : GasMeter)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hRefund : m.refundCounter = 0) :
    let a := allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap
    afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 a.stateGasReservoir a.stateGasReservoir 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        afterPreparation m a.stateGasReservoir hBaseline hRefund := by
  dsimp only
  refine ⟨partial_complete _ _ _ _, ?_⟩
  exact (partial_complete _ _ _ _).trans (partial_complete m _ hBaseline hRefund).symm

private theorem reservoir_le (cfg : VmConfig) (T I : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit) :
    (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir ≤ T := by
  rw [allocateEvmGas_eq]
  dsimp only
  omega

private theorem final_baseline (m : GasMeter) (R₀ : Nat)
    (hBaseline : m.stateGasBaseline ≤ R₀) (hRefund : m.refundCounter = 0) :
    (afterPreparation m R₀ hBaseline hRefund).stateGasBaseline ≤ R₀ := by
  rw [partial_complete]
  exact Nat.le_refl _

private theorem final_state_zero (m : GasMeter) (R₀ : Nat)
    (hBaseline : m.stateGasBaseline ≤ R₀) (hRefund : m.refundCounter = 0) :
    txStateGasUsed (afterPreparation m R₀ hBaseline hRefund) R₀
      (final_baseline m R₀ hBaseline hRefund) = 0 := by
  rw [txStateGasUsed_eq, partial_complete]
  dsimp only
  omega

-- PF3: the observer, unsigned range and existing checked reconstruction follow locally.
private theorem final_observations (cfg : VmConfig) (T I : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (m : GasMeter)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hRefund : m.refundCounter = 0) :
    let R₀ := (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir
    let g := afterPreparation m R₀ hBaseline hRefund
    R₀ ≤ T ∧ g.stateGasBaseline ≤ R₀ ∧
      txStateGasUsed g R₀ (final_baseline m R₀ hBaseline hRefund) = 0 ∧
      g.refundCounter = 0 ∧ 0 ≤ g.refundCounter ∧ g.refundCounter < (2 : Int) ^ 256 ∧
      U256.ofNat? g.refundCounter.toNat = some U256.zero ∧
      U256.zero.toNat = g.refundCounter.toNat := by
  dsimp only
  refine ⟨reservoir_le cfg T I hIntrinsicTx hIntrinsicCap,
    final_baseline m _ hBaseline hRefund, final_state_zero m _ hBaseline hRefund, ?_⟩
  rw [partial_complete]
  dsimp only
  have hz := U256.toNat_zero
  have hc := U256.ofNat?_toNat U256.zero
  rw [hz] at hc
  exact ⟨rfl, by decide, by decide, hc, hz⟩

private theorem final_returned (cfg : VmConfig) (T I : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (m : GasMeter)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hRefund : m.refundCounter = 0) :
    let R₀ := (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir
    let g := afterPreparation m R₀ hBaseline hRefund
    g.gasLeft + g.stateGasLeft ≤ T := by
  dsimp only
  rw [partial_complete]
  rw [Nat.zero_add]
  exact reservoir_le cfg T I hIntrinsicTx hIntrinsicCap

private def settlePreparation (cfg : VmConfig) (T I F : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (hFloor : F ≤ T) (m : GasMeter)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hRefund : m.refundCounter = 0) : TransactionGasSettlement :=
  let R₀ := (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir
  let g := afterPreparation m R₀ hBaseline hRefund
  settleTransactionGas T F g.gasLeft g.stateGasLeft U256.zero
    (txStateGasUsed g R₀ (final_baseline m R₀ hBaseline hRefund))
    (final_returned cfg T I hIntrinsicTx hIntrinsicCap m hBaseline hRefund)
    (by rw [final_state_zero]; exact Nat.zero_le _) hFloor

-- PF4: all settlement premises except the original floor/allocation bounds are derived above.
private theorem settlement_complete (cfg : VmConfig) (T I F : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (hFloor : F ≤ T) (m : GasMeter)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hRefund : m.refundCounter = 0) :
    let a := allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap
    let expected := TransactionGasSettlement.mk (max (T - a.stateGasReservoir) F)
      (T - max (T - a.stateGasReservoir) F) (max (T - a.stateGasReservoir) F) 0
    settlePreparation cfg T I F hIntrinsicTx hIntrinsicCap hFloor m hBaseline hRefund =
        expected ∧
      settlePreparation cfg T I F hIntrinsicTx hIntrinsicCap hFloor
        (entryMeter a) (Nat.le_refl _) rfl = expected := by
  dsimp only
  constructor <;>
    unfold settlePreparation <;>
    rw [settleTransactionGas_eq, final_state_zero, partial_complete, U256.toNat_zero] <;>
    dsimp only <;>
    rw [Nat.min_zero, Int.toNat_zero] <;>
    repeat rw [Nat.sub_zero]

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC01 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
    let a := allocateEvmGas c 0 0 (by decide) (by change 0 ≤ 0; decide)
    let m := GasMeter.mk 0 0 0 0 0 0
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 0 ≤ 0
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 0 0 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 0 0 0 0 0 ∧
      settlePreparation c 0 0 0 (by decide) (by change 0 ≤ 0; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 0 0 0 0 ∧
      settlePreparation c 0 0 0 (by decide) (by change 0 ≤ 0; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 0 0 0 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
      0 0 (by decide) (by change 0 ≤ 0; decide)).stateGasReservoir = 0 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
    0 0 0 (by decide) (by change 0 ≤ 0; decide) (by decide) (GasMeter.mk 0 0 0 0 0 0)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC02 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
    let a := allocateEvmGas c 10 2 (by decide) (by change 2 ≤ 7; decide)
    let m := GasMeter.mk 1 9 1 0 4 7
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 1 ≤ 3
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 3 3 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 3 3 0 0 0 ∧
      settlePreparation c 10 2 0 (by decide) (by change 2 ≤ 7; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 7 3 7 0 ∧
      settlePreparation c 10 2 0 (by decide) (by change 2 ≤ 7; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 7 3 7 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
      10 2 (by decide) (by change 2 ≤ 7; decide)).stateGasReservoir = 3 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
    10 2 0 (by decide) (by change 2 ≤ 7; decide) (by decide) (GasMeter.mk 1 9 1 0 4 7)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC03 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
    let a := allocateEvmGas c 10 2 (by decide) (by change 2 ≤ 7; decide)
    let m := GasMeter.mk 1 9 1 0 4 7
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 1 ≤ 3
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 3 3 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 3 3 0 0 0 ∧
      settlePreparation c 10 2 10 (by decide) (by change 2 ≤ 7; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 10 0 10 0 ∧
      settlePreparation c 10 2 10 (by decide) (by change 2 ≤ 7; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 10 0 10 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
      10 2 (by decide) (by change 2 ≤ 7; decide)).stateGasReservoir = 3 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 7 } }
    10 2 10 (by decide) (by change 2 ≤ 7; decide) (by decide) (GasMeter.mk 1 9 1 0 4 7)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC04 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 12 } }
    let a := allocateEvmGas c 10 2 (by decide) (by change 2 ≤ 12; decide)
    let m := GasMeter.mk 8 0 0 0 0 0
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 0 ≤ 0
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 0 0 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 0 0 0 0 0 ∧
      settlePreparation c 10 2 0 (by decide) (by change 2 ≤ 12; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 10 0 10 0 ∧
      settlePreparation c 10 2 0 (by decide) (by change 2 ≤ 12; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 10 0 10 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 12 } }
      10 2 (by decide) (by change 2 ≤ 12; decide)).stateGasReservoir = 0 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 12 } }
    10 2 0 (by decide) (by change 2 ≤ 12; decide) (by decide) (GasMeter.mk 8 0 0 0 0 0)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC05 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 10 } }
    let a := allocateEvmGas c 10 10 (by decide) (by change 10 ≤ 10; decide)
    let m := GasMeter.mk 0 0 0 0 0 0
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 0 ≤ 0
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 0 0 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 0 0 0 0 0 ∧
      settlePreparation c 10 10 0 (by decide) (by change 10 ≤ 10; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 10 0 10 0 ∧
      settlePreparation c 10 10 0 (by decide) (by change 10 ≤ 10; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 10 0 10 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 10 } }
      10 10 (by decide) (by change 10 ≤ 10; decide)).stateGasReservoir = 0 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 10 } }
    10 10 0 (by decide) (by change 10 ≤ 10; decide) (by decide) (GasMeter.mk 0 0 0 0 0 0)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

-- Complete raw arithmetic control; no preparation reachability is asserted.
private theorem pfC06 (cfg : VmConfig) :
    let c := { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
    let a := allocateEvmGas c 10 0 (by decide) (by change 0 ≤ 0; decide)
    let m := GasMeter.mk 0 10 10 0 0 0
    let hBaseline : m.stateGasBaseline ≤ a.stateGasReservoir := by
      dsimp only [a, m]
      rw [allocateEvmGas_eq]
      change 10 ≤ 10
      decide
    afterPreparation m a.stateGasReservoir hBaseline rfl = GasMeter.mk 0 10 10 0 0 0 ∧
      afterPreparation (entryMeter a) a.stateGasReservoir (Nat.le_refl _) rfl =
        GasMeter.mk 0 10 10 0 0 0 ∧
      settlePreparation c 10 0 2 (by decide) (by change 0 ≤ 0; decide) (by decide)
        m hBaseline rfl = TransactionGasSettlement.mk 2 8 2 0 ∧
      settlePreparation c 10 0 2 (by decide) (by change 0 ≤ 0; decide) (by decide)
        (entryMeter a) (Nat.le_refl _) rfl = TransactionGasSettlement.mk 2 8 2 0 := by
  dsimp only
  have hR : (allocateEvmGas
      { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
      10 0 (by decide) (by change 0 ≤ 0; decide)).stateGasReservoir = 10 := by
    rw [allocateEvmGas_eq]
    rfl
  have hs := settlement_complete
    { cfg with costs := { cfg.costs with txMaxGasLimit := 0 } }
    10 0 2 (by decide) (by change 0 ≤ 0; decide) (by decide) (GasMeter.mk 0 10 10 0 0 0)
    (by rw [hR]; decide) rfl
  exact ⟨(partial_complete _ _ _ _).trans (by rw [hR]),
    (partial_complete _ _ _ _).trans (by rw [hR]),
    hs.1.trans (by rw [hR]; rfl), hs.2.trans (by rw [hR]; rfl)⟩

end STFSpec.Conformance.Vm.Core.PreparationFailureGasCallerProofs
