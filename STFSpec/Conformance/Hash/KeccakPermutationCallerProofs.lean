/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Keccak permutation caller proofs

Library `EthConformance`: composition through public coordinate-model equations,
without unfolding storage or step implementations. The reference permutation is
only one part of EthHash; sponge, byte packing and query composition remain open.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §7.
-/

open STFSpec.Hash

example (a : KeccakState) :
    keccakToModel (keccakChi (keccakPi (keccakRho (keccakTheta a)))) =
      KeccakModel.chi (KeccakModel.pi (KeccakModel.rho
        (KeccakModel.theta (keccakToModel a)))) := by
  rw [keccakToModel_chi, keccakToModel_pi, keccakToModel_rho, keccakToModel_theta]

example (a : KeccakState) (r : Fin 24) (model : KeccakModel)
    (h : keccakToModel a = model) :
    keccakToModel (keccakRound a r) = KeccakModel.round model r := by
  rw [keccakToModel_round, h]

example (a b : KeccakState) (h : keccakToModel a = keccakToModel b) :
    keccakF1600 a = keccakF1600 b := by
  apply keccakToModel_inj
  rw [keccakToModel_f1600, keccakToModel_f1600, h]

example (a : KeccakState) (model : KeccakModel) (h : keccakToModel a = model)
    (n : Nat) (hn : n ≤ 24) :
    keccakToModel (keccakRounds a n hn) = KeccakModel.rounds model n hn := by
  rw [keccakToModel_rounds, h]

example (a : KeccakState) (x y : Fin 5) :
    keccakLane (keccakPi a) y (keccakCoord x (x.val + 3 * y.val)) =
      keccakLane a x y := keccakLane_pi_forward a x y

example (a : UInt64) (r : Nat) (z : Fin 64) (h : r % 64 ≤ z.val) :
    (keccakRotl a r).toBitVec.getLsbD z.val = a.toBitVec.getLsbD (z.val - r % 64) := by
  rw [keccakRotl_bit, ite_eq_right (Nat.not_lt.mpr h)]
