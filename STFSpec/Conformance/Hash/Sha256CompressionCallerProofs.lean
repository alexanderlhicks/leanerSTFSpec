/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# SHA-256 compression composition clients

Library `EthConformance`. Consumers use public equations and model laws only;
no executable definition or provider representation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §7.
-/

open STFSpec.Hash STFSpec.Hash.Sha256

example (s : Vector UInt32 8) (b1 b2 : Vector UInt32 16) :
    wordsModel (sha256Compress (sha256Compress s b1) b2) =
      Model.compress (Model.compress (wordsModel s) (wordsModel b1)) (wordsModel b2) := by
  rw [sha256Compress_model, sha256Compress_model]

example (w : Vector UInt32 64) (s : Vector UInt32 8) :
    wordsModel (rounds w s 1 (by decide)) =
      Model.round (wordsModel s) roundConstants[0].toBitVec w[0].toBitVec := by
  rw [rounds_succ w s 0 (by decide), rounds_zero, wordsModel_round]

example (b : Vector UInt32 16) (i : Nat) (hi : i < 16) :
    (wordsModel (schedule b))[i] = b[i].toBitVec := by
  rw [wordsModel_get, schedule_get_input b i hi]

example (s : Vector UInt32 8) (b : Vector UInt32 16) (i : Nat) (hi : i < 8) :
    (sha256Compress s b)[i] = s[i] + (rounds (schedule b) s 64 (by decide))[i] := by
  rw [sha256Compress_eq, feedForward_get]

example (s : Vector UInt32 8) (b : Vector UInt32 16)
    (candidate : Vector UInt32 8)
    (h : wordsModel candidate = Model.compress (wordsModel s) (wordsModel b)) :
    candidate = sha256Compress s b := by
  apply wordsModel_injective
  rw [h, sha256Compress_model]
