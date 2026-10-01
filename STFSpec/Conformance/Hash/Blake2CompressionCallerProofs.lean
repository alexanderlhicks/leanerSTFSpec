/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Blake2Compression

/-!
# BLAKE2b compression clients

Library `EthConformance`. These proofs use exported model/operation equations,
without unfolding the native path or any provider's storage.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §7.
-/

namespace STFSpec.Conformance.Hash.Blake2Compression
open STFSpec.Hash.Blake2b

-- No premise restricts index aliasing.
example (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) :
    wordsModel (G v a b c d x y) =
      Model.G (wordsModel v) a b c d x.toBitVec y.toBitVec :=
  wordsModel_G v a b c d x y

example (v candidate : Vector UInt64 16) (a : Fin 16) (x y : UInt64)
    (he : wordsModel candidate = Model.G (wordsModel v) a a a a x.toBitVec y.toBitVec) :
    candidate = G v a a a a x y := by
  apply wordsModel_injective
  rw [he, wordsModel_G]

example (m v : Vector UInt64 16) (n k start : Nat) :
    wordsModel (rounds m (n + k) start v) =
      Model.rounds (wordsModel m) k (start + n)
        (Model.rounds (wordsModel m) n start (wordsModel v)) := by
  rw [rounds_add, wordsModel_rounds, wordsModel_rounds]

example (m v : Vector UInt64 16) (n : Nat) :
    wordsModel (rounds m (n + 1) 0 v) =
      Model.round (wordsModel m) (Model.rounds (wordsModel m) n 0 (wordsModel v)) n := by
  rw [rounds_succ, wordsModel_round, wordsModel_rounds, Nat.zero_add]

example (n : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t0 t1 : UInt64) (f : Bool) :
    compress n h m t0 t1 f =
      Model.compress n (wordsModel h) (wordsModel m) t0.toBitVec t1.toBitVec f :=
  compress_model n h m t0 t1 f

-- This symbolic client covers maxUInt32 without evaluating any compression rounds.
example (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64) (f : Bool) :
    (compress 0xffffffff h m t0 t1 f).size = 64 := compress_size _ _ _ _ _ _

example (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64) (f : Bool) :
    compress 0 h m t0 t1 f = serializeWords (feedForward h (initState h t0 t1 f)) := by
  rw [compress_eq]
  change serializeWords (feedForward h (rounds m 0 0 (initState h t0 t1 f))) = _
  rw [rounds_zero]

example (h : Vector UInt64 8) (v : Vector UInt64 16) (i : Nat) (hi : i < 8) :
    (wordsModel (feedForward h v))[i] =
      h[i].toBitVec ^^^ v[i].toBitVec ^^^ v[i + 8].toBitVec := by
  rw [wordsModel_get, feedForward_get, UInt64.toBitVec_xor, UInt64.toBitVec_xor]

example (x : UInt64) (j : Fin 8) :
    (outputByte x j).toNat = x.toBitVec.toNat / 256 ^ j.val % 256 := by
  rw [outputByte_eq_wordByte, wordByte_toNat]

end STFSpec.Conformance.Hash.Blake2Compression
