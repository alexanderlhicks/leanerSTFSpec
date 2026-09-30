/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Public RIPEMD-160 compression clients

Library `EthConformance`. Callers compose public equations without unfolding native
storage or branch arithmetic. These are compression clients, without digest, gas or
host capability claims.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3,7–8.
-/

namespace STFSpec.Conformance.Hash.Ripemd160CompressionCallerProofs
open STFSpec.Hash

/-- The returned fixed-word state follows the model at every word position. -/
theorem compression_word (h : Vector UInt32 5) (m : Vector UInt32 16) (i : Fin 5) :
    (ripemd160Compress h m)[i].toBitVec =
      (Ripemd160Model.compress (ripemd160ToModel h) (ripemd160ToModel m))[i] := by
  rw [← ripemd160ToModel_word, ripemd160ToModel_compress]

/-- Two consecutive compressions compose without an extra premise. -/
theorem two_blocks (h : Vector UInt32 5) (m₁ m₂ : Vector UInt32 16) :
    ripemd160ToModel (ripemd160Compress (ripemd160Compress h m₁) m₂) =
      Ripemd160Model.compress
        (Ripemd160Model.compress (ripemd160ToModel h) (ripemd160ToModel m₁))
        (ripemd160ToModel m₂) := by
  rw [ripemd160ToModel_compress, ripemd160ToModel_compress]

/-- A client can substitute equal model observations before compression. -/
theorem compress_congr (h h' : Vector UInt32 5) (m m' : Vector UInt32 16)
    (hh : ripemd160ToModel h = ripemd160ToModel h')
    (hm : ripemd160ToModel m = ripemd160ToModel m') :
    ripemd160Compress h m = ripemd160Compress h' m' := by
  apply ripemd160ToModel_inj
  rw [ripemd160ToModel_compress, ripemd160ToModel_compress, hh, hm]

/-- Public round-prefix correspondence supplies the feedforward model premise. -/
theorem prefix_feedforward (h : Vector UInt32 5) (q : Ripemd160Work)
    (m : Vector UInt32 16) (n : Nat) (hn : n ≤ 80) :
    ripemd160ToModel (ripemd160Feedforward h (ripemd160Rounds q m n hn)) =
      Ripemd160Model.feedforward (ripemd160ToModel h)
        (Ripemd160Model.rounds (ripemd160WorkToModel q) (ripemd160ToModel m) n hn) := by
  rw [ripemd160ToModel_feedforward, ripemd160WorkToModel_rounds]

/-- The word observer supplies a bit-level observation to a future byte adapter. -/
theorem word_bits (h : Vector UInt32 5) (i : Fin 5) (z : Fin 32) :
    ((ripemd160ToModel h)[i]).getLsbD z.val = h[i].toNat.testBit z.val :=
  ripemd160ToModel_bit h i z

/-- Equal complete dual-round model observations determine equal executable states. -/
theorem prefix_ext (a b : Ripemd160Work) (m : Vector UInt32 16) (n : Nat) (hn : n ≤ 80)
    (hab : Ripemd160Model.rounds (ripemd160WorkToModel a) (ripemd160ToModel m) n hn =
      Ripemd160Model.rounds (ripemd160WorkToModel b) (ripemd160ToModel m) n hn) :
    ripemd160Rounds a m n hn = ripemd160Rounds b m n hn := by
  apply ripemd160WorkToModel_inj
  rw [ripemd160WorkToModel_rounds, ripemd160WorkToModel_rounds]
  exact hab

end STFSpec.Conformance.Hash.Ripemd160CompressionCallerProofs
