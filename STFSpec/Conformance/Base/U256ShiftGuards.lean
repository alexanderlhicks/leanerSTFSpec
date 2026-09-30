/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 shift-composition regression guards

Library `EthConformance`: deterministic amount boundaries and both sign patterns.
The matrix covers zero amounts, saturation, and nonwrapping word-sized amounts.
Wrapping maximum plus one gives explicit counterexamples outside the premise.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

private def signPatterns : List U256 :=
  [U256.zero, U256.one, U256.ofNat (2 ^ 255 - 1), U256.ofNat (2 ^ 255),
    U256.ofNat (2 ^ 255 + 1), U256.ofNat (2 ^ 256 - 3), U256.max,
    U256.ofNat 0xaa55aa55]

private def amountPairs : List (Nat × Nat) :=
  [(0, 0), (0, 1), (1, 0), (0, 255), (255, 0), (1, 254), (254, 1),
    (127, 128), (128, 127), (1, 255), (128, 128), (256, 0), (0, 256),
    (2 ^ 255, 2 ^ 255 - 1), (2 ^ 256 - 1, 0)]

#guard amountPairs.all (fun (s, t) ↦ signPatterns.all (fun v ↦
  U256.shl (U256.ofNat t) (U256.shl (U256.ofNat s) v) =
    U256.shl (U256.add (U256.ofNat s) (U256.ofNat t)) v))
#guard amountPairs.all (fun (s, t) ↦ signPatterns.all (fun v ↦
  U256.shr (U256.ofNat t) (U256.shr (U256.ofNat s) v) =
    U256.shr (U256.add (U256.ofNat s) (U256.ofNat t)) v))
#guard amountPairs.all (fun (s, t) ↦ signPatterns.all (fun v ↦
  U256.sar (U256.ofNat t) (U256.sar (U256.ofNat s) v) =
    U256.sar (U256.add (U256.ofNat s) (U256.ofNat t)) v))
#guard U256.add U256.max U256.one = U256.zero
#guard U256.shl U256.one (U256.shl U256.max U256.one) = U256.zero
#guard U256.shl (U256.add U256.max U256.one) U256.one = U256.one
#guard U256.shr U256.one (U256.shr U256.max U256.one) = U256.zero
#guard U256.shr (U256.add U256.max U256.one) U256.one = U256.one
#guard U256.sar U256.one (U256.sar U256.max (U256.ofNat (2 ^ 255))) = U256.max
#guard U256.sar (U256.add U256.max U256.one) (U256.ofNat (2 ^ 255)) =
  U256.ofNat (2 ^ 255)
