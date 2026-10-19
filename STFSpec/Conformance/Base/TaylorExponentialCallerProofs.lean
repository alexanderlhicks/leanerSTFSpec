/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.TaylorExponential

/-!
# Taylor exponential public-law clients

Library `EthConformance`: complete arbitrary-natural results through only the
two public zero-value laws, without unfolding the operation or private loop.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

private theorem zero_factor_result (n d : Nat) (hd : 0 < d) :
    taylorExponential 0 n d hd = 0 := taylorExponential_zero_factor n d hd

private theorem zero_numerator_result (f d : Nat) (hd : 0 < d) :
    taylorExponential f 0 d hd = f := taylorExponential_zero_numerator f d hd

private theorem zero_overlap (d : Nat) (hd : 0 < d) :
    taylorExponential 0 0 d hd = 0 := taylorExponential_zero_numerator 0 d hd

private theorem zero_factor_cross_domain (n m d e : Nat) (hd : 0 < d) (he : 0 < e) :
    taylorExponential 0 n d hd = taylorExponential 0 m e he := by
  rw [taylorExponential_zero_factor, taylorExponential_zero_factor]

private theorem zero_numerator_denominator (f d e : Nat) (hd : 0 < d) (he : 0 < e) :
    taylorExponential f 0 d hd = taylorExponential f 0 e he := by
  rw [taylorExponential_zero_numerator, taylorExponential_zero_numerator]

private theorem zero_numerator_injective (f g d e : Nat) (hd : 0 < d) (he : 0 < e) :
    (taylorExponential f 0 d hd = taylorExponential g 0 e he) ↔ f = g := by
  rw [taylorExponential_zero_numerator, taylorExponential_zero_numerator]

private theorem zero_numerator_nonzero (f d : Nat) (hd : 0 < d) :
    (taylorExponential f 0 d hd ≠ 0) ↔ f ≠ 0 := by
  rw [taylorExponential_zero_numerator]

private theorem zero_factor_as_factor (n m d e : Nat) (hd : 0 < d) (he : 0 < e) :
    taylorExponential (taylorExponential 0 n d hd) m e he = 0 := by
  rw [taylorExponential_zero_factor, taylorExponential_zero_factor]

private theorem zero_factor_as_numerator (f n d e : Nat) (hd : 0 < d) (he : 0 < e) :
    taylorExponential f (taylorExponential 0 n d hd) e he = f := by
  rw [taylorExponential_zero_factor, taylorExponential_zero_numerator]

private theorem zero_numerator_composition (f d e : Nat) (hd : 0 < d) (he : 0 < e) :
    taylorExponential (taylorExponential f 0 d hd) 0 e he = f := by
  rw [taylorExponential_zero_numerator, taylorExponential_zero_numerator]

private theorem proof_witness_independence (f n d : Nat) (hd hd' : 0 < d) :
    taylorExponential f n d hd = taylorExponential f n d hd' := rfl
