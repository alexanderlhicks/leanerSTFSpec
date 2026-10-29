/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Public raw block parameter clients

Library `EthConformance`. Complete raw construction, reconstruction and updates
through the public Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

open STFSpec.Block

private def constructor_type : Nat → Nat → Nat → BlockParams := BlockParams.mk
private def denominator_type : BlockParams → Nat := BlockParams.baseFeeMaxChangeDenominator
private def elasticity_type : BlockParams → Nat := BlockParams.elasticityMultiplier
private def size_type : BlockParams → Nat := BlockParams.maxRlpBlockSize

private theorem denominator_projection (d e s : Nat) :
    (BlockParams.mk d e s).baseFeeMaxChangeDenominator = d := rfl

private theorem elasticity_projection (d e s : Nat) :
    (BlockParams.mk d e s).elasticityMultiplier = e := rfl

private theorem size_projection (d e s : Nat) :
    (BlockParams.mk d e s).maxRlpBlockSize = s := rfl

private theorem reconstruct (p : BlockParams) :
    BlockParams.mk p.baseFeeMaxChangeDenominator p.elasticityMultiplier p.maxRlpBlockSize = p := rfl

private theorem update_denominator (p : BlockParams) (d : Nat) :
    let q := { p with baseFeeMaxChangeDenominator := d }
    (q.baseFeeMaxChangeDenominator, q.elasticityMultiplier, q.maxRlpBlockSize) =
      (d, p.elasticityMultiplier, p.maxRlpBlockSize) := rfl

private theorem update_elasticity (p : BlockParams) (e : Nat) :
    let q := { p with elasticityMultiplier := e }
    (q.baseFeeMaxChangeDenominator, q.elasticityMultiplier, q.maxRlpBlockSize) =
      (p.baseFeeMaxChangeDenominator, e, p.maxRlpBlockSize) := rfl

private theorem update_size (p : BlockParams) (s : Nat) :
    let q := { p with maxRlpBlockSize := s }
    (q.baseFeeMaxChangeDenominator, q.elasticityMultiplier, q.maxRlpBlockSize) =
      (p.baseFeeMaxChangeDenominator, p.elasticityMultiplier, s) := rfl

private def observe (p : BlockParams) : Nat × Nat × Nat :=
  (p.baseFeeMaxChangeDenominator, p.elasticityMultiplier, p.maxRlpBlockSize)

#guard observe (BlockParams.mk 0 0 0) == (0, 0, 0)
#guard observe (BlockParams.mk 17 29 43) == (17, 29, 43)
#guard observe (BlockParams.mk (2 ^ 256) 0 (2 ^ 512 + 1)) == (2 ^ 256, 0, 2 ^ 512 + 1)
#guard observe (BlockParams.mk 0 (2 ^ 300 + 7) 3) == (0, 2 ^ 300 + 7, 3)
