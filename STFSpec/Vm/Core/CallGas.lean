/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.GasMeter
import STFSpec.Base.Numeric
import STFSpec.Base.U256

/-!
# Pure call and init-code gas pricing

Library `EthVmCore`. EELS `src/ethereum/forks/amsterdam/vm/gas.py:357–371,816–899`.
These helpers compute amounts, without charging a meter or allocating code.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Call charge excluding memory, followed by the complete child grant. -/
structure MessageCallGas where
  /-- Call charge excluding memory expansion. -/
  cost : Nat
  /-- Complete child grant, including the selected stipend. -/
  subCall : Nat

/-- Equality of both stored fields determines the complete result. -/
theorem MessageCallGas.ext (a b : MessageCallGas)
    (h_cost : a.cost = b.cost) (h_subCall : a.subCall = b.subCall) :
    a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruct the result in source field order. -/
theorem MessageCallGas.eta (r : MessageCallGas) :
    MessageCallGas.mk r.cost r.subCall = r := by
  cases r
  rfl

/-- Select the stipend, test shortage before subtraction, then cap the affordable request.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:816–858`.
The optional argument uses this call's `cfg`; Python's captured default remains
an additional source-correspondence premise. -/
def calculateMessageCallGas (cfg : VmConfig) (value : U256)
    (gas gasLeft memoryCost extraGas : Nat)
    (stipend : Nat := cfg.costs.callStipend) : MessageCallGas :=
  let callStipend := if value = U256.zero then cfg.costs.zero else stipend
  if gasLeft < extraGas + memoryCost then
    MessageCallGas.mk (gas + extraGas) (gas + callStipend)
  else
    let gas := min gas (maxMessageCallGas ((gasLeft - memoryCost) - extraGas))
    MessageCallGas.mk (gas + extraGas) (gas + callStipend)

/-- The full shortage-first equation, on every raw configuration and Nat input. -/
theorem calculateMessageCallGas_eq (cfg : VmConfig) (value : U256)
    (gas gasLeft memoryCost extraGas stipend : Nat) :
    let t := if value = U256.zero then cfg.costs.zero else stipend
    calculateMessageCallGas cfg value gas gasLeft memoryCost extraGas stipend =
      if gasLeft < extraGas + memoryCost then
        MessageCallGas.mk (gas + extraGas) (gas + t)
      else
        let q := min gas
          (maxMessageCallGas ((gasLeft - memoryCost) - extraGas))
        MessageCallGas.mk (q + extraGas) (q + t) := rfl

/-- Only the effective selected stipend affects a fully applied result. -/
theorem calculateMessageCallGas_congr (cfg₁ cfg₂ : VmConfig)
    (value : U256) (gas gasLeft memoryCost extraGas stipend₁ stipend₂ : Nat)
    (h_price :
      (if value = U256.zero then cfg₁.costs.zero else stipend₁) =
      (if value = U256.zero then cfg₂.costs.zero else stipend₂)) :
    calculateMessageCallGas cfg₁ value gas gasLeft memoryCost extraGas stipend₁ =
    calculateMessageCallGas cfg₂ value gas gasLeft memoryCost extraGas stipend₂ := by
  simp only [calculateMessageCallGas]
  rw [h_price]

/-- Multiply the rounded length by its configured price before dividing by 32.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:879–899`.
No buffer, size limit, meter or failure is involved. -/
def initCodeCost (cfg : VmConfig) (n : Nat) : Nat :=
  (cfg.costs.codeInitPerWord * ceil32 n) / 32

/-- Exact source-ordered init pricing on every Nat length and word price. -/
theorem initCodeCost_eq (cfg : VmConfig) (n : Nat) :
    initCodeCost cfg n = (cfg.costs.codeInitPerWord * ceil32 n) / 32 := rfl

/-- Init pricing observes only its per-word price. -/
theorem initCodeCost_congr (cfg₁ cfg₂ : VmConfig)
    (h_price : cfg₁.costs.codeInitPerWord = cfg₂.costs.codeInitPerWord)
    (n : Nat) :
    initCodeCost cfg₁ n = initCodeCost cfg₂ n := by
  simp only [initCodeCost, h_price]

end STFSpec.Vm.Core
