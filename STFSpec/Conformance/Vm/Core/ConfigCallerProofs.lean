/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public raw VM-configuration clients

Library `EthConformance`. Every client is private.
Construct all supplied fields, consume all six public laws, and retain complete
selected chargeGas results without a premise on unused state costs or limits.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.ConfigCallerProofs
open STFSpec.Vm.Core

private theorem supplied_state_constructor_eta (r n s a : Nat) :
    let c := StateGasCosts.mk r n s a
    (c.costPerStateByte, c.bytesPerNewAccount, c.bytesPerStorageSet, c.bytesPerAuthBase)
        = (r, n, s, a) ∧
      StateGasCosts.mk c.costPerStateByte c.bytesPerNewAccount
        c.bytesPerStorageSet c.bytesPerAuthBase = c := by
  constructor
  · rfl
  · exact StateGasCosts.eta _

private theorem supplied_limits_constructor_eta (d c i : Nat) :
    let limits := VmLimits.mk d c i
    (limits.stackDepthLimit, limits.maxCodeSize, limits.maxInitCodeSize) = (d, c, i) ∧
      VmLimits.mk limits.stackDepthLimit limits.maxCodeSize limits.maxInitCodeSize = limits := by
  constructor
  · rfl
  · exact VmLimits.eta _

private theorem supplied_config_constructor_eta
    (costs : GasCosts) (stateCosts : StateGasCosts) (limits : VmLimits) :
    let cfg := VmConfig.mk costs stateCosts limits
    (cfg.costs, cfg.stateCosts, cfg.limits) = (costs, stateCosts, limits) ∧
      VmConfig.mk cfg.costs cfg.stateCosts cfg.limits = cfg := by
  constructor
  · rfl
  · exact VmConfig.eta _

private theorem public_state_ext (a b : StateGasCosts)
    (hr : a.costPerStateByte = b.costPerStateByte)
    (hn : a.bytesPerNewAccount = b.bytesPerNewAccount)
    (hs : a.bytesPerStorageSet = b.bytesPerStorageSet)
    (ha : a.bytesPerAuthBase = b.bytesPerAuthBase) : a = b := by
  exact StateGasCosts.ext a b hr hn hs ha

private theorem public_limits_ext (a b : VmLimits)
    (hd : a.stackDepthLimit = b.stackDepthLimit)
    (hc : a.maxCodeSize = b.maxCodeSize)
    (hi : a.maxInitCodeSize = b.maxInitCodeSize) : a = b := by
  exact VmLimits.ext a b hd hc hi

private theorem public_config_ext (a b : VmConfig)
    (hc : a.costs = b.costs) (hs : a.stateCosts = b.stateCosts)
    (hl : a.limits = b.limits) : a = b := by
  exact VmConfig.ext a b hc hs hl

-- Two arbitrary full configurations may disagree on every unselected field.
private theorem selected_config_charge_congr (a b : VmConfig) (g : GasMeter)
    (h : a.costs.opcodeAdd = b.costs.opcodeAdd) :
    chargeGas g a.costs.opcodeAdd = chargeGas g b.costs.opcodeAdd := by
  exact congrArg (chargeGas g) h

-- Explicitly varying all unused record arguments leaves the complete result equal.
private theorem unused_state_limits_charge
    (costs : GasCosts) (s t : StateGasCosts) (l k : VmLimits) (g : GasMeter) :
    chargeGas g (VmConfig.mk costs s l).costs.opcodeAdd =
      chargeGas g (VmConfig.mk costs t k).costs.opcodeAdd := by
  rfl

private theorem selected_config_charge_success (cfg : VmConfig) (g : GasMeter)
    (h : cfg.costs.opcodeAdd ≤ g.gasLeft) :
    chargeGas g cfg.costs.opcodeAdd =
      .ok { g with gasLeft := g.gasLeft - cfg.costs.opcodeAdd } := by
  exact chargeGas_of_le g cfg.costs.opcodeAdd h

private theorem selected_config_charge_error
    (cfg : VmConfig) (g : GasMeter) (e : ExceptionalHalt) :
    chargeGas g cfg.costs.opcodeAdd = .error e ↔
      g.gasLeft < cfg.costs.opcodeAdd ∧ e = .outOfGas := by
  exact chargeGas_eq_error_iff g cfg.costs.opcodeAdd e

end STFSpec.Conformance.Vm.Core.ConfigCallerProofs
