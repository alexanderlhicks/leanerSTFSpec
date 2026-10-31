/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.GasMeter
import STFSpec.Vm.Core.Sets
import STFSpec.Vm.Core.SatisfiesM

/-!
# Shared precompile result and certified table carriers

Library `EthVmCore`. Source-free calling convention and proof fields shared by
precompile producers and consumers. Actual entries, installation, effect bridges
and halt settlement are separate obligations.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- A successful complete meter/output pair or a nominal exceptional halt. -/
inductive PrecompileResult where
  /-- Successful completion with the returned meter and output bytes. -/
  | ok (meter : GasMeter) (output : Bytes)
  /-- A nominal exceptional halt, settled by the caller. -/
  | halt (e : ExceptionalHalt)

/-- Raw monadic precompile calling convention; no hash-query instance is required. -/
abbrev PrecompileFn (m : Type → Type) := Bytes → GasMeter → m PrecompileResult

/-- Success can only decrease execution gas, preserving every other meter field.
Output is unrestricted, and a halt imposes no meter or settlement condition. -/
def MeterOk (g : GasMeter) : PrecompileResult → Prop
  | .ok g' _ => g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g
  | .halt _ => True

/-- A supplied lookup domain and an actual action-factorization witness per entry.
Only the exact `Id` law interprets this proof field as a result predicate here. -/
structure PrecompileTable (m : Type → Type) [Monad m] where
  /-- The installed entry, if any, at each address. -/
  lookup : Address → Option (PrecompileFn m)
  /-- The supplied lookup domain. -/
  addresses : AddrSet
  /-- Lookup succeeds exactly on the supplied domain. -/
  lookup_iff : ∀ a, (lookup a).isSome ↔ a ∈ addresses
  /-- Every installed entry has an action-factorization witness for `MeterOk`. -/
  meter_law : ∀ a p i g, lookup a = some p → SatisfiesM (MeterOk g) (p i g)

end STFSpec.Vm.Core
