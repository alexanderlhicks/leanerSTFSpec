/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root

/-!
# Universal clients of the longest shared-prefix support slice

Library `EthConformance`. Constructor premises are consumed through the public
`PatricializeDomain` contract. Private scanner law clients live in the Root owner;
these callers do not access private declarations, packed storage or generated
provider equations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.Commit.RootPrefixCallerProofs

open STFSpec.Commit

/-- Future callers consume the public domain fields for child recursion. -/
theorem advanced_child (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (advanced : PatricializeDomain obj (level + amount)) (digit : Fin 16) :
    PatricializeDomain
      (obj.filter (fun k _ ↦
        if h : level + amount < k.size then
          decide (k.get ⟨level + amount, h⟩ = digit) else false))
      (level + amount + 1) := advanced.child digit

/-- Future callers retain full-key bounds and consumed-prefix agreement as public premises. -/
theorem extension_premises (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (advanced : PatricializeDomain obj (level + amount)) :
    (∀ key : Nibbles, key ∈ obj → level + amount ≤ key.size) ∧
      (∀ key : Nibbles, key ∈ obj → ∀ other : Nibbles, other ∈ obj →
        key.take (level + amount) = other.take (level + amount)) :=
  ⟨advanced.depth, advanced.consumedPrefix⟩

end STFSpec.Conformance.Commit.RootPrefixCallerProofs
