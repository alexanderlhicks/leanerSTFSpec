/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
/-! A clean module: `check-decls` must report nothing. -/

namespace CheckDeclsTest.Good

theorem classical (p : Prop) : p ∨ ¬ p := Classical.em p

def total : Nat → Nat
  | 0 => 0
  | n + 1 => total n

end CheckDeclsTest.Good
