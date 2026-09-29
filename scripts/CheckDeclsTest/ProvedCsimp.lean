/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
/-! A correctly proved `@[csimp]`: `check-decls` must still reject it (banned, D21). -/

namespace CheckDeclsTest.ProvedCsimp

def f (n : Nat) : Nat := n + 0
def g (n : Nat) : Nat := n
@[csimp] theorem f_eq_g : @f = @g := by funext n; simp [f, g]

end CheckDeclsTest.ProvedCsimp
