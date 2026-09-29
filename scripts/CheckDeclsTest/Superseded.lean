/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
/-! A superseded unsound compiler replacement must remain detectable. -/

namespace CheckDeclsTest.Superseded
def ref (n : Nat) : Nat := n * 0
def wrong (_ : Nat) : Nat := 1
def right (_ : Nat) : Nat := 0
@[csimp] theorem ref_eq_wrong : @ref = @wrong := sorry
def caller (n : Nat) : Nat := ref n
@[csimp] theorem ref_eq_right : @ref = @right := by funext n; simp [ref, right]
end CheckDeclsTest.Superseded
