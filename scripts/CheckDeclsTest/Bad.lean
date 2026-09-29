/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import Std.Tactic.BVDecide

/-! Deliberate violations: `check-decls` must report every one of them (see `scripts/test_checks.sh`). -/

namespace CheckDeclsTest.Bad

def usesSorry : Nat := sorry

theorem usesNativeDecide : 2 + 2 = 4 := by native_decide

axiom bogus : False

unsafe def unsafeDef : Nat := 0

partial def loops (n : Nat) : Nat := loops n

def slow (n : Nat) : Nat := n
def fastUnsafe (n : Nat) : Nat := n
attribute [implemented_by fastUnsafe] slow

@[extern "check_decls_test_ext"] opaque ext : Nat → Nat

def f (n : Nat) : Nat := n
def g (n : Nat) : Nat := n + 0
@[csimp] theorem f_eq_g : @f = @g := sorry

end CheckDeclsTest.Bad

namespace CheckDeclsTest.Bad
/-- `bv_decide` adds a native-evaluation axiom (`…._native.bv_decide.ax_…`); banned (D21). -/
theorem usesBvDecide (x y : BitVec 8) : x &&& y = y &&& x := by bv_decide
end CheckDeclsTest.Bad

namespace CheckDeclsTest.Bad
/-- `decide +native` also adds a native-evaluation axiom; judged by dependencies, not spelling (D21). -/
theorem usesDecideNative : 2 ^ 20 + 1 = 1048577 := by decide +native
end CheckDeclsTest.Bad
