/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import Lean

/-!
A kernel bypass from an elaboration-time metaprogram (see `scripts/test_checks.sh`).

The `#eval` adds a theorem of `False` with `debug.skipKernelTC` set, so the kernel never
checks it; `oneEqTwo` then proves `1 = 2` from it. Elaboration and `lake build --wfail`
succeed, and `#print axioms oneEqTwo` reports no axioms.

`check-decls` cannot see this, and its fixture test pins that it reports nothing: it reads
the compiled environment and judges each declaration by its axiom dependencies, which are
empty here, never re-checking a proof. Kernel replay rejects it (`lake env leanchecker`;
`scripts/replay_kernel.sh` runs it in CI over every library module), and that is the soundness
check. In the core, `scripts/check_boundaries.py` also rejects this file, for its `import Lean`,
its `#eval` and its `skipKernelTC` token; the test plants it in a scratch core tree to show
that. Those source checks are tripwires: a macro expanding to `#eval`, or an option name built
from strings, evades the token checks.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  liftCoreM <| withOptions (fun o => o.setBool `debug.skipKernelTC true) do
    addDecl <| .thmDecl {
      name := `CheckDeclsTest.KernelBypass.bad, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro }

namespace CheckDeclsTest.KernelBypass

theorem oneEqTwo : (1 : Nat) = 2 := bad.elim

end CheckDeclsTest.KernelBypass
