#!/usr/bin/env bash
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
# Regression tests for the checkers themselves: each injected violation must be caught,
# and look-alikes (comments, doc strings) must not be. Run from the repository root.
set -uo pipefail
ROOT=$(pwd); FAIL=0
WORK=$(mktemp -d)
LOG="$WORK/check.log"
ORPHAN=""
ORPHAN_DIR=""
cleanup() {
  if [ -n "$ORPHAN" ]; then rm -f "$ORPHAN"; fi
  if [ -n "$ORPHAN_DIR" ]; then rmdir "$ORPHAN_DIR" 2>/dev/null || true; fi
  rm -rf "$WORK"
}
trap cleanup EXIT
# Each mutation lives under this owned scratch directory.
fresh() { T=$(mktemp -d "$WORK/tree.XXXXXX"); cp -r "$ROOT/STFSpec" "$ROOT/scripts" "$ROOT/lakefile.toml" "$T/"; echo "$T"; }
expect() { # expect <0|1> <description> <dir>
  python3 "$3/scripts/check_boundaries.py" --root "$3" >"$LOG" 2>&1; got=$?
  if [ "$got" -ne "$1" ]; then echo "FAIL: $2 (exit $got, expected $1)"; cat "$LOG"; FAIL=1; else echo "ok:   $2"; fi
  rm -rf "$3"; }

T=$(fresh); expect 0 "clean tree passes" "$T"
T=$(fresh); sed -i 's/roots = \["STFSpec.Base"\]/roots = ["STFSpec.Hash"]/' "$T/lakefile.toml"; expect 1 "Lake roots must match the boundary roots" "$T"
T=$(fresh); printf 'import/- separator -/Mathlib.Tactic\n' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "a comment separating import tokens cannot hide an import" "$T"
T=$(fresh); sed -i 's/^| `EthCurve` | curve groups, ECDSA recover\/verify, MSM | `EthField` |/| `EthCurve` | curve groups, ECDSA recover\/verify, MSM | `EthBase` |/' "$T/STFSpec/informal/ARCHITECTURE.md"; expect 1 "an architecture dependency table that disagrees with boundaries.toml is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Commit' | cat - "$T/STFSpec/State.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/State.lean"; expect 1 "EthState importing EthCommit is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Vm.Runner' | cat - "$T/STFSpec/Vm/Instructions.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Vm/Instructions.lean"; expect 1 "Instructions importing the Runner is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Precompiles' | cat - "$T/STFSpec/Vm/Instructions.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Vm/Instructions.lean"; expect 1 "Instructions importing Precompiles is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Base' | cat - "$T/STFSpec/Block.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Block.lean"; expect 0 "a transitive dependency (Block -> Base) is allowed" "$T"
T=$(fresh); echo 'import Mathlib.Tactic' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "importing Mathlib in the core is rejected" "$T"
T=$(fresh); printf '\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n' >> "$T/lakefile.toml"; expect 1 "a [[require]] in the core lakefile is rejected" "$T"
T=$(fresh); printf '\ndef bad : Nat := sorry\n' >> "$T/STFSpec/Base.lean"; expect 1 "sorry in core code is rejected" "$T"
T=$(fresh); printf '\n-- a comment mentioning sorry, partial def and axiom is fine\n/- so is a /- nested -/ block with native_decide -/\n' >> "$T/STFSpec/Base.lean"; expect 0 "banned words inside comments are ignored" "$T"
T=$(fresh); printf '\ndef s : String := "sorry"\n' >> "$T/STFSpec/Base.lean"; expect 0 "banned words inside string literals are ignored" "$T"
T=$(fresh); printf '\npartial def f (n : Nat) : Nat := f n\n' >> "$T/STFSpec/Hash.lean"; expect 1 "partial def in core is rejected" "$T"
T=$(fresh); printf '\nset_option debug.skipKernelTC true\n' >> "$T/STFSpec/Hash.lean"; expect 1 "skipping the kernel check is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Stray"; echo '' > "$T/STFSpec/Stray/X.lean"; expect 1 "a module outside every declared library is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Base"; printf 'def x : Nat := 0\n' > "$T/STFSpec/Base/Orphan.lean"; expect 1 "a module not imported by its library root is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Base"; printf 'def x : Nat := 0\n' > "$T/STFSpec/Base/Used.lean"; printf 'import STFSpec.Base.Used\n' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 0 "a submodule imported by its root is accepted" "$T"
T=$(fresh); sed -i 's/^deps = \["EthBase"\]$/deps = ["EthBase", "EthHash"]/' "$T/scripts/boundaries.toml"; python3 - "$T" <<'PY'
import sys,re; p=sys.argv[1]+"/scripts/boundaries.toml"; s=open(p).read()
s=s.replace('[libs.EthBase]\nroot = "STFSpec.Base"\ndeps = []','[libs.EthBase]\nroot = "STFSpec.Base"\ndeps = ["EthHash"]'); open(p,"w").write(s)
PY
expect 1 "a dependency cycle in boundaries.toml is rejected" "$T"

# check-decls on its fixtures (needs `lake build CheckDeclsTest check-decls` first).
if lake exe check-decls CheckDeclsTest.Good >"$LOG" 2>&1; then echo "ok:   check-decls passes the clean fixture"; else echo "FAIL: check-decls rejects the clean fixture"; FAIL=1; fi
OUT=$(lake exe check-decls CheckDeclsTest.ProvedCsimp)
if grep -q "^csimp-banned: CheckDeclsTest.ProvedCsimp.f_eq_g" <<<"$OUT"; then echo "ok:   a correctly proved csimp is still rejected (csimp banned, D21)"; else echo "FAIL: a proved csimp is accepted"; FAIL=1; fi
if lake exe check-decls --allow-sory CheckDeclsTest.Good >"$LOG" 2>&1; then echo "FAIL: an unknown option is accepted"; FAIL=1; else echo "ok:   an unknown option is rejected"; fi
OUT=$(lake exe check-decls --allow-sorry CheckDeclsTest.Bad); st=$?
for kind in "axiom: CheckDeclsTest.Bad.bogus" "unsafe: CheckDeclsTest.Bad.unsafeDef" "partial: CheckDeclsTest.Bad.loops" \
            "implemented_by: CheckDeclsTest.Bad.slow" "extern: CheckDeclsTest.Bad.ext" "csimp: CheckDeclsTest.Bad.f_eq_g" \
            "axioms: CheckDeclsTest.Bad.usesNativeDecide" "axioms: CheckDeclsTest.Bad.usesBvDecide" "axioms: CheckDeclsTest.Bad.usesDecideNative"; do
  if grep -q "^$kind" <<<"$OUT"; then echo "ok:   check-decls reports $kind"; else echo "FAIL: check-decls misses $kind"; FAIL=1; fi
done
if [ "$st" -ne 1 ]; then echo "FAIL: check-decls exit $st on the bad fixture"; FAIL=1; fi
if grep -q "usesSorry" <<<"$OUT"; then echo "FAIL: --allow-sorry still reports a plain sorry"; FAIL=1; else echo "ok:   --allow-sorry tolerates a plain sorry (but not a csimp one)"; fi
OUT=$(lake exe check-decls CheckDeclsTest.Bad)
if grep -q "^axioms: CheckDeclsTest.Bad.usesSorry" <<<"$OUT"; then echo "ok:   strict mode reports sorry"; else echo "FAIL: strict mode misses sorry"; FAIL=1; fi
OUT=$(lake exe check-decls --allow-sorry CheckDeclsTest.Superseded)
if grep -q "^csimp: CheckDeclsTest.Superseded.ref_eq_wrong" <<<"$OUT"; then echo "ok:   a superseded unsound csimp is reported (even with --allow-sorry)"; else echo "FAIL: a superseded unsound csimp is missed"; FAIL=1; fi
# An unbuilt module on disk must make the (disk-discovering) declaration check fail.
if [ ! -d STFSpec/Hash ]; then mkdir STFSpec/Hash; ORPHAN_DIR=STFSpec/Hash; fi
ORPHAN=$(mktemp STFSpec/Hash/CheckDeclsOrphanXXXXXX.lean)
printf 'def orphan : Nat := 0\n' > "$ORPHAN"
if scripts/check_decls.sh core >"$LOG" 2>&1; then echo "FAIL: check-decls passes with an unbuilt module on disk"; FAIL=1; else echo "ok:   check-decls fails on an unbuilt module on disk"; fi
rm -f "$ORPHAN"; ORPHAN=""
exit $FAIL
