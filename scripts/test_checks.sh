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
# The tree's lean-toolchain makes elan run the pinned Lean for Lake's import parser (lean --deps-json).
fresh() { T=$(mktemp -d "$WORK/tree.XXXXXX"); cp -r "$ROOT/STFSpec" "$ROOT/scripts" "$ROOT/lakefile.toml" "$ROOT/lean-toolchain" "$T/"; echo "$T"; }
expect() { # expect <0|1> <description> <dir>
  uv run --no-project --python 3.12 python "$3/scripts/check_boundaries.py" --root "$3" >"$LOG" 2>&1; got=$?
  if [ "$got" -ne "$1" ]; then echo "FAIL: $2 (exit $got, expected $1)"; cat "$LOG"; FAIL=1; else echo "ok:   $2"; fi
  rm -rf "$3"; }
expect_msg() { # expect_msg <description> <dir> <grep pattern>: rejected, with this violation
  uv run --no-project --python 3.12 python "$2/scripts/check_boundaries.py" --root "$2" >"$LOG" 2>&1; got=$?
  if [ "$got" -eq 1 ] && grep -q -- "$3" "$LOG"; then echo "ok:   $1"
  else echo "FAIL: $1 (exit $got; expected a violation matching: $3)"; cat "$LOG"; FAIL=1; fi
  rm -rf "$2"; }
prepend() { # prepend <file> <printf format>: add header text at the top of a module
  printf "$2" | cat - "$1" > "$1.x" && mv "$1.x" "$1"; }

# Declaration diagnostics start on the keyword's line, or on its private/protected modifier.
# Keep the lexer's LF-based line numbering, including for CR and Unicode whitespace.
if uv run --no-project --python 3.12 python -B - "$ROOT/scripts" <<'PY'
import re, sys
sys.path.insert(0, sys.argv[1]); import check_boundaries as cb
bad = []
for keyword in ("axiom", "opaque"):
    cases = [  # (description, source, reported declaration lines)
        ("plain", f"{keyword} forbidden : Nat\n", [1]),
        ("blank lines", f"\n\n\n{keyword} forbidden : Nat\n", [4]),
        ("line comment", f"-- note\n\n{keyword} forbidden : Nat\n", [3]),
        ("long block comment", "/-\n" + "comment\n" * 256 + f"-/\n\n{keyword} forbidden : Nat\n", [260]),
        ("long blank region", " \t\n" * 256 + f"  {keyword} forbidden : Nat\n", [257]),
        ("private", f"\n\tprivate {keyword} forbidden : Nat\n", [2]),
        ("protected", f"\n  protected\t{keyword} forbidden : Nat\n", [2]),
        ("split private", f"\n\nprivate\n  {keyword} forbidden : Nat\n", [3]),
        ("split protected", f"\nprotected\n\n{keyword} forbidden : Nat\n", [2]),
        ("comment after modifier", f"\nprivate /- note\n nested /- x -/ -/\n{keyword} forbidden : Nat\n", [2]),
        ("CRLF", f"\r\n\r\n\t{keyword} forbidden : Nat\r\n", [3]),
        ("CR indentation", f"\r\r{keyword} forbidden : Nat\n", [1]),
        ("CR is not LF", f"def x := 0\r{keyword} forbidden : Nat\n", []),
        ("whitespace indentation", f"\n\t\v\f\r\u0085\u00a0\u2003\u2028\u2029{keyword} forbidden : Nat\n", [2]),
        ("modifier whitespace", f"\nprotected\r\n\u00a0\u2028{keyword} forbidden : Nat\n", [2]),
        ("separate declarations", f"\n{keyword} first : Nat\n\n-- gap\n\t{keyword} second : Nat\n", [2, 5]),
        ("adjacent declarations", f"{keyword} first : Nat\n{keyword} second : Nat\n", [1, 2]),
        ("comment", f"/-\n{keyword} hidden : Nat\n-/\n-- {keyword} hidden : Nat\n", []),
        ("string", f'def s := "\n{keyword} hidden : Nat\n"\n', []),
        ("raw string", f'def s := r#"\n{keyword} hidden : Nat\n"#\n', []),
        ("quoted name", f"def «{keyword}» : Nat := 0\n", []),
        ("longer names", f"{keyword}Count\nprivate {keyword}_name\n", []),
        ("primed keyword tripwire", f"protected {keyword}'\n", [1]),
        ("noninitial keyword", f"def x := {keyword}\n", []),
        ("lookalike before declaration", f'def s := "{keyword}"\n\n{keyword} forbidden : Nat\n', [3]),
    ]
    pattern = next(p for p, what in cb.BANNED if what == keyword)
    for name, src, want in cases:
        code = cb.strip_comments(src)
        got = [code.count("\n", 0, m.start()) + 1 for m in re.finditer(pattern, code, re.M)]
        if got != want:
            bad.append((keyword, name, got, want))
for keyword, name, got, want in bad:
    print(f"FAIL: {keyword} {name}: declaration lines {got}, expected {want}")
sys.exit(1 if bad else 0)
PY
then echo "ok:   axiom and opaque classification and declaration lines"
else FAIL=1; fi

T=$(fresh); expect 0 "clean tree passes" "$T"
T=$(fresh); sed -i 's/roots = \["STFSpec.Base"\]/roots = ["STFSpec.Hash"]/' "$T/lakefile.toml"; expect 1 "Lake roots must match the boundary roots" "$T"
T=$(fresh); printf 'import/- separator -/Mathlib.Tactic\n' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "a comment separating import tokens cannot hide an import" "$T"
T=$(fresh); sed -i 's/^| `EthCurve` | curve groups, ECDSA recover\/verify, MSM | `EthField` |/| `EthCurve` | curve groups, ECDSA recover\/verify, MSM | `EthBase` |/' "$T/STFSpec/informal/ARCHITECTURE.md"; expect 1 "an architecture dependency table that disagrees with boundaries.toml is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Commit' | cat - "$T/STFSpec/State.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/State.lean"; expect 1 "EthState importing EthCommit is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Vm.Runner' | cat - "$T/STFSpec/Vm/Instructions.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Vm/Instructions.lean"; expect 1 "Instructions importing the Runner is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Precompiles' | cat - "$T/STFSpec/Vm/Instructions.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Vm/Instructions.lean"; expect 1 "Instructions importing Precompiles is rejected" "$T"
T=$(fresh); echo 'import STFSpec.Base' | cat - "$T/STFSpec/Block.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Block.lean"; expect 0 "a transitive dependency (Block -> Base) is allowed" "$T"
T=$(fresh); echo 'import Mathlib.Tactic' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "importing Mathlib in the core is rejected" "$T"
# From Lean, only Lean.Data.Json and its submodules (they do not bring addDecl or the elaborator).
T=$(fresh); echo 'import Lean' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "importing all of Lean in the core is rejected" "$T"
T=$(fresh); echo 'import Lean.Elab.Command' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "importing the Lean elaborator in the core is rejected" "$T"
T=$(fresh); echo 'import Lean.Data.JsonRpc' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 1 "a Lean module merely named like the JSON modules is rejected" "$T"
T=$(fresh); printf 'import Lean.Data.Json\nimport Lean.Data.Json.Printer\n' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 0 "importing Lean.Data.Json and its submodules is allowed" "$T"
# Imports come from Lake's import parser: several may share a line, one may span lines, and
# `import` needs no space before a «…» name.
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import«Lean».Elab.Command\n'
expect_msg "an import with no space before a «…» name is rejected" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'module\nimport«Lean».Elab.Command\n'
expect_msg "module, then an import with no space before a «…» name, is rejected" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import Lean.Data.Json import«Lean».Elab.Command\n'
expect_msg "a second, unspaced «…» import on the same line is rejected" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); mkdir -p "$T/STFSpec/Hash"; printf 'import Lean.Data.Json import«Lean».Elab.Command\ndef zzRef := @Lean.addDecl\n' > "$T/STFSpec/Hash/ZZUnspaced.lean"
prepend "$T/STFSpec/Hash.lean" 'import STFSpec.Hash.ZZUnspaced\n'
expect_msg "the same, as a leaf module that names Lean.addDecl" "$T" "STFSpec.Hash.ZZUnspaced: imports Lean.Elab.Command; from Lean"
# The import parser fails closed: an unreadable header or a missing toolchain is a violation.
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import 3\n'
expect_msg "a header Lean cannot read is rejected" "$T" "STFSpec/Base.lean: Lean cannot read the header"
T=$(fresh); rm "$T/lean-toolchain"
uv run --no-project --python 3.12 python "$T/scripts/check_boundaries.py" --root "$T" >"$LOG" 2>&1; got=$?
if [ "$got" -eq 1 ] && grep -q "lean-toolchain is missing" "$LOG" && [ "$(grep -c '^boundary:' "$LOG")" -eq 1 ]; then
  echo "ok:   without lean-toolchain the import parser cannot run: one violation, checks 3 and 3b skipped"
else echo "FAIL: a missing lean-toolchain must give exactly one violation (exit $got, $(grep -c '^boundary:' "$LOG") violations)"; head -5 "$LOG"; FAIL=1; fi
rm -rf "$T"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import Lean.Data.Json import Lean.Elab.Command\n'
expect_msg "a second Lean import on the same line is rejected" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); mkdir -p "$T/STFSpec/Hash"; printf 'import Std import Lean.Elab.Command\ndef zzRef := @Lean.addDecl\n' > "$T/STFSpec/Hash/ZZRef.lean"
prepend "$T/STFSpec/Hash.lean" 'import STFSpec.Hash.ZZRef\n'
expect_msg "a Lean import after Std on the same line is rejected" "$T" "STFSpec.Hash.ZZRef: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import STFSpec.Base.U8 import STFSpec.Vm.Runner\n'
expect_msg "a second core import on the same line is checked against the closure" "$T" "STFSpec.Base (EthBase): imports STFSpec.Vm.Runner (EthVmRunner), not in the allowed closure"
T=$(fresh); prepend "$T/STFSpec/Hash.lean" 'import Std import STFSpec.Field\n'
expect_msg "a core import after Std on the same line is checked against the closure" "$T" "STFSpec.Hash (EthHash): imports STFSpec.Field (EthField), not in the allowed closure"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import\n  Lean.Elab.Command\n'
expect_msg "an import split across lines is rejected" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import Lean.Data.Json /- a comment -/ import Lean.Elab.Command\n'
expect_msg "a comment between imports on one line does not hide the second" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'module\npublic meta import all Lean.Elab.Command\n'
expect_msg "module, public, meta and all do not hide an import" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); prepend "$T/STFSpec/Base.lean" 'import «Lean».Elab.Command\n'
expect_msg "a guillemet-quoted import name is read as Lean reads it" "$T" "STFSpec.Base: imports Lean.Elab.Command; from Lean"
T=$(fresh); mkdir -p "$T/STFSpec/Base"; printf 'def zzUsed : Nat := 0\n' > "$T/STFSpec/Base/ZZUsed.lean"
prepend "$T/STFSpec/Base.lean" 'import STFSpec.Base.U8 import STFSpec.Base.ZZUsed\n'
expect 0 "a module imported second on a line counts as reachable from its root" "$T"
T=$(fresh); printf '\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n' >> "$T/lakefile.toml"; expect 1 "a [[require]] in the core lakefile is rejected" "$T"
T=$(fresh); printf '\ndef bad : Nat := sorry\n' >> "$T/STFSpec/Base.lean"; expect 1 "sorry in core code is rejected" "$T"
T=$(fresh); printf '\n-- a comment mentioning sorry, partial def and axiom is fine\n/- so is a /- nested -/ block with native_decide -/\n' >> "$T/STFSpec/Base.lean"; expect 0 "banned words inside comments are ignored" "$T"
T=$(fresh); printf '\ndef s : String := "sorry"\n' >> "$T/STFSpec/Base.lean"; expect 0 "banned words inside string literals are ignored" "$T"
T=$(fresh); printf '\npartial def f (n : Nat) : Nat := f n\n' >> "$T/STFSpec/Hash.lean"; expect 1 "partial def in core is rejected" "$T"
T=$(fresh); printf '\nset_option debug.skipKernelTC true\n' >> "$T/STFSpec/Hash.lean"; expect 1 "skipping the kernel check is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Stray"; echo '' > "$T/STFSpec/Stray/X.lean"; expect 1 "a module outside every declared library is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Base"; printf 'def x : Nat := 0\n' > "$T/STFSpec/Base/Orphan.lean"; expect 1 "a module not imported by its library root is rejected" "$T"
T=$(fresh); mkdir -p "$T/STFSpec/Base"; printf 'def x : Nat := 0\n' > "$T/STFSpec/Base/Used.lean"; printf 'import STFSpec.Base.Used\n' | cat - "$T/STFSpec/Base.lean" > "$T/x" && mv "$T/x" "$T/STFSpec/Base.lean"; expect 0 "a submodule imported by its root is accepted" "$T"
T=$(fresh); sed -i 's/^deps = \["EthBase"\]$/deps = ["EthBase", "EthHash"]/' "$T/scripts/boundaries.toml"; uv run --no-project --python 3.12 python - "$T" <<'PY'
import sys,re; p=sys.argv[1]+"/scripts/boundaries.toml"; s=open(p).read()
s=s.replace('[libs.EthBase]\nroot = "STFSpec.Base"\ndeps = []','[libs.EthBase]\nroot = "STFSpec.Base"\ndeps = ["EthHash"]'); open(p,"w").write(s)
PY
expect 1 "a dependency cycle in boundaries.toml is rejected" "$T"

# Check 4b, a tripwire for obvious elaboration-time metaprograms, and the literal `skipKernelTC`
# (kernel replay, tested below, is the soundness check; 4b is evadable, e.g. by a macro).
plant() { # plant <tree> <module>: add STFSpec.Hash.<module> to the EthHash root's imports
  printf 'import STFSpec.Hash.%s\n' "$2" | cat - "$1/STFSpec/Hash.lean" > "$1/x" && mv "$1/x" "$1/STFSpec/Hash.lean"; }
T=$(fresh); mkdir -p "$T/STFSpec/Hash"; cp "$ROOT/scripts/CheckDeclsTest/KernelBypass.lean" "$T/STFSpec/Hash/KernelBypass.lean"
plant "$T" KernelBypass
uv run --no-project --python 3.12 python "$T/scripts/check_boundaries.py" --root "$T" >"$LOG" 2>&1; got=$?
for what in "STFSpec/Hash/KernelBypass.lean:[0-9]*: banned in core: #eval" \
            "STFSpec/Hash/KernelBypass.lean:[0-9]*: banned in core: skipKernelTC" \
            "STFSpec.Hash.KernelBypass: imports Lean; from Lean"; do
  if [ "$got" -eq 1 ] && grep -q "^boundary: $what" "$LOG"; then
    echo "ok:   the kernel-bypass fixture planted in the core is rejected: $what"
  else echo "FAIL: the kernel-bypass fixture planted in the core is not rejected: $what (exit $got)"; cat "$LOG"; FAIL=1; fi
done
rm -rf "$T"
# One planted module: every line marked `-- BAN` must be reported, and no other line. The
# unmarked lines are look-alikes, and literals that must not hide the code after them.
T=$(fresh); mkdir -p "$T/STFSpec/Hash"; MOD="$T/STFSpec/Hash/Metaprograms.lean"
cat > "$MOD" <<'LEAN'
#eval 1 -- BAN
#eval! (1 : Nat) -- BAN
run_cmd pure () -- BAN
run_elab pure () -- BAN
run_meta pure () -- BAN
example : True := by run_tac pure () -- BAN
example : Nat := by_elab pure (Lean.mkNatLit 0) -- BAN
elab "zz" : term => pure (Lean.mkNatLit 0) -- BAN
scoped elab "zz" : term => pure (Lean.mkNatLit 0) -- BAN
elab_rules : term | `(zz) => pure (Lean.mkNatLit 0) -- BAN
initialize pure () -- BAN
builtin_initialize pure () -- BAN
@[init zzInit] def zzA : Nat := 0 -- BAN
attribute [builtin_init zzInit] zzA -- BAN
@[command_elab zzKind] def zzB : Unit := () -- BAN
@[term_elab zzKind] def zzC : Unit := () -- BAN
@[inline, tactic zzKind] def zzD : Unit := () -- BAN
simproc zzE (Nat.succ _) := fun _ => pure .continue -- BAN
dsimproc_decl zzF (Nat.succ _) := fun _ => pure .continue -- BAN
set_option debug.skipKernelTC true in -- BAN
def zzG := `debug.skipKernelTC -- BAN
def zzH := `debug.«skipKernelTC» -- BAN
def zzI := "debug.skipKernelTC" -- BAN
def zzJ := (fun (o : Lean.Options) => o.setBool `debug.skipKernelTC true) -- BAN
def zzO := s!"{sorry}" -- BAN
def zzK : Char := '"'
#eval 2 -- BAN
def zzL := r"\"
#eval 3 -- BAN
def zzM := r#"a"b"#
#eval 4 -- BAN
def zzN := s!"{'"'}"
#eval 5 -- BAN
def «zzq"» : Nat := 0
#eval 6 -- BAN
def «/-» : Nat := 0
#eval 7 -- BAN
def «--» : Nat := by_elab pure (Lean.mkNatLit 0) -- BAN
def zzS : Bool := !'"'.isAlpha
#eval 8 -- BAN
def zzT : Bool := ?'"'
#eval 9 -- BAN
def zzU := s! "{sorry}" -- BAN
def zzV : Nat := dbg_trace "{sorry}"; 0 -- BAN
def «elab» : Nat := 0
def foo!'a' : Nat := 0
def zzW (x' : Nat) : Char := if x' = 0 then 'a' else '"'
#eval 10 -- BAN
@[deprecated init (since := "2026-01-01")] def zzX : Nat := 0
@[simp, deprecated tactic] def zzY : Nat := 0
@[«init» f] def zzZ : Nat := 0 -- BAN
@[simp, «tactic» k] def zzZ2 : Nat := 0 -- BAN
-- #eval, run_cmd, elab, initialize and skipKernelTC in a line comment
/-- A doc comment: `#eval`, `elab_rules`, `@[init f]`, `skipKernelTC`. -/
def zzP : String := "#eval run_cmd elab elab_rules initialize @[init f]"
def zzQ : String := s!"#eval {1 + 1} elab"
#guard 1 + 1 = 2
#check_failure (1 : String)
#synth Inhabited Nat
def elaborate (init : Nat) : Nat := init
@[inline] def initial (init : Nat) : Nat := init
def zzR (elabCount runCmd : Nat) : Nat := elabCount + runCmd
macro "zz" : term => `(0)
syntax "yy" : term
LEAN
plant "$T" Metaprograms
uv run --no-project --python 3.12 python "$T/scripts/check_boundaries.py" --root "$T" >"$LOG" 2>&1; got=$?
n=0; bad=0
while IFS= read -r line; do
  n=$((n + 1)); marked=0; reported=0
  if [[ $line == *"-- BAN" ]]; then marked=1; fi
  if grep -q "^boundary: STFSpec/Hash/Metaprograms.lean:$n: banned in core: " "$LOG"; then reported=1; fi
  if [ "$marked" -ne "$reported" ]; then
    echo "FAIL: line $n is $([ "$marked" -eq 1 ] && echo missed || echo wrongly reported): $line"; bad=1; fi
done < "$MOD"
if [ "$got" -eq 1 ] && [ "$bad" -eq 0 ]; then echo "ok:   every listed metaprogram entry point and skipKernelTC spelling is rejected, and no look-alike"
else echo "FAIL: metaprogram entry points or look-alikes misjudged (exit $got)"; cat "$LOG"; FAIL=1; fi
rm -rf "$T"
# The lexer cases again, each in isolation (in one module, a misread literal can be masked by the
# next one): a literal or «name» must not hide the code after it, interpolations are code, and
# an attribute argument is not an attribute name. A trailing quote gives a misread string an end.
if uv run --no-project --python 3.12 python -B - "$ROOT/scripts" <<'PY'
import re, sys
sys.path.insert(0, sys.argv[1]); import check_boundaries as cb
def reported(src):
    code, lits = cb.strip_comments(src), cb.strip_comments(src, keep_strings=True)
    return any(re.search(p, code, re.M) for p, _ in cb.BANNED) or \
           any(re.search(p, lits, re.M) for p, _ in cb.BANNED_IN_LITERALS)
cases = [  # (source, must be reported)
    ("def a : Char := '\"'\n#eval 1\ndef b := \"x\"\n", True),
    ("def a : Bool := !'\"'.isAlpha\n#eval 1\ndef b := \"x\"\n", True),
    ("def a : Bool := ?'\"'\n#eval 1\ndef b := \"x\"\n", True),
    ("def a := r\"\\\"\n#eval 1\ndef b := \"x\"\n", True),
    ("def a := s!\"{'\"'}\"\n#eval 1\ndef b := \"x\"\n", True),
    ("def «a\"» : Nat := 0\n#eval 1\ndef b := \"x\"\n", True),
    ("def «/-» : Nat := 0\n#eval 1\ndef «-/» : Nat := 0\n", True),
    ("def «--» : Nat := by_elab pure 0\n", True),
    ("def a := s!\"{sorry}\"\n", True),
    ("def a := s! \"{sorry}\"\n", True),
    ("def a : Nat := dbg_trace \"{sorry}\"; 0\n", True),
    ("@[simp, init f] def a : Nat := 0\n", True),
    ("@[«init» f] def a : Nat := 0\n", True),
    ("@[simp, «tactic» k] def a : Nat := 0\n", True),
    ("def «elab» : Nat := 0\n", False),
    ("def a (x' : Nat) : Char := if x' = 0 then 'a' else 'b'\n", False),
    ("def foo!'a' : Nat := 0\n", False),
    ("@[deprecated init (since := \"2026-01-01\")] def a : Nat := 0\n", False),
    ("@[simp, deprecated tactic] def a : Nat := 0\n", False),
    ("def a := \"{sorry}\"\n", False),
]
bad = [src for src, want in cases if reported(src) != want]
for src in bad: print("FAIL: lexer case misjudged:", repr(src))
sys.exit(1 if bad else 0)
PY
then echo "ok:   isolated lexer cases («name», literals after ! and ?, raw and interpolated strings, attribute arguments)"
else FAIL=1; fi

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
# The kernel bypass: check-decls judges declarations by their axioms and cannot see it (pinned,
# so that a change is noticed); kernel replay rejects it. The prefix argument mirrors
# scripts/replay_kernel.sh, which replays every module under a namespace.
OUT=$(lake exe check-decls CheckDeclsTest.KernelBypass); st=$?
if [ "$st" -eq 0 ] && grep -q "; 0 findings$" <<<"$OUT"; then echo "ok:   check-decls cannot see the kernel bypass (pinned blind spot; kernel replay is the check)"
else echo "FAIL: check-decls on the kernel bypass changed (exit $st); update this pin and the fixture's comment"; echo "$OUT"; FAIL=1; fi
if lake env leanchecker CheckDeclsTest >"$LOG" 2>&1; then echo "FAIL: kernel replay accepts the kernel bypass"; FAIL=1
elif grep -q "^leanchecker found a problem in CheckDeclsTest.KernelBypass$" "$LOG" \
  && grep -q "while replaying declaration 'CheckDeclsTest.KernelBypass.bad'" "$LOG"; then echo "ok:   kernel replay of the CheckDeclsTest namespace rejects the kernel bypass"
else echo "FAIL: kernel replay fails, but not on the kernel bypass"; cat "$LOG"; FAIL=1; fi
# An unbuilt module on disk must make the (disk-discovering) declaration check fail.
if [ ! -d STFSpec/Hash ]; then mkdir STFSpec/Hash; ORPHAN_DIR=STFSpec/Hash; fi
ORPHAN=$(mktemp STFSpec/Hash/CheckDeclsOrphanXXXXXX.lean)
printf 'def orphan : Nat := 0\n' > "$ORPHAN"
if scripts/check_decls.sh core >"$LOG" 2>&1; then echo "FAIL: check-decls passes with an unbuilt module on disk"; FAIL=1; else echo "ok:   check-decls fails on an unbuilt module on disk"; fi
rm -f "$ORPHAN"; ORPHAN=""
exit $FAIL
