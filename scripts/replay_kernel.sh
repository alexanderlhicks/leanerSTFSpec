#!/usr/bin/env bash
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
# Kernel replay: re-check every constant of every module of a package's libraries with the Lean
# kernel (`leanchecker`), after `lake build`. This is the soundness check against declarations
# the kernel never checked, such as one added by an elaboration-time metaprogram (`addDecl` under
# `debug.skipKernelTC`, or `addDeclWithoutChecking`); neither `check-decls` nor `#print axioms`
# can see one (scripts/CheckDeclsTest/KernelBypass.lean). It checks constants only: environment
# extensions, compiled IR and build-time IO are outside it.
#
# Scope: the library namespaces (core: STFSpec; mathlib: STFSpecMathlib; security:
# STFSpecSecurity and ToVCVio). The core package's `scripts/` executables (native tests,
# benchmarks, the checkers and their fixtures) are not replayed: no library imports them, no
# result depends on them, and `check-decls` audits them; CheckDeclsTest fails replay by design.
#
# `leanchecker` treats each argument as a module-name prefix and replays every .olean on the
# search path under it, each against its own imports. A .olean whose source is gone (a renamed or
# deleted module, for example in a restored CI cache) is removed first, since replaying it against
# current imports can fail spuriously. The number of modules replayed must then equal the number
# of source modules under the namespaces, so an unbuilt module fails the check.
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=$(mktemp); trap 'rm -f "$LOG"' EXIT
replay() { # replay <namespace>...: in the current package directory
  if [ "$#" -eq 0 ]; then echo "replay_kernel: no namespaces to replay" >&2; exit 1; fi
  local lib=.lake/build/lib/lean ns olean src sources=0 replayed
  for ns in "$@"; do
    if [ -d "$lib" ]; then
      while IFS= read -r olean; do
        src=${olean#"$lib/"}; src=${src%.olean}.lean
        if [ ! -f "$src" ]; then echo "replay_kernel: removing $olean (no $src)"; rm -f "$olean"; fi
      done < <(find "$lib" \( -path "$lib/$ns.olean" -o -path "$lib/$ns/*.olean" \) -print)
    fi
    sources=$((sources + $( { if [ -f "$ns.lean" ]; then echo "$ns.lean"; fi
                             if [ -d "$ns" ]; then find "$ns" -name '*.lean'; fi; } | wc -l)))
  done
  lake env leanchecker --verbose "$@" > "$LOG"
  replayed=$(grep -c '^replaying ' "$LOG" || true)
  if [ "$replayed" -ne "$sources" ]; then
    echo "replay_kernel: replayed $replayed modules under $*, but $sources source modules exist" >&2; exit 1
  fi
  echo "replay_kernel: all $replayed modules under $* replayed"
}
namespaces() { # the top-level module names of the current package, excluding dependency checkouts
  find . -path ./.lake -prune -o -name '*.lean' ! -name lakefile.lean -print | sed 's|^\./||; s|/.*||; s|\.lean$||' | sort -u; }
case "${1:-}" in
  core) replay STFSpec ;;
  mathlib|security)
    cd "$([ "$1" = mathlib ] && echo STFSpecMathlib || echo STFSpecSecurity)"
    mapfile -t NS < <(namespaces)
    replay "${NS[@]}" ;;
  *) echo "usage: scripts/replay_kernel.sh core|mathlib|security" >&2; exit 2 ;;
esac
