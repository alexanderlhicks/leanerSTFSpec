#!/usr/bin/env bash
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
# Check compiled declarations of EVERY module on disk (not just library roots), so that a
# module nobody imports cannot escape the declaration check: its .olean would be missing and the import
# fails. `scripts/check_decls.sh core` is strict. `scripts/check_decls.sh mathlib|security` tolerate `sorry` during
# development (reported separately) but not csimp replacements, axioms, unsafe/partial/opaque,
# extern or implemented_by.
set -euo pipefail
cd "$(dirname "$0")/.."
modules() { # modules <dir> <prefix-dir>: list module names of all .lean files under <dir>
  (cd "$2" && find "$1" -name '*.lean' | sort | sed 's|\.lean$||; s|/|.|g'); }
case "${1:-}" in
  core)
    mapfile -t MODS < <(modules STFSpec .)
    exec lake exe check-decls "${MODS[@]}" ;;
  mathlib|security)
    PKG=$([ "$1" = mathlib ] && echo STFSpecMathlib || echo STFSpecSecurity)
    # Every module of the package on disk, excluding its dependency checkouts.
    mapfile -t MODS < <(cd "$PKG" && find . -path ./.lake -prune -o -name '*.lean' ! -name lakefile.lean -print \
      | sort | sed 's|^\./||; s|\.lean$||; s|/|.|g')
    cd "$PKG"
    lake exe check-decls --allow-sorry "${MODS[@]}"
    echo "--- sorry report (informational until release gates) ---"
    n=$(lake exe check-decls "${MODS[@]}" | grep -c 'sorryAx' || true)
    echo "$n declarations depend on sorry" ;;
  *) echo "usage: scripts/check_decls.sh core|mathlib|security" >&2; exit 2 ;;
esac
