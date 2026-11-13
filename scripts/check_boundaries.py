#!/usr/bin/env -S uv run --no-project --python 3.12 python
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Enforce the core package's dependency and hygiene boundaries.

Checks (CONTRIBUTING.md §4, STFSpec/informal/ARCHITECTURE.md §3):
  1. the core lakefile declares no `[[require]]` (package-level Mathlib boundary);
  2. every `lean_lib` in the lakefile under `STFSpec.` is declared in boundaries.toml, and the
     declared graph is acyclic;
  3. every core module belongs to exactly one library, and imports only Init, Std,
     `Lean.Data.Json` or its submodules, or modules of libraries in the transitive closure of
     its library's deps. Any other `Lean` import is a violation: the JSON modules do not
     bring the elaborator, `addDecl` or the kernel environment into scope, so a core module
     cannot name them. Imports come from Lake's fast import parser (`Lean.parseImports'` in
     `Lean/Elab/ParseImportsFast.lean`, run as `lean --deps-json`: one batched call with the
     pinned toolchain, `lean_imports`), the parser Lake itself uses for build dependencies; it
     can over-report imports relative to the frontend but never under-reports without an
     error. If it cannot run or cannot read a header, that is a violation, and checks 3 and 3b
     are skipped so that the cause is not buried under spurious reachability reports;
  3b. every core module on disk is reachable by imports from its library's root, so that
     building the roots builds (and the declaration check discovers) every module: an unimported file
     would otherwise escape both compilation and the declaration check;
  4. source-level bans in core modules (defence in depth; `check-decls` checks the compiled
     declarations): `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `partial`,
     `opaque`, `implemented_by`, `extern`, `set_option maxHeartbeats/maxRecDepth 0`, and the
     literal token `skipKernelTC` outside comments, string literals included. `@[csimp]`,
     `bv_decide` and `decide +native` are not checked here: they are enforced only by `check-decls`;
  4b. a tripwire against accidental or obvious elaboration-time metaprograms in core modules:
     `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `by_elab`, `elab`/`elab_rules`,
     `initialize`/`builtin_initialize`, the `init`/`builtin_init` attributes, the
     elaborator-registering attributes `command_elab`/`term_elab`/`tactic`, and the `simproc`
     commands. It is a token check, not a guarantee. It is evaded by a `macro` (allowed) whose
     expansion builds a `#eval` command node, by an option name assembled from strings, and by
     `Lean.Kernel.Environment.addDeclWithoutChecking`, which needs no option; check 3 removes
     the names those routes need, but a macro expanding to `#eval` of Init-only `IO` stays
     possible. Logical soundness rests on kernel replay (`scripts/replay_kernel.sh`), which
     re-checks every constant of every library module. Replay checks constants only:
     environment extensions, compiled IR and build-time IO are outside it;
  5. the dependency table in STFSpec/informal/ARCHITECTURE.md §3 states exactly the direct
     deps of boundaries.toml for every library it lists, and lists every library.
Exit status is non-zero on any violation.
"""
import argparse, json, pathlib, re, subprocess, sys, tomllib

LEAN_BUILTIN = ("Init", "Std")
# The only `Lean` imports a core module may use: `Lean.Data.Json` and its submodules.
LEAN_ALLOWED = "Lean.Data.Json"
# A keyword or attribute name, not part of a longer identifier or a dotted name.
_KW = r"(?<![\w.'!?«])({})(?![\w'!?»])"
BANNED = [
    (r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"\bnative_decide\b", "native_decide"),
    (r"^[^\S\n]*(private\s+|protected\s+)?axiom\b", "axiom"), (r"\bunsafe\b", "unsafe"),
    (r"\bpartial\s+def\b", "partial def"), (r"^[^\S\n]*(private\s+|protected\s+)?opaque\b", "opaque"),
    (r"implemented_by", "implemented_by"), (r"@\[\s*extern\b|\bextern\s+\"", "extern"),
    (r"set_option\s+(maxHeartbeats|maxRecDepth)\s+0\b", "unbounded maxHeartbeats/maxRecDepth"),
    # 4b. Elaboration-time metaprogram entry points (a tripwire; see the module docstring).
    (r"#eval\b", "#eval (elaboration-time metaprogram)"),
    (_KW.format(r"run_cmd|run_elab|run_meta|run_tac|by_elab"), "run_* / by_elab (elaboration-time metaprogram)"),
    (_KW.format(r"elab|elab_rules"), "elab / elab_rules (elaboration-time metaprogram)"),
    (_KW.format(r"initialize|builtin_initialize"), "initialize (elaboration-time metaprogram)"),
    (_KW.format(r"d?simproc(?:_decl)?|builtin_d?simproc(?:_decl)?"), "simproc (elaboration-time metaprogram)"),
    # An attribute *name* (first in the list or after a comma), not an argument such as
    # `@[deprecated init (since := …)]`; Lean also accepts the name in guillemets (`@[«init» f]`).
    (r"(?:@\[|\battribute\s*\[)(?:[^\]]*?,)?\s*(?:(?:scoped|local)\s+)?"
     r"(?<![\w.'!?])«?(?:init|builtin_init|command_elab|term_elab|tactic)»?(?![\w'!?])",
     "init / elaborator attribute (elaboration-time metaprogram)"),
]
# Checked with string and character literals kept, so that a quoted option name is caught too.
BANNED_IN_LITERALS = [(r"skipKernelTC", "skipKernelTC")]

_IDENT_CHAR = re.compile(r"[\w.'!?]")
_IDENT_RUN_START = re.compile(r"[^\W\d]")          # a letter or `_` starts an identifier
_CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
_RAW_STR = re.compile(r'r(#*)"')
_NEXT = re.compile(r"/-|--|['\"r{}«]")      # where a comment, literal, «name» or brace may start
_NESTING = re.compile(r"/-|-/")
_IN_STRING = re.compile(r'[\\"{]')
# Strings that Lean parses as interpolated: after `s!`, `m!`, `f!`, `panic!`, … (with optional
# whitespace) or after a known interpolating macro.
_INTERPOLATING = re.compile(r"(?:!|(?<![\w.'!?])(?:throwError|logInfo|logWarning|logError|dbg_trace))\s*$")

def _blank(s: str) -> str:
    return re.sub(r"[^\n]", " ", s)

def _is_prime(src: str, i: int) -> bool:
    """Whether the `'` at `i` continues an identifier (`x'`, `foo!'a'`) rather than opening a
    character literal: the maximal run of identifier characters before it starts with a
    letter or `_` (so `!'"'` and `?'a'` open literals)."""
    j = i
    while j > 0 and _IDENT_CHAR.match(src[j - 1]): j -= 1
    return j < i and bool(_IDENT_RUN_START.match(src[j]))

def _lex(src: str, i: int, keep: bool, out: list[str], in_braces: bool = False) -> int:
    """Copy `src[i:]` to `out`, blanking comments and (unless `keep`) literals; inside a string
    interpolation (`in_braces`), stop after its closing brace. Returns the index reached."""
    n, braces = len(src), 0
    lit = out.append if keep else (lambda s: out.append(_blank(s)))
    while (m := _NEXT.search(src, i)):
        out.append(src[i:m.start()]); i, tok = m.start(), m.group()
        if tok == "/-":                                  # nested block and doc comments
            j, depth = i + 2, 1
            while depth and (k := _NESTING.search(src, j)):
                depth += 1 if k.group() == "/-" else -1; j = k.end()
            j = j if not depth else n
            out.append(_blank(src[i:j])); i = j
        elif tok == "--":
            j = src.find("\n", i); j = n if j < 0 else j
            out.append(_blank(src[i:j])); i = j
        elif tok == "«":                                 # `«…»` identifier: kept verbatim
            j = src.find("»", i + 1); j = n if j < 0 else j + 1
            out.append(src[i:j]); i = j
        elif tok == "'" and not _is_prime(src, i) and (k := _CHAR_LIT.match(src, i)):
            lit(k.group()); i = k.end()
        elif tok == "r" and not (i > 0 and _IDENT_CHAR.match(src[i - 1])) and (k := _RAW_STR.match(src, i)):
            j = src.find('"' + k.group(1), k.end()); j = n if j < 0 else j + 1 + len(k.group(1))
            lit(src[i:j]); i = j
        elif tok == '"':                                 # interpolated: the braces hold code
            interpolated = bool(_INTERPOLATING.search(src, max(0, i - 64), i))
            start, j = i, i + 1
            while (k := _IN_STRING.search(src, j)) and k.group() != '"':
                if k.group() == "\\": j = k.end() + 1
                elif interpolated:
                    lit(src[start:k.end()]); j = start = _lex(src, k.end(), keep, out, True)
                else: j = k.end()
            j = k.end() if k else n
            lit(src[start:j]); i = j
        elif in_braces and tok == "}" and not braces:
            out.append(tok); return i + 1
        else:
            if in_braces and tok in "{}": braces += 1 if tok == "{" else -1
            out.append(tok); i += 1
    out.append(src[i:])
    return n

def strip_comments(src: str, keep_strings: bool = False) -> str:
    """Remove Lean comments (nested block comments, doc comments, line comments) and the contents
    of string and character literals, preserving line structure; with `keep_strings`, keep the
    literals. Recognises `«…»` identifiers, character literals after `!`/`?`, raw strings
    (`r#"…"#`) and interpolated strings (after `!` or a known interpolating macro), whose
    `{…}` parts are code. Interpolating macros not listed in `_INTERPOLATING` are missed: their
    `{…}` parts are read as string contents. It approximates Lean's tokenizer; kernel replay is
    authoritative."""
    out: list[str] = []
    _lex(src, 0, keep_strings, out)
    return "".join(out)

def lean_imports(root: pathlib.Path, paths: list[pathlib.Path]) -> tuple[dict[pathlib.Path, list[str]], list[str]]:
    """The modules each file's header imports, read by Lake's fast import parser
    (`Lean.parseImports'`, the one Lake uses for build dependencies): one batched
    `lean --deps-json` call, run from `root` so that elan selects the pinned toolchain in
    `root/lean-toolchain` (checked against `lean --version`). Lean prepends implicit `Init`
    entries (one plain, one `meta`) to every non-`prelude` file; exactly those two leading
    entries are dropped. Fails closed: a missing or mismatched toolchain, a nonzero exit,
    unreadable output, a count mismatch or a per-file parse error yields an error, never an
    empty import list that passes. Returns (imports per readable file, errors)."""
    pin_file = root / "lean-toolchain"
    if not pin_file.exists():
        return {}, [f"{pin_file.name} is missing: cannot run Lake's import parser"]
    pin = pin_file.read_text().strip()
    try:
        ver = subprocess.run(["lean", "--version"], cwd=root, capture_output=True, text=True, timeout=300)
        if ver.returncode or f"version {pin.rsplit(':', 1)[-1].lstrip('v')}," not in ver.stdout:
            return {}, [f"lean --version ({(ver.stdout + ver.stderr).strip()[:200]}) does not match lean-toolchain {pin}"]
        run = subprocess.run(["lean", "--deps-json", *map(str, paths)], cwd=root,
                             capture_output=True, text=True, timeout=600)
    except (OSError, subprocess.SubprocessError) as e:
        return {}, [f"cannot run Lake's import parser: {e}"]
    if run.returncode:
        return {}, [f"lean --deps-json exited {run.returncode}: {run.stderr.strip()[:500]}"]
    try:
        entries = json.loads(run.stdout)["imports"]
    except (ValueError, KeyError, TypeError) as e:
        return {}, [f"lean --deps-json output is unreadable: {e}"]
    if not isinstance(entries, list) or len(entries) != len(paths):
        return {}, [f"lean --deps-json returned {len(entries) if isinstance(entries, list) else '?'} entries for {len(paths)} files"]
    out: dict[pathlib.Path, list[str]] = {}
    errors: list[str] = []
    for path, entry in zip(paths, entries):
        try:
            if entry.get("errors") or "result" not in entry:
                errors.append(f"{path.relative_to(root)}: Lean cannot read the header: {entry.get('errors')}"); continue
            imps = entry["result"]["imports"]
            if [(i["module"], i["isMeta"]) for i in imps[:2]] == [("Init", False), ("Init", True)]:
                imps = imps[2:]
            out[path] = [i["module"] for i in imps]
        except (AttributeError, KeyError, TypeError) as e:
            errors.append(f"{path.relative_to(root)}: unreadable lean --deps-json entry: {e}")
    return out, errors

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root")
    root = pathlib.Path(ap.parse_args().root).resolve()
    errors: list[str] = []
    bounds = tomllib.loads((root / "scripts/boundaries.toml").read_text())["libs"]
    lake = tomllib.loads((root / "lakefile.toml").read_text())

    # 1. no requires
    if lake.get("require"):
        errors.append("lakefile.toml: the core package must not `require` any package")

    # 2. lakefile libs vs boundaries; acyclicity
    core_libs = {l["name"]: l for l in lake.get("lean_lib", [])
                 if any(r.startswith("STFSpec.") for r in l.get("roots", []))}
    for name in core_libs.keys() - bounds.keys():
        errors.append(f"lakefile lean_lib {name} is not declared in boundaries.toml")
    for name in bounds.keys() - core_libs.keys():
        errors.append(f"boundaries.toml lib {name} has no lean_lib in lakefile.toml")
    for name in core_libs.keys() & bounds.keys():
        if core_libs[name].get("roots") != [bounds[name]["root"]]:
            errors.append(f"lakefile {name}: roots must equal [{bounds[name]['root']}] from boundaries.toml")
    for name, spec in bounds.items():
        for d in spec["deps"]:
            if d not in bounds:
                errors.append(f"boundaries.toml: {name} depends on unknown lib {d}")
    closure: dict[str, set[str]] = {}
    def close(lib: str, stack: tuple = ()) -> set[str]:
        if lib in stack:
            errors.append(f"boundaries.toml: dependency cycle {' -> '.join(stack + (lib,))}")
            return set()
        if lib not in closure:
            acc: set[str] = set()
            for d in bounds.get(lib, {}).get("deps", []):
                acc |= {d} | close(d, stack + (lib,))
            closure[lib] = acc
        return closure[lib]
    for lib in bounds: close(lib)

    # 3 & 4. modules
    roots = sorted(((spec["root"], name) for name, spec in bounds.items()), key=lambda r: -len(r[0]))
    def lib_of(mod: str):
        for r, name in roots:
            if mod == r or mod.startswith(r + "."):
                return name
        return None
    imports_of: dict[str, list[str]] = {}
    lib_of_mod: dict[str, str] = {}
    paths = sorted((root / "STFSpec").rglob("*.lean"))
    header, header_errors = lean_imports(root, paths)
    errors.extend(header_errors)
    imports_known = not header_errors      # otherwise checks 3 and 3b are skipped (fail closed)
    for path in paths:
        mod = ".".join(path.relative_to(root).with_suffix("").parts)
        lib = lib_of(mod)
        if lib is None:
            errors.append(f"{path.relative_to(root)}: module {mod} belongs to no declared library")
            continue
        raw = path.read_text()
        code = strip_comments(raw)
        lib_of_mod[mod] = lib
        imports_of[mod] = header.get(path, [])
        for imp in (imports_of[mod] if imports_known else []):
            if imp.split(".")[0] in LEAN_BUILTIN or imp == LEAN_ALLOWED or imp.startswith(LEAN_ALLOWED + "."):
                continue
            tgt = lib_of(imp)
            if imp.split(".")[0] == "Lean":
                errors.append(f"{mod}: imports {imp}; from Lean, core modules may import only {LEAN_ALLOWED} and its submodules")
            elif tgt is None:
                errors.append(f"{mod}: imports {imp}, which is outside the core (only Init, Std and {LEAN_ALLOWED} allowed)")
            elif tgt != lib and tgt not in closure[lib]:
                errors.append(f"{mod} ({lib}): imports {imp} ({tgt}), not in the allowed closure {sorted(closure[lib])}")
        for text, banned in ((code, BANNED), (strip_comments(raw, keep_strings=True), BANNED_IN_LITERALS)):
            for pat, what in banned:
                for m in re.finditer(pat, text, re.M):
                    line = text.count("\n", 0, m.start()) + 1
                    errors.append(f"{path.relative_to(root)}:{line}: banned in core: {what}")

    # 3b. reachability from library roots
    for name, spec in (bounds.items() if imports_known else []):
        seen, todo = set(), [spec["root"]]
        while todo:
            m = todo.pop()
            if m in seen or m not in imports_of: continue
            seen.add(m); todo.extend(imports_of[m])
        if spec["root"] not in imports_of:
            errors.append(f"library {name}: root module {spec['root']} does not exist")
        for mod, lib in lib_of_mod.items():
            if lib == name and mod not in seen:
                errors.append(f"{mod} ({name}) is not imported (transitively) by its library root {spec['root']}: it would be neither built nor checked")

    # 5. The architecture's dependency table agrees with boundaries.toml.
    arch = root / "STFSpec/informal/ARCHITECTURE.md"
    if not arch.exists():
        errors.append(f"{arch.relative_to(root)} is missing")
    else:
        text = arch.read_text()
        m = re.search(r"^\| Library \| Contents \| May depend on \|.*?\n\|[-| ]+\|\n((?:\|.*\n)+)", text, re.M)
        if not m:
            errors.append("ARCHITECTURE.md §3: dependency table (| Library | Contents | May depend on | …) not found")
        else:
            listed = set()
            for row in m.group(1).splitlines():
                cells = [c.strip() for c in row.strip().strip("|").split("|")]
                deps = set(re.findall(r"`(Eth\w*)`", cells[2])) if len(cells) > 2 else set()
                for lib in re.findall(r"`(Eth\w*)`", cells[0]):
                    listed.add(lib)
                    if lib not in bounds:
                        errors.append(f"ARCHITECTURE.md §3 lists {lib}, which boundaries.toml does not declare")
                    elif deps != set(bounds[lib]["deps"]):
                        errors.append(f"ARCHITECTURE.md §3: {lib} may depend on {sorted(deps)}, "
                                      f"but boundaries.toml says {sorted(bounds[lib]['deps'])}")
            for lib in sorted(set(bounds) - listed):
                errors.append(f"ARCHITECTURE.md §3 does not list {lib}")

    for e in errors:
        print("boundary:", e)
    print(f"check_boundaries: {len(bounds)} libraries, {len(errors)} violations")
    return 1 if errors else 0

if __name__ == "__main__":
    sys.exit(main())
