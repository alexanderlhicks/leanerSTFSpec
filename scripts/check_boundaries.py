#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Enforce the core package's dependency and hygiene boundaries.

Checks (CONTRIBUTING.md §4, STFSpec/informal/ARCHITECTURE.md §3):
  1. the core lakefile declares no `[[require]]` (package-level Mathlib boundary);
  2. every `lean_lib` in the lakefile under `STFSpec.` is declared in boundaries.toml, and the
     declared graph is acyclic;
  3. every core module belongs to exactly one library, and imports only Lean/Init/Std or
     modules of libraries in the transitive closure of its library's deps;
  3b. every core module on disk is reachable by imports from its library's root, so that
     building the roots builds (and the declaration check discovers) every module: an unimported file
     would otherwise escape both compilation and the declaration check;
  4. source-level bans in core modules (defence in depth; `check-decls` checks the compiled
     declarations): `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `partial`,
     `opaque`, `implemented_by`, `extern`, and `set_option` of kernel/elaborator escape
     hatches (`debug.skipKernelTC`, `maxRecDepth`/`maxHeartbeats 0`). `@[csimp]`, `bv_decide`
     and `decide +native` are not checked here: they are enforced only by `check-decls`;
  5. the dependency table in STFSpec/informal/ARCHITECTURE.md §3 states exactly the direct
     deps of boundaries.toml for every library it lists, and lists every library.
Exit status is non-zero on any violation.
"""
import argparse, pathlib, re, sys, tomllib

LEAN_BUILTIN = ("Init", "Std", "Lean")
BANNED = [
    (r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"\bnative_decide\b", "native_decide"),
    (r"^\s*(private\s+|protected\s+)?axiom\b", "axiom"), (r"\bunsafe\b", "unsafe"),
    (r"\bpartial\s+def\b", "partial def"), (r"^\s*(private\s+|protected\s+)?opaque\b", "opaque"),
    (r"implemented_by", "implemented_by"), (r"@\[\s*extern\b|\bextern\s+\"", "extern"),
    (r"set_option\s+debug\.skipKernelTC", "debug.skipKernelTC"),
    (r"set_option\s+(maxHeartbeats|maxRecDepth)\s+0\b", "unbounded maxHeartbeats/maxRecDepth"),
]

def strip_comments(src: str) -> str:
    """Remove Lean comments (nested block comments, doc comments, line comments) and strings."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            out.append("  "); depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            out.append("  "); depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n": out.append(" "); i += 1
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.extend("\n" if c == "\n" else " " for c in src[i:min(j + 1, n)])
            i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)

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
    for path in sorted((root / "STFSpec").rglob("*.lean")):
        mod = ".".join(path.relative_to(root).with_suffix("").parts)
        lib = lib_of(mod)
        if lib is None:
            errors.append(f"{path.relative_to(root)}: module {mod} belongs to no declared library")
            continue
        raw = path.read_text()
        code = strip_comments(raw)
        lib_of_mod[mod] = lib
        imports_of[mod] = [m.group(1) for m in re.finditer(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", code, re.M)]
        for m in re.finditer(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", code, re.M):
            imp = m.group(1)
            if imp.split(".")[0] in LEAN_BUILTIN:
                continue
            tgt = lib_of(imp)
            if tgt is None:
                errors.append(f"{mod}: imports {imp}, which is outside the core (only Init/Std/Lean allowed)")
            elif tgt != lib and tgt not in closure[lib]:
                errors.append(f"{mod} ({lib}): imports {imp} ({tgt}), not in the allowed closure {sorted(closure[lib])}")
        for pat, what in BANNED:
            for m in re.finditer(pat, code, re.M):
                line = code.count("\n", 0, m.start()) + 1
                errors.append(f"{path.relative_to(root)}:{line}: banned in core: {what}")

    # 3b. reachability from library roots
    for name, spec in bounds.items():
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
