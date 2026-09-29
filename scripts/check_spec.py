#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Check the informal specification (STFSpec/informal/) against the architecture and the pinned EELS.

1. Every core library in scripts/boundaries.toml and every proof library in
   STFSpecMathlib/lakefile.toml and STFSpecSecurity/lakefile.toml has STFSpec/informal/modules/<Library>.md with the ten required sections.
2. Coverage: every item of STFSpec/informal/eels-inventory.json (function, class, method, constant) is
   claimed by exactly one spec guidance document (`file::name` or `file::*` in §3) or excluded in
   STFSpec/informal/EXCLUDED.md; every claim names a real inventory item or file. External-library
   items are reported (by library) but only need to be discussed, not claimed.
3. §8 "Depends on:" matches the library's direct deps in boundaries.toml exactly.
4. Pins agree; shared declarations have one owner; proof imports are explicit and acyclic.
5. §7 contains an informal argument with claim, premises, argument and open obligations.
6. Every decision ID (D<n>, P<n>) and every resolution, finding or question ID (B<n>, F<n>,
   Q<n>) mentioned exists in STFSpec/informal/DECISIONS.md.
These are structural checks, not verification of Lean typing or mathematical truth.
With --report, also print per-module counts and the unclaimed items (the coverage gaps).
"""
import collections, json, pathlib, re, sys, tomllib
from check_boundaries import strip_comments

ROOT = pathlib.Path(__file__).resolve().parent.parent
SECTIONS = ["## 1. Purpose", "## 2. Requirements", "## 3. EELS source map", "## 4. Tests",
            "## 5. Interface", "## 6. Data structures", "## 7. Contract and laws",
            "## 8. Composition", "## 9. Open decisions", "## 10. Gaps"]
CLAIM = re.compile(r"`([A-Za-z0-9_./]+\.py)::([A-Za-z0-9_.*]+)`")

def sections(text: str, owner: str, errs: list[str]) -> dict[int, str]:
    heads = list(re.finditer(r"^## (\d+)\. ([^\n]+)$", text, re.M))
    if [int(h[1]) for h in heads] != list(range(1, 11)):
        errs.append(f"{owner}: numbered sections must occur once each, in order 1–10")
    out = {}
    for i, h in enumerate(heads):
        n = int(h[1])
        if not 1 <= n <= 10:
            continue
        if h[0] != SECTIONS[n-1]:
            errs.append(f"{owner}: expected heading '{SECTIONS[n-1]}'")
        body = text[h.end():heads[i+1].start() if i+1 < len(heads) else len(text)].strip()
        if not body:
            errs.append(f"{owner}: section {n} is empty")
        out[n] = body
    return out

def closures(graph: dict[str, list[str]], errs: list[str]) -> dict[str, set[str]]:
    done, active = {}, []
    def visit(lib):
        if lib in active:
            errs.append("dependency cycle: " + " -> ".join(active + [lib]))
            return set()
        if lib in done:
            return done[lib]
        active.append(lib)
        result = set()
        for dep in graph[lib]:
            if dep not in graph:
                errs.append(f"{lib}: unknown dependency {dep}")
                continue
            result.add(dep)
            result.update(visit(dep))
        active.pop()
        done[lib] = result
        return result
    for lib in graph:
        visit(lib)
    return done

def main() -> int:
    report = "--report" in sys.argv
    errs: list[str] = []
    bounds = tomllib.loads((ROOT / "scripts/boundaries.toml").read_text())["libs"]
    proof_configs = [(pkg, l) for pkg in ("STFSpecMathlib", "STFSpecSecurity")
                     for l in tomllib.loads((ROOT / pkg / "lakefile.toml").read_text()).get("lean_lib", [])]
    proof_libs = [l["name"] for _, l in proof_configs]
    libs = list(bounds) + proof_libs
    contracts = tomllib.loads((ROOT / "STFSpec/informal/contracts.toml").read_text())
    proof_imports = contracts["proof_imports"]
    if set(proof_imports) != set(proof_libs):
        errs.append("contracts.toml proof_imports must enumerate the proof libraries exactly")
    for path in (ROOT / "STFSpec/informal/modules").glob("*.md"):
        if path.stem not in libs:
            errs.append(f"unregistered spec guidance: {path.name}")
    module_owners = {b["root"]: n for n, b in bounds.items()}
    module_owners.update({r: l["name"] for _, l in proof_configs for r in l.get("roots", [])})
    def owner_of(module):
        return next((module_owners[r] for r in sorted(module_owners, key=len, reverse=True)
                     if module == r or module.startswith(r + ".")), None)
    for pkg, config in proof_configs:
        imported, seen, pending = set(), set(), list(config.get("roots", []))
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            source = ROOT / pkg / (module.replace(".", "/") + ".lean")
            if not source.exists():
                errs.append(f"{config['name']}: missing proof root {module}")
                continue
            for module_import in re.findall(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", strip_comments(source.read_text()), re.M):
                owner = owner_of(module_import)
                if owner == config["name"]:
                    pending.append(module_import)
                elif owner:
                    imported.add(owner)
                elif module_import.split(".")[0] in ("STFSpec", "STFSpecMathlib", "STFSpecSecurity"):
                    errs.append(f"{config['name']}: unregistered repository import {module_import}")
        if imported != set(proof_imports.get(config["name"], [])):
            errs.append(f"{config['name']}: proof source imports {sorted(imported)} differ from import registry {proof_imports.get(config['name'], [])}")
    graph = {lib: list(b["deps"]) for lib, b in bounds.items()}
    graph.update({lib: list(proof_imports.get(lib, [])) for lib in proof_libs})
    for lib in bounds:
        if any(dep not in bounds for dep in graph[lib]):
            errs.append(f"{lib}: core cannot import a proof library")
    reachable = closures(graph, errs)
    inv = json.loads((ROOT / "STFSpec/informal/eels-inventory.json").read_text())
    release = tomllib.loads((ROOT / "reference.toml").read_text())["release"]
    if inv["release"] != release["commit"]:
        errs.append("inventory pin does not match reference.toml")
    items = [i for i in inv["items"] if i["kind"] != "external"]
    by_file = collections.defaultdict(set)
    for i in items: by_file[i["file"]].add(i["name"])
    decisions_md = (ROOT / "STFSpec/informal/DECISIONS.md").read_text()
    decisions = set(re.findall(r"^\| ([DP]\d+) \|", decisions_md, re.M))
    # B/F/Q/O IDs are defined in the first two columns of the DECISIONS tables (the B rows list
    # their original Q numbers in the second).
    defined_ids = set()
    for row in re.findall(r"^\| (.*)$", decisions_md, re.M):
        for c in row.split(" | ")[:2]:
            defined_ids |= set(re.findall(r"\b([BFQO]\d+)\b", c))

    claims: dict[tuple, list[str]] = collections.defaultdict(list)
    def claim_all(text: str, owner: str):
        for f, n in CLAIM.findall(text):
            if f not in by_file:
                errs.append(f"{owner}: claims `{f}::{n}`, but {f} is not in the inventory"); continue
            names = by_file[f] if n == "*" else {n}
            if n != "*" and n not in by_file[f]:
                errs.append(f"{owner}: claims `{f}::{n}`, which is not an inventory item"); continue
            for nm in names: claims[(f, nm)].append(owner)

    per_module = {}
    declarations = collections.defaultdict(list)
    for lib in libs:
        p = ROOT / "STFSpec/informal/modules" / f"{lib}.md"
        if not p.exists():
            errs.append(f"STFSpec/informal/modules/{lib}.md is missing"); continue
        text = p.read_text()
        sec = sections(text, lib, errs)
        if f'`{release["tag"]}` @{release["commit"][:8]}' not in text.split("## 1.", 1)[0]:
            errs.append(f"{lib}: document pin does not match reference.toml")
        argument = sec.get(7, "").split("### Informal correctness argument", 1)
        if len(argument) != 2:
            errs.append(f"{lib}: §7 lacks its informal correctness argument")
        else:
            for label in ("Claim", "Premises", "Argument", "Open obligations"):
                if f"**{label}.**" not in argument[1]:
                    errs.append(f"{lib}: informal argument lacks {label}")
        sm = sec.get(3, "")
        before = sum(len(v) for v in claims.values())
        claim_all(sm, lib)
        per_module[lib] = sum(len(v) for v in claims.values()) - before
        m = re.search(r"\*\*Depends on:\*\*(.*)", sec.get(8, ""))
        got = set(re.findall(r"`(Eth\w+)`", m.group(1))) if m else None
        want = set(graph[lib])
        if got is None: errs.append(f"{lib}: §8 has no '**Depends on:**' line")
        elif got != want: errs.append(f"{lib}: §8 Depends on {sorted(got)} but import registry says {sorted(want)}")
        code = "\n".join(re.findall(r"^```lean\s*\n(.*?)^```", sec.get(5, ""), re.M | re.S))
        for name in re.findall(r"\b(?:structure|inductive|class|abbrev|def)\s+([A-Za-z][A-Za-z0-9_'.]*)", code):
            if name in contracts["owners"]:
                declarations[name].append(lib)
        for name, owner in contracts["owners"].items():
            if re.search(r"\b" + re.escape(name) + r"\b", code) and lib != owner and owner not in reachable.get(lib, set()):
                errs.append(f"{lib}: interface uses {name} but cannot reach its owner {owner}")
        # P256 names the curve, not a decision.
        for d in set(re.findall(r"\b([DP]\d+)\b", text)) - decisions - {"P256"}:
            errs.append(f"{lib}: mentions decision {d}, which is not in STFSpec/informal/DECISIONS.md")
        # Not after "-" or a letter, so module-local IDs such as R-F4 do not match. F0 is the
        # CREATE opcode byte in opcode tables, not a finding.
        for d in set(re.findall(r"(?<![-\w])([BFQ]\d+)\b", text)) - defined_ids - {"F0"}:
            errs.append(f"{lib}: cites {d}, which is not in STFSpec/informal/DECISIONS.md")
    for name, owner in contracts["owners"].items():
        if owner not in libs:
            errs.append(f"{name}: unknown declaration owner {owner}")
        if declarations[name] != [owner]:
            errs.append(f"{name}: expected one §5 declaration in {owner}, found {declarations[name]}")
    claim_all((ROOT / "STFSpec/informal/EXCLUDED.md").read_text(), "EXCLUDED")

    dup = {k: v for k, v in claims.items() if len(v) > 1}
    for (f, n), owners in sorted(dup.items()):
        errs.append(f"`{f}::{n}` claimed by several: {owners}")
    unclaimed = [i for i in items if (i["file"], i["name"]) not in claims]
    for i in unclaimed:
        errs.append(f"unclaimed: `{i['file']}::{i['name']}` ({i['kind']}, line {i['line']})") if report else None
    if unclaimed:
        errs.append(f"{len(unclaimed)} inventory items are neither claimed nor excluded (run with --report to list them)")

    if report:
        print("claims per module:", json.dumps(per_module, indent=0))
        ext = collections.Counter(i["name"].split(".")[0] for i in inv["items"] if i["kind"] == "external")
        print("external library uses to discuss:", dict(ext))
    for e in errs: print("spec:", e)
    print(f"check_spec: {len(libs)} libraries, {len(items)} inventory items, "
          f"{len(items) - len(unclaimed)} covered, {len(errs)} problems")
    return 1 if errs else 0

if __name__ == "__main__":
    sys.exit(main())
