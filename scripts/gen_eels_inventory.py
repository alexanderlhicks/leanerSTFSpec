#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Generate STFSpec/informal/eels-inventory.json from the pinned execution-specs release.

Usage: gen_eels_inventory.py EELS_CHECKOUT [--check]
The checkout must be at reference.toml's release.commit (checked). Every top-level
function, class (with its methods) and module-level constant in the in-scope files is
recorded with its line number. The scope is the Amsterdam fork package plus the shared modules
it uses; scripts/check_spec.py requires each entry to be claimed by exactly one spec guidance document
or excluded with a reason.
"""
import argparse, ast, json, pathlib, subprocess, sys, tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCOPE = ["src/ethereum/forks/amsterdam", "src/ethereum/state.py", "src/ethereum/state_mpt.py",
         "src/ethereum/merkle_patricia_trie.py", "src/ethereum/exceptions.py",
         "src/ethereum/crypto", "src/ethereum/utils",
         # previous-fork header, used by stateless.py for transition-period headers
         "src/ethereum/forks/bpo5/blocks.py"]

EXTERNAL = ("ethereum_rlp", "ethereum_types", "remerkleable", "py_ecc", "Crypto", "cryptography",
            "spec256k1", "coincurve", "hashlib", "ckzg", "eth_typing")

def items(path: pathlib.Path, rel: str):
    tree = ast.parse(path.read_text(), filename=rel)
    # External semantics: names imported from non-ethereum libraries (their behaviour is part
    # of the reference semantics and must be specified too).
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module and node.module.split(".")[0] in EXTERNAL:
            for a in node.names:
                yield {"file": rel, "name": f"{node.module}.{a.name}", "kind": "external", "line": node.lineno}
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name.split(".")[0] in EXTERNAL:
                    yield {"file": rel, "name": a.name, "kind": "external", "line": node.lineno}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield {"file": rel, "name": node.name, "kind": "function", "line": node.lineno}
        elif isinstance(node, ast.ClassDef):
            yield {"file": rel, "name": node.name, "kind": "class", "line": node.lineno}
            for sub in node.body:
                if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    yield {"file": rel, "name": f"{node.name}.{sub.name}", "kind": "method", "line": sub.lineno}
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for t in targets:
                if isinstance(t, ast.Name) and t.id.isupper() or (isinstance(t, ast.Name) and t.id[:1].isupper() and "_" in t.id):
                    yield {"file": rel, "name": t.id, "kind": "constant", "line": node.lineno}

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("eels", type=pathlib.Path)
    parser.add_argument("--check", action="store_true", help="compare without rewriting the inventory")
    args = parser.parse_args()
    eels = args.eels.resolve()
    commit = tomllib.loads((ROOT / "reference.toml").read_text())["release"]["commit"]
    head = subprocess.run(["git", "-C", str(eels), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head != commit:
        print(f"checkout is at {head}, reference.toml pins {commit}"); return 1
    status = subprocess.run(["git", "-C", str(eels), "status", "--porcelain", "--", "src", "uv.lock"],
                            capture_output=True, text=True, check=True)
    if status.stdout:
        print("checkout source or uv.lock has local changes"); return 1
    out = []
    for s in SCOPE:
        p = eels / s
        files = sorted(p.rglob("*.py")) if p.is_dir() else [p]
        for f in files:
            if "__pycache__" in f.parts: continue
            rel = str(f.relative_to(eels / "src/ethereum"))
            out.extend(items(f, rel))
    doc = {"release": commit, "scope": SCOPE, "items": out}
    rendered = json.dumps(doc, indent=1) + "\n"
    target = ROOT / "STFSpec/informal/eels-inventory.json"
    if args.check:
        if not target.exists() or target.read_text() != rendered:
            print("STFSpec/informal/eels-inventory.json differs from the pinned source; regenerate it"); return 1
    else:
        target.write_text(rendered)
    kinds = {}
    for i in out: kinds[i["kind"]] = kinds.get(i["kind"], 0) + 1
    print(f"{len(out)} items in {len({i['file'] for i in out})} files: {kinds}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
