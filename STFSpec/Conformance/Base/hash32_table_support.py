# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Actual Hash32 whole-value/native regressions against independent nonprotocol arithmetic.

Run after building the core:
python3 STFSpec/Conformance/Base/hash32_table_support.py --output /tmp/evidence
The output directory retains source, commands, failures and current artifact provenance.
This is a functional test, not EELS hashing or a distribution/throughput benchmark.
"""

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import time


def support(value):
    """Independent integer arithmetic, retaining all 32 bytes and wrapping each multiply."""
    acc = 14695981039346656037
    for byte in (value % (1 << 256)).to_bytes(32, "big"):
        acc = ((acc ^ byte) * 1099511628211) % (1 << 64)
    return acc


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probe_source(vectors):
    values = ",\n    ".join(str(value) for value in vectors)
    return '''/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Base.FixedBytes
import Std.Data.HashMap.Lemmas
open STFSpec.Base
namespace Hash32TableProbe
def key (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
def payload (n : Nat) : ByteArray :=
  (Bytes.ofList [UInt8.ofNat n, UInt8.ofNat (n / 256), 170, 85]).toByteArray
def longKey (i : Nat) : Nat := 2 ^ 240 + 257 * i
def observe (label : String) (db : Std.HashMap Hash32 ByteArray) (queries : List Nat) :
    IO Unit := do
  IO.println s!"S|{label}|{db.size}"
  for n in queries do
    let x := key n
    let some reconstructed := Hash32.ofBytes? x.toBytes
      | throw (IO.userError "reconstruction failed")
    if x != reconstructed then throw (IO.userError "key equality failed")
    let value := match db[reconstructed]? with
      | none => "none"
      | some p => toString (Bytes.ofByteArray p).toList
    IO.println s!"M|{label}|{n}|{x.toBytes.toList}|{value}"
def main : IO Unit := do
  let vectors : List Nat := [VALUES]
  for n in vectors do
    let x := key n
    let some y := Hash32.ofBytes? x.toBytes
      | throw (IO.userError "vector reconstruction failed")
    if x != y || hash x != hash y then throw (IO.userError "reconstructed vector failed")
    IO.println s!"V|{n}|{hash x}|{Hash32.tableHashReference x}|{x.toBytes.toList}"
  let tiny : Std.HashMap Hash32 ByteArray := ∅
  let tiny := ((tiny.insert (key 3) (payload 1)).insert (key 8) (payload 2)).insert
    (key (3 + 2 ^ 256)) (payload 3)
  observe "tiny" tiny [3, 8, 3 + 2 ^ 256, 999]
  let mut parent : Std.HashMap Hash32 ByteArray := ∅
  for i in List.range 1024 do parent := parent.insert (key (longKey i)) (payload i)
  let queries := (List.range 1025).map longKey
  observe "parent" parent queries
  let mut latest := parent
  for i in List.range 1024 do
    if i % 3 == 0 then
      latest := latest.insert (key (longKey i + 2 ^ 256)) (payload (i + 32768))
  observe "latest" latest queries
  observe "parentAfter" parent queries
  for sibling in List.range 16 do
    let mut child := parent
    for i in List.range 64 do
      child := child.insert (key (longKey (i * 13))) (payload (sibling * 64 + i + 8192))
    child := child.insert (key (longKey 1024)) (payload (sibling + 61440))
    observe s!"sibling{sibling}" child queries
  observe "parentReleased" parent queries
end Hash32TableProbe
def main := Hash32TableProbe.main
'''.replace("VALUES", values)


def check_output(raw, vectors):
    def require(condition, message):
        if not condition:
            raise AssertionError(message)

    def natural(field, line):
        require(field.isascii() and field.isdecimal(), f"Expected decimal natural: {line}")
        try:
            return int(field)
        except ValueError as error:
            raise AssertionError(f"Invalid natural: {line}") from error

    def byte_list(field, width, line):
        try:
            value = ast.literal_eval(field)
        except (SyntaxError, ValueError) as error:
            raise AssertionError(f"Invalid byte list: {line}") from error
        require(type(value) is list and len(value) == width, f"Expected {width} bytes: {line}")
        require(all(type(byte) is int and 0 <= byte <= 255 for byte in value),
                f"Expected integer bytes in [0, 255]: {line}")
        return value

    observations = []
    expected_maps = {"tiny": {3: [3, 0, 170, 85], 8: [2, 0, 170, 85]}}
    long_key = lambda i: (1 << 240) + 257 * i
    payload = lambda n: [n % 256, (n // 256) % 256, 170, 85]
    parent = {long_key(i): payload(i) for i in range(1024)}
    for name in ("parent", "parentAfter", "parentReleased"):
        expected_maps[name] = parent
    expected_maps["latest"] = {
        long_key(i): payload(i + 32768 if i % 3 == 0 else i) for i in range(1024)}
    for sibling in range(16):
        child = dict(parent)
        child.update({long_key(i * 13): payload(sibling * 64 + i + 8192) for i in range(64)})
        child[long_key(1024)] = payload(sibling + 61440)
        expected_maps[f"sibling{sibling}"] = child
    seen_vectors, sizes, lookups = [], {}, {}
    arity = {"V": 5, "S": 3, "M": 5}
    for line in raw.splitlines():
        fields = line.split("|")
        require(fields[0] in arity and len(fields) == arity[fields[0]],
                f"Unexpected output schema: {line}")
        if fields[0] == "V":
            _, n, actual, reference, content = fields
            n = natural(n, line)
            require(natural(actual, line) == natural(reference, line) == support(n), line)
            require(byte_list(content, 32, line) ==
                    list((n % (1 << 256)).to_bytes(32, "big")), line)
            seen_vectors.append(n)
        elif fields[0] == "S":
            _, label, size = fields
            require(label in expected_maps and label not in sizes, line)
            sizes[label] = natural(size, line)
            require(sizes[label] == len(expected_maps[label]), line)
        elif fields[0] == "M":
            _, label, n, content, actual = fields
            require(label in expected_maps, line)
            n = natural(n, line)
            canonical = n % (1 << 256)
            require(byte_list(content, 32, line) == list(canonical.to_bytes(32, "big")), line)
            value = None if actual == "none" else byte_list(actual, 4, line)
            require(value == expected_maps[label].get(canonical), line)
            lookups.setdefault(label, []).append(n)
        else:
            raise AssertionError(f"Unexpected output: {line}")
        observations.append(line)
    require(seen_vectors == vectors, "Incomplete Hash32 observations")
    require(set(sizes) == set(expected_maps) == set(lookups), "Incomplete Hash32 observations")
    require(lookups["tiny"] == [3, 8, 3 + (1 << 256), 999], "Incomplete Hash32 observations")
    for label in set(expected_maps) - {"tiny"}:
        require(lookups[label] == [long_key(i) for i in range(1025)],
                f"Incomplete Hash32 lookups: {label}")
    return {"vectors": len(vectors), "maps": len(sizes),
            "whole_key_payload_lookups": sum(map(len, lookups.values())),
            "observations": len(observations)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("use default Python mode for native provenance checks; parser tests support -O")
    root = Path(__file__).resolve().parents[3]
    out = args.output.resolve()
    if out == root or root in out.parents:
        parser.error("evidence output must be outside the candidate source tree")
    out.mkdir(parents=True, exist_ok=False)
    commands, provenance = [], {}

    def run(label, argv, *, env=None):
        start = time.monotonic()
        result = subprocess.run(list(map(str, argv)), cwd=root, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / f"{label}.log").write_bytes(result.stdout)
        commands.append({"label": label, "argv": list(map(str, argv)), "cwd": str(root),
                         "env_override": None if env is None else {"LEAN_PATH": env["LEAN_PATH"]},
                         "exit": result.returncode, "seconds": time.monotonic() - start,
                         "log": f"{label}.log"})
        (out / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        print(f"{label}: exit {result.returncode}", flush=True)
        if result.returncode:
            raise RuntimeError(f"{label} failed; see {out / (label + '.log')}")
        return result.stdout

    run("package-current-native", ["lake", "build", "EthBase:static", "--wfail"])
    toolchain = Path(run("toolchain", ["lake", "env", "lean", "--print-prefix"]).decode().strip())
    fresh = out / "fresh"

    def current_imports(source):
        """Resolve source imports by module name, replacing historical setup paths."""
        imports = {}
        for line in source.splitlines():
            if not line.startswith("import "):
                continue
            for name in line.split()[1:]:
                relative = Path(*name.split(".")).with_suffix(".olean")
                if name.startswith("STFSpec."):
                    artifact = fresh / relative
                    if not artifact.is_file():
                        artifact = root / ".lake/build/lib/lean" / relative
                else:
                    artifact = toolchain / "lib/lean" / relative
                assert artifact.is_file(), f"Missing current import {name}: {artifact}"
                parts = [artifact]
                for suffix in (".olean.server", ".olean.private"):
                    part = artifact.with_suffix(suffix)
                    if part.is_file():
                        parts.append(part)
                ir = [artifact.with_suffix(suffix) for suffix in (".ir.sig", ".ir")
                      if artifact.with_suffix(suffix).is_file()]
                imports[name] = [[str(part) for part in parts]]
                if ir:
                    imports[name].append([str(part) for part in ir])
                provenance.setdefault("imports", {})[name] = {
                    str(part): digest(part) for part in parts + ir}
        return imports

    for module in ("Bytes", "FixedBytes"):
        stem = fresh / "STFSpec/Base" / module
        stem.parent.mkdir(parents=True, exist_ok=True)
        setup = json.loads((root / f".lake/build/ir/STFSpec/Base/{module}.setup.json").read_text())
        setup["importArts"] = current_imports((root / f"STFSpec/Base/{module}.lean").read_text())
        setup_file = stem.with_suffix(".setup.json")
        setup_file.write_text(json.dumps(setup, indent=2) + "\n")
        run(f"fresh-{module}", ["lake", "env", "lean", "--setup", setup_file,
                               "-o", stem.with_suffix(".olean"), "-c", stem.with_suffix(".c"),
                               f"STFSpec/Base/{module}.lean", "-DwarningAsError=true"])
        for suffix, built in ((".olean", f".lake/build/lib/lean/STFSpec/Base/{module}.olean"),
                              (".c", f".lake/build/ir/STFSpec/Base/{module}.c")):
            assert stem.with_suffix(suffix).read_bytes() == (root / built).read_bytes(), built
        flags = ["-O3", "-DNDEBUG", "-DLEAN_EXPORTING", "-Werror"]
        run(f"compile-{module}", ["lake", "env", "leanc", "-c", stem.with_suffix(".c"),
                                 "-o", stem.with_suffix(".o"), *flags])
        provenance[module] = {"source": digest(root / f"STFSpec/Base/{module}.lean"),
                              "setup": digest(setup_file),
                              "olean": digest(stem.with_suffix(".olean")),
                              "c": digest(stem.with_suffix(".c")),
                              "object": digest(stem.with_suffix(".o"))}
    archive = out / "libHash32Providers.a"
    objects = [fresh / f"STFSpec/Base/{module}.o" for module in ("Bytes", "FixedBytes")]
    run("archive-create", ["ar", "rcs", archive, *objects])
    for module, obj in zip(("Bytes", "FixedBytes"), objects):
        extracted = run(f"archive-member-{module}", ["ar", "p", archive, obj.name])
        assert extracted == obj.read_bytes()
    rng = random.Random(0x3832)
    vectors = [0, 1, 3, 8, (1 << 256) - 1, 3 + (1 << 256)]
    vectors += [1 << bit for bit in range(256)]
    vectors += [byte << (8 * position) for position in range(32) for byte in (1, 128, 255)]
    vectors += [int.from_bytes(bytes(range(32)), "big"),
                int.from_bytes(bytes(reversed(range(32))), "big")]
    vectors += [rng.getrandbits(256) for _ in range(128)]
    source = out / "Hash32TableProbe.lean"
    source.write_text(probe_source(vectors))
    setup = {"plugins": [], "dynlibs": [], "name": "Hash32TableProbe", "isModule": False,
             "options": {"autoImplicit": False, "relaxedAutoImplicit": False},
             "importArts": current_imports(source.read_text())}
    setup_file = out / "Hash32TableProbe.setup.json"
    setup_file.write_text(json.dumps(setup, indent=2) + "\n")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(fresh) + os.pathsep + str(root / ".lake/build/lib/lean")
    run("probe-elaborate", [toolchain / "bin/lean", "--setup", setup_file, source,
                            "-o", out / "Hash32TableProbe.olean", "-c", out / "Hash32TableProbe.c",
                            "-DwarningAsError=true"], env=env)
    source_output = run("source-evaluate", [toolchain / "bin/lean", "--setup", setup_file,
                                           "--run", source], env=env)
    run("probe-compile", ["lake", "env", "leanc", "-c", out / "Hash32TableProbe.c",
                          "-o", out / "Hash32TableProbe.o", "-O3", "-Werror"])
    run("probe-link", ["lake", "env", "leanc", out / "Hash32TableProbe.o", archive,
                       "-o", out / "hash32-table-probe",
                       "-Wl,-Map=" + str(out / "native-link.map")])
    native_output = run("native-evaluate", [out / "hash32-table-probe"])
    assert native_output == source_output, "native/source complete observation mismatch"
    summary = check_output(native_output.decode(), vectors)
    run("native-symbols", ["nm", "-u", *objects, out / "Hash32TableProbe.o"])
    for file in (source, out / "Hash32TableProbe.c", out / "Hash32TableProbe.o",
                 archive, out / "hash32-table-probe", setup_file, out / "native-link.map"):
        provenance[str(file.relative_to(out))] = digest(file)
    provenance["toolchain"] = str(toolchain)
    provenance["script"] = digest(Path(__file__))
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
