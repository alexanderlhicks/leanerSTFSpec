# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Fresh source/native complete NodeDB regressions against pinned-source observations.

Run python3 scripts/test_node_db.py --observations OUT/NodeDBSource.observations.json
--output OUT/native. Evidence must be outside the candidate. Finite functional
construction and sibling observations do not establish table costs or security.
"""

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def array(raw):
    return "⟨#[" + ", ".join(str(b) for b in raw) + "]⟩"


def probe_source(cases):
    calls = []
    for case in cases:
        entries = "#[" + ", ".join(array(bytes.fromhex(b)) for b in case["entries"]) + "]"
        calls.append(f'  observe "id{case["case"]}" (NodeDB.build (m := Id) {entries})')
    return '''/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.NodeDB
open STFSpec.Base STFSpec.Hash STFSpec.Commit
namespace NodeDBProbe
def key (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
def payload (n : Nat) : ByteArray :=
  (Bytes.ofList [UInt8.ofNat (n / 256), UInt8.ofNat n, 170, 85]).toByteArray
structure Trace where
  seen : Array ByteArray := #[]
  mode : Nat := 0
  failAt : Option Nat := none
abbrev Recording := StateM Trace
def query (b : ByteArray) : Recording Hash32 := fun s =>
  let n := Uint.ofBeBytes (Bytes.ofByteArray b)
  let answer := if s.mode == 0 then 2^(64 * s.seen.size) + 7
    else if s.mode == 1 then 2^255 + 7
    else if s.mode == 2 then 2^(n / 65536)
    else 2^240 + 257 * (n / 65536)
  (key answer, { s with seen := s.seen.push b })
instance : KeccakQuery Recording where
  keccak := query
def observe (label : String) (db : NodeDB) : IO Unit := do
  IO.println s!"S|{label}|{db.map.size}"
  let items := db.map.toList.mergeSort (fun x y => x.1.toNat ≤ y.1.toNat)
  for (h, b) in items do
    let some reconstructed := Hash32.ofBytes? h.toBytes
      | throw (IO.userError "key reconstruction failed")
    if db.map[reconstructed]? != some b then throw (IO.userError "reconstructed lookup failed")
    IO.println s!"M|{label}|{h.toNat}|{h.toBytes.toList}|{(Bytes.ofByteArray b).toList}"
  for h in [key 0, key 999999, key (2^256 - 1)] do
    let result := match db.map[h]? with
      | none => "none"
      | some b => toString (Bytes.ofByteArray b).toList
    IO.println s!"Q|{label}|{h.toNat}|{result}"
def trace (label : String) (s : Trace) : IO Unit := do
  for b in s.seen do IO.println s!"T|{label}|{(Bytes.ofByteArray b).toList}"
def failing (b : ByteArray) : ExceptT Nat Recording Hash32 := ExceptT.mk fun s =>
  if s.failAt = some s.seen.size then
    (.error s.seen.size, { s with seen := s.seen.push b })
  else let (h, next) := query b s; (.ok h, next)
def main : IO Unit := do
CALLS
  let entries : Array ByteArray := #[⟨#[]⟩, ⟨#[255]⟩, ⟨#[]⟩, ⟨#[128, 0]⟩]
  for mode in [0, 1] do
    let label := s!"control{mode}"
    let (db, s) := (NodeDB.build (m := Recording) entries).run { mode := mode }
    observe label db
    trace label s
  let (empty, emptyTrace) := (NodeDB.build (m := Recording) #[]).run {}
  observe "empty" empty
  trace "empty" emptyTrace
  let ((result, added), s) :=
    ((NodeDB.build (m := ExceptT String (StateT Nat Recording)) entries).run.run 91).run {}
  match result with
  | .error _ => throw (IO.userError "lift failure")
  | .ok db =>
    IO.println s!"L|forward|{added}"
    observe "forward" db
    trace "forward" s
  let (result, s) :=
    ((NodeDB.build (m := StateT Nat (ExceptT String Recording)) entries).run 91).run.run {}
  match result with
  | .error _ => throw (IO.userError "reverse lift failure")
  | .ok (db, added) =>
    IO.println s!"L|reverse|{added}"
    observe "reverse" db
    trace "reverse" s
  let markers := (List.range 256).toArray.map payload
  let (db, s) := (NodeDB.build (m := Recording) markers).run { mode := 2 }
  observe "markers" db
  trace "markers" s
  let large := (List.range 1024).toArray.map payload
  let (parent, s) := (NodeDB.build (m := Recording) large).run { mode := 3 }
  observe "large" parent
  trace "large" s
  for sibling in List.range 8 do
    let more := (List.range 64).toArray.map fun n =>
      (Bytes.ofList [UInt8.ofNat (n / 256), UInt8.ofNat n,
        UInt8.ofNat sibling, 0]).toByteArray
    let (db, s) := (NodeDB.buildReference (m := Recording) more.toList parent).run { mode := 3 }
    observe s!"sibling{sibling}" db
    trace s!"sibling{sibling}" s
  observe "parentAfter" parent
  letI : KeccakQuery (ExceptT Nat Recording) := ⟨failing⟩
  for n in List.range 4 do
    let (result, s) :=
      (NodeDB.build (m := ExceptT Nat Recording) entries).run.run { failAt := some n }
    match result with
    | .ok _ => throw (IO.userError "expected failure")
    | .error e => IO.println s!"F|failure{n}|{e}"
    trace s!"failure{n}" s
end NodeDBProbe
def main := NodeDBProbe.main
'''.replace("CALLS", "\n".join(calls))


def check_output(raw, cases):
    expected = {f'id{c["case"]}': {int(item["key"], 16): bytes.fromhex(item["value"])
                                  for item in c["items"]} for c in cases}
    small = [b"", b"\xff", b"", b"\x80\x00"]
    controlled = {(1 << (64 * i)) + 7: b for i, b in enumerate(small)}
    expected.update(control0=controlled, control1={(1 << 255) + 7: small[-1]}, empty={},
                    forward=controlled, reverse=controlled)
    payload = lambda n: bytes([n // 256, n % 256, 170, 85])
    expected["markers"] = {1 << i: payload(i) for i in range(256)}
    parent = {(1 << 240) + 257 * i: payload(i) for i in range(1024)}
    expected["large"] = parent
    expected["parentAfter"] = parent
    for sibling in range(8):
        child = dict(parent)
        child.update({(1 << 240) + 257 * i: bytes([0, i, sibling, 0]) for i in range(64)})
        expected[f"sibling{sibling}"] = child
    traces = {"empty": [], "control0": small, "control1": small, "forward": small, "reverse": small,
              "markers": [payload(i) for i in range(256)], "large": [payload(i) for i in range(1024)]}
    traces.update({f"sibling{s}": [bytes([0, i, s, 0]) for i in range(64)] for s in range(8)})
    traces.update({f"failure{n}": small[:n + 1] for n in range(4)})
    sizes, observed, actual_traces, queries, failures, lifts = {}, {}, {}, {}, {}, {}
    for line in raw.splitlines():
        fields = line.split("|")
        kind, label = fields[:2]
        if kind == "S":
            assert label not in sizes and int(fields[2]) == len(expected[label]), line
            sizes[label] = int(fields[2])
            observed[label] = {}
        elif kind == "M":
            n = int(fields[2])
            assert ast.literal_eval(fields[3]) == list(n.to_bytes(32, "big")), line
            value = bytes(ast.literal_eval(fields[4]))
            assert n not in observed[label] and expected[label][n] == value, line
            observed[label][n] = value
        elif kind == "Q":
            n = int(fields[2])
            value = None if fields[3] == "none" else bytes(ast.literal_eval(fields[3]))
            assert value == expected[label].get(n), line
            queries.setdefault(label, []).append(n)
        elif kind == "T":
            actual_traces.setdefault(label, []).append(bytes(ast.literal_eval(fields[2])))
        elif kind == "F":
            assert label not in failures
            failures[label] = int(fields[2])
        elif kind == "L":
            assert label not in lifts
            lifts[label] = int(fields[2])
        else:
            raise AssertionError(line)
    assert observed == expected and set(sizes) == set(expected)
    assert queries == {label: [0, 999999, (1 << 256) - 1] for label in expected}
    assert {label: actual_traces.get(label, []) for label in traces} == traces
    assert set(actual_traces) == set(traces) - {"empty"}
    assert failures == {f"failure{n}": n for n in range(4)} and lifts == {"forward": 91, "reverse": 91}
    return {"maps": len(expected), "full_key_value_observations": sum(map(len, expected.values())),
            "missing_or_present_queries": sum(map(len, queries.values())),
            "ordered_queries": sum(map(len, traces.values())), "failure_positions": len(failures)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--observations", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root, out = Path(__file__).resolve().parents[1], args.output.resolve()
    if out.is_relative_to(root):
        parser.error("output must be outside the candidate")
    out.mkdir(parents=True, exist_ok=False)
    cases = json.loads(args.observations.read_text())["concrete"]
    commands, provenance = [], {}

    def run(label, argv, *, env=None):
        started = time.monotonic()
        result = subprocess.run(list(map(str, argv)), cwd=root, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = out / (label + ".log")
        log.write_bytes(result.stdout)
        commands.append({"label": label, "argv": list(map(str, argv)), "cwd": str(root),
                         "env_override": None if env is None else {"LEAN_PATH": env["LEAN_PATH"]},
                         "exit": result.returncode, "seconds": time.monotonic() - started,
                         "log": str(log), "sha256": digest(log)})
        (out / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        print(label + ": " + str(result.returncode), flush=True)
        if result.returncode:
            raise RuntimeError(f"{label} failed: {log}")
        return result.stdout

    run("package-build", ["lake", "build", "EthBase:static", "EthHash:static", "EthCodec:static",
                          "EthCommit:static", "--wfail"])
    toolchain = Path(run("toolchain", ["lake", "env", "lean", "--print-prefix"]).decode().strip())
    modules = ["STFSpec.Base.Bytes", "STFSpec.Base.FixedBytes", "STFSpec.Base.ValueRecords",
               "STFSpec.Hash.KeccakPermutation", "STFSpec.Hash.KeccakSponge", "STFSpec.Hash.KeccakQuery",
               "STFSpec.Commit.NodeDB"]
    fresh, objects = out / "fresh", []
    for module in modules:
        path = Path(*module.split("."))
        source, stem = root / path.with_suffix(".lean"), fresh / path
        stem.parent.mkdir(parents=True, exist_ok=True)
        # Ask Lake for the current actual module's setup, with no inherited cache path.
        current_setup = run("setup-" + module, ["lake", "setup-file", str(source)])
        setup = json.loads(current_setup)
        assert setup["name"] == module and setup["package"] == "stfspec"
        for dep in setup["importArts"]:
            dep_path = Path(*dep.split(".")).with_suffix(".olean")
            local = fresh / dep_path
            if not local.is_file():
                local = root / ".lake/build/lib/lean" / dep_path
            assert local.is_file() and (local.resolve().is_relative_to(fresh) or
                                       local.resolve().is_relative_to(root / ".lake/build"))
            setup["importArts"][dep] = [[str(local)]]
        setup_file = stem.with_suffix(".setup.json")
        setup_file.write_text(json.dumps(setup, indent=2) + "\n")
        run("emit-" + module, ["lake", "env", "lean", "--setup", setup_file, source,
                              "-o", stem.with_suffix(".olean"), "-c", stem.with_suffix(".c"),
                              "-DwarningAsError=true"])
        for suffix, folder in [(".olean", "lib/lean"), (".c", "ir")]:
            assert stem.with_suffix(suffix).read_bytes() == (
                root / ".lake/build" / folder / path.with_suffix(suffix)).read_bytes()
        obj = out / (module + ".o")
        run("compile-" + module, ["lake", "env", "leanc", "-c", stem.with_suffix(".c"),
                                  "-o", obj, "-O3", "-DNDEBUG", "-DLEAN_EXPORTING", "-Werror"])
        objects.append(obj)
        provenance[module] = {"source": digest(source), "c": digest(stem.with_suffix(".c")),
                              "olean": digest(stem.with_suffix(".olean")), "object": digest(obj),
                              "setup": digest(setup_file), "imports": setup["importArts"]}
    archive = out / "libNodeDBProviders.a"
    run("archive", ["ar", "rcs", archive, *objects])
    for obj in objects:
        assert run("archive-member-" + obj.stem, ["ar", "p", archive, obj.name]) == obj.read_bytes()
    probe = out / "NodeDBProbe.lean"
    probe.write_text(probe_source(cases))
    setup = json.loads((fresh / "STFSpec/Commit/NodeDB.setup.json").read_text())
    setup["name"] = "NodeDBProbe"
    setup.pop("package")
    setup["importArts"]["STFSpec.Commit.NodeDB"] = [[str(fresh / "STFSpec/Commit/NodeDB.olean")]]
    setup_file = out / "NodeDBProbe.setup.json"
    setup_file.write_text(json.dumps(setup, indent=2) + "\n")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(fresh) + os.pathsep + str(root / ".lake/build/lib/lean")
    run("probe-emit", [toolchain / "bin/lean", "--setup", setup_file, probe,
                       "-o", out / "NodeDBProbe.olean", "-c", out / "NodeDBProbe.c",
                       "-DwarningAsError=true"], env=env)
    source = run("source-run", [toolchain / "bin/lean", "--setup", setup_file, "--run", probe], env=env)
    run("probe-compile", ["lake", "env", "leanc", "-c", out / "NodeDBProbe.c", "-o",
                          out / "NodeDBProbe.o", "-O3", "-DNDEBUG", "-Werror"])
    packages = [root / ".lake/build/lib" / ("libstfspec_" + name + ".a")
                for name in ["EthCodec", "EthHash", "EthBase"]]
    run("link", ["lake", "env", "leanc", out / "NodeDBProbe.o", archive, *packages,
                 "-o", out / "node-db-probe", "-Wl,-Map=" + str(out / "native-link.map")])
    native = run("native-run", [out / "node-db-probe"])
    assert native == source, "source/native complete observations differ"
    summary = check_output(native.decode(), cases)
    linkmap = (out / "native-link.map").read_text()
    for obj in objects:
        assert archive.name + "(" + obj.name + ")" in linkmap, obj
    run("symbols", ["nm", "-u", *objects, out / "NodeDBProbe.o"])
    run("defined-symbols", ["nm", "--defined-only", out / "node-db-probe"])
    for path in list(out.rglob("*")):
        if path.is_file():
            provenance[str(path.relative_to(out))] = digest(path)
    provenance["script"] = digest(Path(__file__))
    provenance["observations"] = digest(args.observations)
    provenance["package_archives"] = {str(p): digest(p) for p in packages}
    provenance["toolchain"] = str(toolchain)
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
