#!/usr/bin/env python3
"""Compare pinned EELS get_code with a complete Lean code-read stream.

From the repository root, after capturing the native and interpreted targets:
  uv run --no-project --python 3.12 python -B \
    STFSpec/Conformance/State/code_read_source.py --eels EELS \
    --check-target .lake/code-read-native.jsonl --check-target .lake/code-read-interpreted.jsonl \
    --report REPORT.json

The driver invokes the frozen EELS/.venv/bin/python -I -B directly, normally and
with -O. Every actual worker compiles filesystem source using the shared import
policy and returns its own runtime and compiled-source authentication. The report
keeps the original streams and waits. EELS and its installed files are read-only.
"""

import argparse
import dataclasses
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("code_read_differential",
                                              HERE / "code_read_differential.py")
READER = importlib.util.module_from_spec(SPEC)
exec(compile(Path(SPEC.origin).read_bytes(), SPEC.origin, "exec"), READER.__dict__)
AUTH = READER.load_source("pre_state_account_source")
ROOT = AUTH.ROOT
SOURCE_MODULES = {
    "ethereum.forks.amsterdam.state_tracker": "src/ethereum/forks/amsterdam/state_tracker.py",
    "ethereum.state": "src/ethereum/state.py",
}


def probe():
    from ethereum.forks.amsterdam.state_tracker import BlockState, TransactionState, get_code
    from ethereum.state import Account, EMPTY_CODE_HASH
    from ethereum_types.bytes import Bytes, Bytes20, Bytes32
    from ethereum_types.numeric import Uint, U256

    def address(n):
        return Bytes20(n.to_bytes(20, "big"))

    def digest(n):
        return Bytes32(n.to_bytes(32, "big"))

    def number(value):
        return int.from_bytes(value, "big")

    def code_map(entries):
        return {Bytes32(bytes.fromhex(key)): Bytes(bytes.fromhex(data)) for key, data in entries}

    def sorted_map(entries, key, val):
        return [[key(k), val(v)] for k, v in sorted(entries.items())]

    def account(a):
        return None if a is None else [int(a.nonce), int(a.balance), number(a.code_hash)]

    def observe_code(entries):
        return sorted_map(entries, number, list)

    observers = {
        "account_reads": lambda xs: sorted(map(number, xs)),
        "account_writes": lambda xs: sorted_map(xs, number, account),
        "storage_reads": lambda xs: sorted([number(a), number(k)] for a, k in xs),
        "storage_writes": lambda xs: sorted_map(xs, number, lambda slots: sorted_map(slots, number, int)),
        "code_reads": lambda xs: sorted(map(number, xs)),
        "code_writes": observe_code,
        "oldest_ancestor_offset": lambda n: None if n is None else int(n),
        "storage_clears": lambda xs: sorted(map(number, xs)),
        "created_accounts": lambda xs: sorted(map(number, xs)),
        "transient_storage": lambda xs: sorted([number(a), number(k), int(v)] for (a, k), v in xs.items()),
    }

    def snapshot(tx):
        def frame(carrier, excluded):
            return {field.name: observers[field.name](getattr(carrier, field.name))
                    for field in dataclasses.fields(carrier) if field.name not in excluded}
        return {"block": frame(tx.parent, {"pre_state"}),
                "tx": frame(tx, {"parent", "code_reads"})}

    def fill(carrier, salt, entries):
        first, second = address(salt), address(salt + 1)
        carrier.account_reads = {first, address(salt + 4)}
        carrier.account_writes = {first: None, second: Account(
            Uint(2**80 + salt), U256(2**256 - 1), digest(salt + 2))}
        carrier.storage_reads = {(first, digest(17)), (second, digest(19))}
        carrier.storage_writes = {first: {}, second: {digest(17): U256(0), digest(19): U256(2**256 - 1)}}
        carrier.code_writes = code_map(entries)
        carrier.storage_clears = {first, address(salt + 3)}

    class ReadSet(set):
        def __init__(self, initial):
            super().__init__(initial)
            self.adds = []

        def add(self, value):
            self.adds.append(number(value))
            super().add(value)

    class Provider:
        def __init__(self, entries):
            self.code = code_map(entries)
            self.calls = []
            self.observed = []
            self.observed_add_counts = []

        def get_code(self, queried):
            self.calls.append([0, number(queried)])
            self.observed.append(queried in tx.code_reads)
            self.observed_add_counts.append(len(tx.code_reads.adds))
            return self.code[queried]

    for recipe in READER.recipes():
        if not recipe["sourceComparable"]:
            continue
        if Bytes32(bytes.fromhex(recipe["emptyCodeHash"])) != EMPTY_CODE_HASH:
            raise ValueError("source recipe uses a different reserved hash")
        key = Bytes32(bytes.fromhex(recipe["hash"]))
        provider = Provider(recipe["provider"])
        block = BlockState(provider)
        fill(block, 31, recipe["block"])
        block.code_reads = {digest(41), digest(43)}
        block.oldest_ancestor_offset = Uint(2**420 + 3)
        tx = TransactionState(block)
        fill(tx, 61, recipe["tx"])
        reads = ReadSet(Bytes32(bytes.fromhex(key)) for key in recipe["old_reads"])
        tx.code_reads = reads
        tx.created_accounts = {address(71), address(75)}
        tx.transient_storage = {(address(62), digest(17)): U256(0),
                                (address(63), digest(19)): U256(2**256 - 1)}
        row = {"id": recipe["id"], "frameBefore": snapshot(tx), "attempts": []}
        for _ in range(recipe["repeat"]):
            provider.calls.clear()
            provider.observed.clear()
            provider.observed_add_counts.clear()
            reads.adds.clear()
            try:
                answer = {"ok": list(get_code(tx, key))}
            except KeyError as error:
                if type(error) is not KeyError or error.args != (key,):
                    raise
                answer = {"error": {"keyError": number(error.args[0])}}
            if tx.parent is not block or block.pre_state is not provider or tx.code_reads is not reads:
                raise ValueError("source carrier identity changed")
            members = sorted(map(number, reads))
            failed = "error" in answer
            row["attempts"].append({"answer": answer, "calls": provider.calls.copy(),
                "reads": None if failed else members, "frame": snapshot(tx),
                "failedSourceReads": members if failed else None,
                "providerObservedReads": provider.observed.copy(),
                "providerObservedAddCounts": provider.observed_add_counts.copy(),
                "readAdds": reads.adds.copy()})
        row["providerCode"] = observe_code(provider.code)
        yield row


def worker(eels):
    policy = AUTH.install_source_only_imports()
    observations = "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in probe())
    return {"authentication": AUTH.authenticate(eels, policy, operation_name="get_code"),
            "observations": observations}


def read_worker(data, mode, identity, executable):
    envelope = READER.decode(data)
    if type(envelope) is not dict or envelope.keys() != {"authentication", "observations"}:
        raise READER.AdmissionError("invalid probe envelope")
    auth = envelope["authentication"]
    if type(auth) is not dict:
        raise READER.AdmissionError("invalid probe authentication")
    READER.strict_equal([auth.get("optimize"), auth.get("isolated"), auth.get("dont_write_bytecode")],
                        [mode, 1, True], "source worker flags")
    READER.strict_equal(auth["executable"], executable, "interpreter")
    recorded = {entry["path"]: entry for entry in identity["files"]}
    imports = auth["imported_files"]
    loading = auth["source_loading"]
    READER.strict_equal(loading["policy"], "compile-source-without-bytecode-cache")
    for name, imported in zip(SOURCE_MODULES, imports[:2], strict=True):
        compiled = loading["compiled_sources"][name]
        READER.strict_equal(compiled, imported, name)
        READER.strict_equal(compiled, recorded[compiled["path"]], name)
    for name, imported in zip(("ethereum_types.numeric", "ethereum_types.bytes"), imports[2:], strict=True):
        READER.strict_equal(loading["compiled_sources"][name], imported, name)
    if type(auth["operation_source"]) is not str or not auth["operation_source"].startswith("def get_code("):
        raise READER.AdmissionError("incorrect source operation")
    stream = envelope["observations"]
    if type(stream) is not str:
        raise READER.AdmissionError("invalid probe stream")
    return auth, stream, READER.parse_stream(stream.encode(), source=True)


def compare_targets(target_rows, source_rows):
    target_by_id = {row["id"]: row for row in target_rows}
    for source in source_rows:
        target = target_by_id[source["id"]]
        READER.strict_equal(source["frameBefore"], target["frameBefore"], source["id"])
        for s, t in zip(source["attempts"], target["attempts"], strict=True):
            for key in ("calls", "reads"):
                READER.strict_equal(s[key], t[key], key)
            if "ok" in s["answer"]:
                READER.strict_equal(s["answer"], t["answer"], "code bytes")
                READER.strict_equal(s["frame"], t["frame"], "success frame")
            else:
                digest = s["answer"]["error"]["keyError"]
                READER.strict_equal(t["answer"], {"error": {"witness": {"missing": {"code": digest}}}},
                                    "bounded missing-code correspondence")
                READER.strict_equal(t["frame"], None, "failed target transaction state")


def compare(eels, targets, report):
    executable = eels / ".venv/bin/python"
    paths = [Path(__file__).resolve(), Path(SPEC.origin), READER.INPUT, Path(AUTH.__file__),
             HERE / "account_optional_differential.py", HERE / "pre_state_account_differential.py",
             ROOT / "reference.toml", executable, *targets]
    report["inputs_before"] = [AUTH.file_identity(path) for path in paths]
    report["source_before"] = AUTH.source_identity(eels, report)
    target_rows = [READER.parse_stream(target.read_bytes()) for target in targets]
    checked = []
    for mode, flags in enumerate(([], ["-O"])):
        argv = [executable, "-I", "-B", *flags, Path(__file__).resolve(), "--worker", "--eels", eels]
        data = AUTH.run_child(argv, report)
        checked.append(read_worker(data, mode, report["source_before"], AUTH.file_identity(executable)))
    (normal_auth, normal, source_rows), (optimized_auth, optimized, _) = checked
    AUTH.check_authentication(normal_auth, optimized_auth)
    READER.strict_equal(normal, optimized, "source observations in both modes")
    for rows in target_rows:
        compare_targets(rows, source_rows)
    report["source_after"] = AUTH.source_identity(eels, report)
    report["inputs_after"] = [AUTH.file_identity(path) for path in paths]
    READER.strict_equal(report["source_after"], report["source_before"])
    READER.strict_equal(report["inputs_after"], report["inputs_before"])
    report.update(status="PASS", cases=len(source_rows), target_cases=len(target_rows[0]),
                  targets=len(target_rows), source_modes_byte_equal=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eels", required=True, type=Path)
    parser.add_argument("--check-target", action="append", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    eels = args.eels.resolve()
    if args.worker:
        print(json.dumps(worker(eels), separators=(",", ":")))
        return
    if not args.check_target or args.report is None:
        parser.error("--check-target and --report are required")
    targets = [path.resolve() for path in args.check_target]
    destination = args.report.resolve()
    if destination.is_relative_to(eels) or destination.is_relative_to(HERE) or destination in targets:
        parser.error("report must be outside EELS, the conformance source directory and the targets")
    report = {"status": "FAILED", "executions": []}
    with destination.open("x") as output:
        try:
            compare(eels, targets, report)
        except Exception as error:
            report["error"] = type(error).__name__ + ": " + str(error)
            raise
        finally:
            json.dump(report, output, indent=2)
            output.write("\n")
    print(f"PASS code-read source: {report['cases']} authenticated normal/-O observations")


if __name__ == "__main__":
    main()
