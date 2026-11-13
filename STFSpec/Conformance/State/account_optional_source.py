#!/usr/bin/env python3
"""Reproduce bounded current-optional-account comparisons against a supplied pinned EELS clone.

From the repository root, after building/capturing the native target:
  uv run --no-project --python 3.12 python -B \
    STFSpec/Conformance/State/account_optional_source.py --eels EELS \
    --check-target .lake/account-optional-native.jsonl --report REPORT.json

EELS must contain its frozen installed .venv. This driver never installs packages or
writes to EELS. It invokes EELS/.venv/bin/python -I -B directly, normally and with -O.
The report retains complete original child streams, actual waits, source/import/runtime
identities and pinned versions plus installed RECORD integrity. It does not authenticate
an independently downloaded wheel. Probe exceptions are fixture instrumentation, not a
production Python-to-WitnessError adapter. Source failed reads are separate from Lean's
absent returned failed state. Hash-only codeReads does not supply full-state refinement.
"""

import argparse
import base64
import csv
import dataclasses
import hashlib
import importlib.metadata
import importlib.util
import inspect
import io
import json
from pathlib import Path
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "current_account_reader", HERE / "account_optional_differential.py")
READER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(READER)
SOURCE_KEYS = {"case", "answers", "calls", "readStates", "providerObservedReads",
               "failedSourceReads", "sourceFrameBefore", "sourceFrameAfter", "readAddCalls"}
BLOCK_FIELDS = {"account_reads", "account_writes", "storage_reads", "storage_writes",
                "code_reads", "code_writes", "oldest_ancestor_offset", "storage_clears"}
TX_FIELDS = {"account_writes", "storage_reads", "storage_writes", "code_reads",
             "code_writes", "created_accounts", "storage_clears", "transient_storage"}


def file_identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {"path": str(path), "size": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def inputs():
    # This also authenticates both independent catalogues before any source call.
    READER.expected_frames()
    return [row for row in READER.decode((HERE / "account_optional_inputs.json").read_bytes())
            if row["sourceComparable"]]


def source_expected():
    path = HERE / "account_optional_source_expected.json"
    if hashlib.sha256(path.read_bytes()).hexdigest() != "d4fea957051eff6c49fc74282f50440eb35fb280e79b2f973c77af6e9a1b216f":
        raise READER.AdmissionError("source expectations identity mismatch")
    rows = READER.decode(path.read_bytes())
    if type(rows) is not list or len(rows) != 233:
        raise READER.AdmissionError("wrong source expectation count")
    return rows


def parse_source(data):
    """Require complete independently frozen source answers, calls, reads and fields."""
    if type(data) is not bytes or len(data) > 2**23:
        raise READER.AdmissionError("invalid or oversized source stream")
    lines = data.splitlines()
    if len(lines) != 233:
        raise READER.AdmissionError("wrong source row count")
    rows = [READER.decode(line) for line in lines]
    READER.strict_equal(rows, source_expected(), "source")
    return rows


def authenticate(eels):
    """Run inside the supplied source interpreter; report actual imported bytes."""
    import ethereum.forks.amsterdam.state_tracker as tracker
    import ethereum.state as state
    import ethereum_types.numeric as numeric
    import ethereum_types.bytes as byte_types

    if not Path(sys.executable).samefile(eels / ".venv/bin/python"):
        raise ValueError("wrong source interpreter")
    for module, relative in [(tracker, "src/ethereum/forks/amsterdam/state_tracker.py"),
                             (state, "src/ethereum/state.py")]:
        if Path(inspect.getfile(module)).resolve() != (eels / relative).resolve():
            raise ValueError("source import is outside the supplied clone")
    types = importlib.metadata.distribution("ethereum-types")
    for module, relative in [(numeric, "ethereum_types/numeric.py"),
                             (byte_types, "ethereum_types/bytes.py")]:
        if Path(inspect.getfile(module)).resolve() != Path(types.locate_file(relative)).resolve():
            raise ValueError("numeric/bytes import differs from the authenticated distribution")
    pin = tomllib.loads((ROOT / "reference.toml").read_text())
    lock = tomllib.loads((eels / "uv.lock").read_text())
    packages = {package["name"]: package for package in lock["package"]}
    dependencies = []
    for name, version in pin["release"]["python_dependencies"].items():
        distribution = importlib.metadata.distribution(name)
        if distribution.version != version or packages[name]["version"] != version:
            raise ValueError("installed/locked/pinned version mismatch: " + name)
        files = []
        for path, expected, size in csv.reader(io.StringIO(distribution.read_text("RECORD"))):
            if not expected:
                continue
            scheme, encoded = expected.split("=", 1)
            if scheme != "sha256":
                raise ValueError("unsupported RECORD hash")
            identity = file_identity(distribution.locate_file(path))
            actual = base64.urlsafe_b64encode(bytes.fromhex(identity["sha256"])).rstrip(b"=")
            if actual.decode() != encoded or identity["size"] != int(size):
                raise ValueError("installed RECORD integrity failure: " + path)
            files.append(identity)
        dependencies.append({"name": name, "version": version, "verified_files": files,
                             "locked_wheel_hashes": [wheel["hash"] for wheel in
                                                     packages[name].get("wheels", [])]})
    return {"executable": file_identity(sys.executable), "version": sys.version,
            "optimize": sys.flags.optimize, "isolated": sys.flags.isolated,
            "dont_write_bytecode": sys.dont_write_bytecode,
            "operation_source": (inspect.getsource(tracker.get_account_optional) + inspect.getsource(tracker.get_pre_state_account_optional)),
            "imported_files": [file_identity(inspect.getfile(module)) for module in
                               [tracker, state, numeric, byte_types]],
            "uv_lock": file_identity(eels / "uv.lock"), "dependencies": dependencies,
            "limit": "Installed integrity and pinned versions; no downloaded-wheel provenance."}


def probe():
    """Run the original operation on its real carriers with instrumented providers."""
    from ethereum.forks.amsterdam.state_tracker import (
        BlockState, TransactionState, get_account_optional)
    from ethereum.state import Account
    from ethereum_types.numeric import Uint, U256
    from ethereum_types.bytes import Bytes20, Bytes32, Bytes

    class ProbeError(Exception):
        pass

    def account(value):
        return Account(Uint(value["nonce"]), U256(value["balance"]),
                       Bytes32(value["codeHash"].to_bytes(32, "big")))

    def account_values(value):
        return [int(value.nonce), int(value.balance), int.from_bytes(value.code_hash, "big")]

    def optional(value):
        return [0] if value is None else [1, *account_values(value)]

    def supplied_error(row):
        digest = row["providerAccount"]["codeHash"]
        return ([0, 0, digest], [0, 1, digest], [0, 2], [1, 0, digest],
                [1, 1, digest], [1, 2], [2, digest])[row["case"] % 7]

    def choice(row, kind, prefix):
        return None if kind == "tombstone" else account(
            row["emptyAccount"] if kind == "empty" else row[prefix + "Account"])

    def value(item):
        if item is None:
            return None
        if isinstance(item, (bytes, bytearray)):
            return {"bytes": bytes(item).hex()}
        if isinstance(item, Account):
            return {"account": account_values(item)}
        if isinstance(item, dict):
            return {"map": sorted([[value(key), value(val)] for key, val in item.items()],
                                  key=lambda pair: json.dumps(pair[0], sort_keys=True))}
        if isinstance(item, (set, frozenset)):
            return {"set": sorted([value(val) for val in item],
                                  key=lambda val: json.dumps(val, sort_keys=True))}
        if isinstance(item, tuple):
            return {"tuple": [value(val) for val in item]}
        return int(item)

    def snapshot(transaction):
        return {"block": {field.name: value(getattr(transaction.parent, field.name))
                          for field in dataclasses.fields(transaction.parent)
                          if field.name != "pre_state"},
                "tx": {field.name: value(getattr(transaction, field.name))
                       for field in dataclasses.fields(transaction)
                       if field.name not in ("parent", "account_reads")}}

    class ReadSet(set):
        def __init__(self, values):
            super().__init__(values)
            self.add_calls = 0

        def add(self, value):
            self.add_calls += 1
            super().add(value)

    for row in inputs():
        address = Bytes20(row["address"].to_bytes(20, "big"))
        other = Bytes20(row["otherAddress"].to_bytes(20, "big"))
        slot = Bytes32((17).to_bytes(32, "big"))
        second_slot = Bytes32((19).to_bytes(32, "big"))
        digest = Bytes32(row["providerAccount"]["codeHash"].to_bytes(32, "big"))
        calls, observed = [], []

        class Provider:
            def get_account_optional(self, queried):
                calls.append(int.from_bytes(queried, "big"))
                observed.append(queried in transaction.account_reads)
                kind = row["providerKind"]
                if kind == "error":
                    raise ProbeError(supplied_error(row))
                if kind == "absent" or (kind == "sequence" and len(calls) == 1):
                    return None
                return account(row["emptyAccount"] if kind == "empty" else row["providerAccount"])

            def get_storage(self, *_):
                raise RuntimeError("unexpected storage")

            def get_code(self, *_):
                raise RuntimeError("unexpected code")

            def compute_state_root(self, *_):
                raise RuntimeError("unexpected root")

        provider = Provider()
        block = BlockState(provider)
        transaction = TransactionState(block)
        for carrier, kind, prefix in [(block, row["blockKind"], "block"),
                                      (transaction, row["transactionKind"], "transaction")]:
            carrier.account_writes[other] = None
            if kind != "missing":
                carrier.account_writes[address] = choice(row, kind, prefix)
            carrier.storage_writes = {address: {}, other: {slot: U256(0),
                                                          second_slot: U256(2**256 - 1)}}
            carrier.storage_reads = {(other, slot)}
            carrier.code_reads = {digest}
            carrier.code_writes = {digest: Bytes(b"\x00\xff\x80\x00")}
            carrier.storage_clears = {other}
        block.account_reads = {other}
        block.oldest_ancestor_offset = Uint(2**420 + 3)
        transaction.account_reads = ReadSet({other} | ({address} if row["queriedReadBefore"] else set()))
        transaction.created_accounts = {other}
        transaction.transient_storage = {(other, slot): U256(0),
                                         (other, second_slot): U256(2**256 - 1)}
        before = snapshot(transaction)
        answers, reads, failed = [], [], None
        for _ in range(2 if row["twice"] else 1):
            try:
                result = get_account_optional(transaction, address)
            except ProbeError as error:
                answers.append([1, 0, *error.args[0]])
                reads.append(None)
                failed = sorted(int.from_bytes(val, "big") for val in transaction.account_reads)
                break
            answers.append([0, *optional(result)])
            reads.append(sorted(int.from_bytes(val, "big") for val in transaction.account_reads))
        after = snapshot(transaction)
        if before != after or transaction.parent is not block or block.pre_state is not provider:
            raise ValueError("source frame changed")
        print(json.dumps({"case": row["case"], "answers": answers, "calls": calls,
                          "readStates": reads, "providerObservedReads": observed,
                          "failedSourceReads": failed, "readAddCalls": transaction.account_reads.add_calls,
                          "sourceFrameBefore": before,
                          "sourceFrameAfter": after}, separators=(",", ":")))


def run_child(argv, report):
    started = time.time_ns()
    clock = time.monotonic()
    result = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    receipt = {"argv": [str(arg) for arg in argv], "cwd": str(Path.cwd()),
               "started_ns": started, "elapsed_seconds": time.monotonic() - clock,
               "returncode": result.returncode, "wait_consumed": True,
               "stdout": result.stdout.decode("utf-8", errors="backslashreplace"),
               "stderr": result.stderr.decode("utf-8", errors="backslashreplace"),
               "stdout_base64": base64.b64encode(result.stdout).decode("ascii"),
               "stderr_base64": base64.b64encode(result.stderr).decode("ascii"),
               "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
               "stderr_sha256": hashlib.sha256(result.stderr).hexdigest()}
    report["executions"].append(receipt)
    if result.returncode:
        raise ValueError("child failed: " + str(argv))
    return result.stdout


def source_identity(eels, report):
    def git(*args):
        return run_child(["git", "--no-replace-objects", "-C", str(eels), *args], report).decode()
    pin = tomllib.loads((ROOT / "reference.toml").read_text())
    head = git("rev-parse", "HEAD").strip()
    if head != pin["release"]["commit"] or git("status", "--porcelain"):
        raise ValueError("source must be a clean checkout of the exact pin")
    files = ["src/ethereum/forks/amsterdam/state_tracker.py", "src/ethereum/state.py", "uv.lock"]
    for relative in files:
        committed = run_child(["git", "--no-replace-objects", "-C", str(eels),
                               "show", "HEAD:" + relative], report)
        if committed != (eels / relative).read_bytes():
            raise ValueError("source bytes differ from pinned Git object")
    return {"head": head, "files": [file_identity(eels / relative) for relative in files]}


def check_authentication(before, after):
    """Keep runtime-mode checks strict and require unchanged authenticated inputs."""
    fields = {"executable", "version", "optimize", "isolated", "dont_write_bytecode",
              "operation_source", "imported_files", "uv_lock", "dependencies", "limit"}
    for auth, mode in [(before, 0), (after, 1)]:
        if type(auth) is not dict or auth.keys() != fields:
            raise ValueError("wrong source authentication fields")
        READER.strict_equal([auth["optimize"], auth["isolated"], auth["dont_write_bytecode"]],
                            [mode, 1, True], "runtime flags")
    READER.strict_equal({key: val for key, val in before.items() if key != "optimize"},
                        {key: val for key, val in after.items() if key != "optimize"})


def compare(eels, target, report):
    READER.parse_target(target.read_bytes())
    paths = [Path(__file__), HERE / "account_optional_differential.py",
             HERE / "account_optional_inputs.json", HERE / "account_optional_expected.json",
             HERE / "account_optional_source_expected.json",
             ROOT / "reference.toml", target, eels / ".venv/bin/python"]
    report["inputs_before"] = [file_identity(path) for path in paths]
    report["source_before"] = source_identity(eels, report)
    executable = eels / ".venv/bin/python"
    script = Path(__file__).resolve()
    auth_before = READER.decode(run_child([executable, "-I", "-B", script,
                                          "--worker", "authenticate", "--eels", eels], report))
    normal = run_child([executable, "-I", "-B", script, "--worker", "probe"], report)
    optimized = run_child([executable, "-I", "-B", "-O", script, "--worker", "probe"], report)
    parse_source(normal)
    parse_source(optimized)
    if normal != optimized:
        raise ValueError("source observations differ between Python modes")
    auth_after = READER.decode(run_child([executable, "-I", "-B", "-O", script,
                                         "--worker", "authenticate", "--eels", eels], report))
    check_authentication(auth_before, auth_after)
    report["source_after"] = source_identity(eels, report)
    report["inputs_after"] = [file_identity(path) for path in paths]
    READER.strict_equal(report["source_before"], report["source_after"])
    READER.strict_equal(report["inputs_before"], report["inputs_after"])
    report.update(status="PASS", cases=233, source_modes_byte_equal=True,
                  projection="answers, calls, successful read states; separate source failed reads",
                  source_frame_equal=True,
                  limits="No backend adapter, full-state refinement, EEST/guest or cost claim.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--check-target", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--worker", choices=["authenticate", "probe"], help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker == "probe":
        probe()
        return
    if args.worker == "authenticate":
        if args.eels is None:
            parser.error("authentication worker needs --eels")
        print(json.dumps(authenticate(args.eels.resolve()), separators=(",", ":")))
        return
    if args.eels is None or args.check_target is None or args.report is None:
        parser.error("--eels, --check-target and --report are required")
    eels, target, destination = args.eels.resolve(), args.check_target.resolve(), args.report.resolve()
    # Keep the source clone and supplied inputs strictly read-only.
    if (destination == target or destination.is_relative_to(eels) or
            destination in [ROOT / "reference.toml", Path(__file__).resolve()] or
            destination.is_relative_to(HERE)):
        parser.error("report must be outside EELS, the conformance sources and supplied target")
    report = {"status": "FAILED", "executions": []}
    try:
        compare(eels, target, report)
    except Exception as error:
        report["error"] = type(error).__name__ + ": " + str(error)
        raise
    finally:
        destination.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS current-optional-account source: 233 complete normal/-O comparisons and authenticated runtime")


if __name__ == "__main__":
    main()
