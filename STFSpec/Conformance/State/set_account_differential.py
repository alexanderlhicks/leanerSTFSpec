#!/usr/bin/env python3
"""Check complete standalone setAccount histories.

Build set-account-native-tests, then run the native and interpreted controls
with STFSpec/Conformance/State/set_account_inputs.json. Pass each output via
--check-target. Supply --eels EELS --report REPORT.json for the authenticated
comparison with EELS/.venv/bin/python -I -B in normal and -O modes. The source
comparison omits the two histories with no Python representation of their raw
index, and checks the common finite projection in the other histories.
"""

import argparse
import hashlib
import importlib.util
import inspect
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE / "set_account_inputs.json"
INPUT_SHA256 = "ba026b0b6fdf801c470f64228fc60681c97ad77a17b3bf7a953631161a04c22d"
SOURCE_PATH = HERE / "account_optional_source.py"
SPEC = importlib.util.spec_from_file_location("account_source_authentication", SOURCE_PATH)
SOURCE = importlib.util.module_from_spec(SPEC)
exec(compile(SOURCE_PATH.read_bytes(), str(SOURCE_PATH), "exec"), SOURCE.__dict__)
decode = SOURCE.READER.decode
strict_equal = SOURCE.READER.strict_equal

WIDE = 2**152 + 5
SLOT = 2**248 + 7
DIGEST = 2**250 + 11
OFFSET = 2**80 + 3
BALANCE = 2**256 - 1
SOURCE_HISTORIES = {"first-writes", "overwrites", "live-storage-tombstone", "sparse-positions"}


def histories():
    data = INPUT.read_bytes()
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise ValueError("setAccount input catalogue identity mismatch")
    return decode(data)


def raw_index(key):
    return {"next": 2**180 + 17, "positions": [[key, 31]], "keysByPosition": [[31, key]]}


def pairs(dictionary):
    return [[key, value] for key, value in sorted(dictionary.items())]


def shared_frame():
    return {"storageWrites": [[5, [[7, 0], [SLOT, BALANCE]]], [WIDE, []]],
            "codeWrites": [[DIGEST, [0, 255, 128]]], "storageClears": [9],
            "accountReads": [WIDE], "storageReads": [[5, SLOT]], "codeReads": [DIGEST]}


def expected_rows():
    """Describe the finite map, ordered position table and whole framed values."""
    for row in histories():
        values = {w["address"]: w["account"] for w in row["initial"]}
        raw = row["index"]
        if raw is None:
            forward = {key: at for at, key in enumerate(values)}
            reverse = dict(enumerate(values))
            next_position = len(values)
        else:
            forward = dict(raw["positions"])
            reverse = dict(raw["keysByPosition"])
            next_position = raw["next"]
        snapshots = []
        for step in [None, *row["writes"]]:
            if step is not None:
                address = step["address"]
                values[address] = step["account"]
                if address not in forward:
                    forward[address] = next_position
                    reverse[next_position] = address
                    next_position += 1
            common = {"block": {**shared_frame(), "accountOrder": [9],
                                "accountWrites": [[9, {"nonce": 33, "balance": 1, "codeHash": DIGEST}]],
                                "oldestAncestorOffset": OFFSET},
                      "tx": {**shared_frame(), "accountWrites": pairs(values),
                             "accountOrder": [key for _, key in sorted(reverse.items())],
                             "transient": [[WIDE, 7, 23]], "createdAccounts": [9]}}
            snapshots.append({"common": common, "calls": [99],
                              "accountIndex": {"next": next_position, "positions": pairs(forward),
                                               "keysByPosition": pairs(reverse)},
                              "blockAccountIndex": raw_index(9), "blockStorageIndex": raw_index(WIDE),
                              "blockSlotIndexes": [[5, raw_index(SLOT)]],
                              "txStorageIndex": raw_index(WIDE), "txSlotIndexes": [[5, raw_index(SLOT)]],
                              "consts": [21, 22, 23, 24]})
        yield {"name": row["name"], "snapshots": snapshots}


def source_probe():
    from ethereum.forks.amsterdam import state_tracker as tracker
    from ethereum.state import Account
    from ethereum_types.bytes import Bytes, Bytes20, Bytes32
    from ethereum_types.numeric import U256, Uint

    def address(n):
        return Bytes20(n.to_bytes(20, "big"))

    def slot(n):
        return Bytes32(n.to_bytes(32, "big"))

    def integer(value):
        return int.from_bytes(value, "big")

    def account(value):
        return None if value is None else Account(
            Uint(value["nonce"]), U256(value["balance"]), slot(value["codeHash"]))

    def view_account(value):
        return None if value is None else {
            "nonce": int(value.nonce), "balance": int(value.balance),
            "codeHash": integer(value.code_hash)}

    class Provider:
        def __getattr__(self, name):
            calls.append(name)
            raise RuntimeError("unexpected provider access: " + name)

    def frame(value):
        return {"accountWrites": pairs({integer(a): view_account(v)
                                       for a, v in value.account_writes.items()}),
                "accountOrder": [integer(a) for a in value.account_writes],
                "storageWrites": pairs({integer(a): pairs({integer(k): int(v) for k, v in w.items()})
                                       for a, w in value.storage_writes.items()}),
                "codeWrites": pairs({integer(k): list(v) for k, v in value.code_writes.items()}),
                "storageClears": sorted(map(integer, value.storage_clears)),
                "accountReads": sorted(map(integer, value.account_reads)),
                "storageReads": sorted([integer(a), integer(k)] for a, k in value.storage_reads),
                "codeReads": sorted(map(integer, value.code_reads))}

    def snapshot(tx):
        return {"block": {**frame(tx.parent),
                          "oldestAncestorOffset": int(tx.parent.oldest_ancestor_offset)},
                "tx": {**frame(tx), "createdAccounts": sorted(map(integer, tx.created_accounts)),
                       "transient": sorted([integer(a), integer(k), int(v)]
                                           for (a, k), v in tx.transient_storage.items())}}

    def source_fields():
        return {"storage_writes": {address(5): {slot(7): U256(0), slot(SLOT): U256(BALANCE)},
                                   address(WIDE): {}},
                "code_writes": {slot(DIGEST): Bytes(b"\x00\xff\x80")},
                "storage_clears": {address(9)}, "account_reads": {address(WIDE)},
                "storage_reads": {(address(5), slot(SLOT))}, "code_reads": {slot(DIGEST)}}

    for row in histories():
        if row["name"] not in SOURCE_HISTORIES:
            continue
        calls = []
        provider = Provider()
        block = tracker.BlockState(provider, **source_fields(), oldest_ancestor_offset=Uint(OFFSET),
                                   account_writes={address(9): Account(Uint(33), U256(1), slot(DIGEST))})
        initial = {address(w["address"]): account(w["account"]) for w in row["initial"]}
        tx = tracker.TransactionState(block, **source_fields(), account_writes=initial,
                                      created_accounts={address(9)},
                                      transient_storage={(address(WIDE), slot(7)): U256(23)})
        snapshots = [snapshot(tx)]
        for w in row["writes"]:
            result = tracker.set_account(tx, address(w["address"]), account(w["account"]))
            if result is not None or tx.parent is not block or block.pre_state is not provider or calls:
                raise ValueError("source return, provider or parent frame changed")
            snapshots.append(snapshot(tx))
        yield {"name": row["name"], "snapshots": snapshots, "calls": calls}


def worker(eels):
    policy = SOURCE.install_source_only_imports()
    observations = list(source_probe())
    from ethereum.forks.amsterdam import state_tracker as tracker

    auth = SOURCE.authenticate(eels, policy)
    auth["operation_source"] = inspect.getsource(tracker.set_account)
    for imported in auth["imported_files"]:
        compiled = [value for value in policy.compiled_sources.values()
                    if value["path"] == imported["path"]]
        strict_equal(compiled, [imported], "compiled source identity")
    return {"authentication": auth, "observations": observations}


def compare_source(eels, target, rows, report):
    paths = [Path(__file__), INPUT, SOURCE_PATH, SOURCE.HERE / "pre_state_account_source.py",
             SOURCE.HERE / "pre_state_account_differential.py",
             SOURCE.HERE / "account_optional_differential.py",
             SOURCE.ROOT / "reference.toml", eels / ".venv/bin/python", target]
    report["inputs_before"] = [SOURCE.file_identity(path) for path in paths]
    report["source_before"] = SOURCE.source_identity(eels, report)
    projection = [{"name": row["name"], "calls": [],
                   "snapshots": [snapshot["common"] for snapshot in row["snapshots"]]}
                  for row in rows if row["name"] in SOURCE_HISTORIES]
    runs = []
    for flags in ([], ["-O"]):
        result = decode(SOURCE.run_child([eels / ".venv/bin/python", "-I", "-B", *flags,
                                          Path(__file__).resolve(), "--worker", "--eels", eels], report))
        if result.keys() != {"authentication", "observations"}:
            raise ValueError("wrong source worker result fields")
        strict_equal(result["observations"], projection, "EELS versus Lean")
        runs.append(result)
    SOURCE.check_authentication(*(result["authentication"] for result in runs))
    report["source_after"] = SOURCE.source_identity(eels, report)
    report["inputs_after"] = [SOURCE.file_identity(path) for path in paths]
    strict_equal(report["source_before"], report["source_after"], "source checkout identity")
    strict_equal(report["inputs_before"], report["inputs_after"], "source and target inputs")
    report["source_histories"] = len(projection)
    report["source_writes"] = sum(len(row["snapshots"]) - 1 for row in projection)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path)
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        print(json.dumps(worker(args.eels.resolve()), separators=(",", ":")))
        return
    if args.check_target is None or (args.eels is None) != (args.report is None):
        parser.error("supply --check-target and optionally both --eels and --report")

    target = args.check_target.resolve()
    data = target.read_bytes()
    if len(data) > 2**20 or not data.endswith(b"\n"):
        raise ValueError("oversized or unterminated setAccount stream")
    rows = [decode(line) for line in data.splitlines()]
    strict_equal(rows, list(expected_rows()), "Lean output")
    target_identity = SOURCE.file_identity(target)
    if target_identity["sha256"] != hashlib.sha256(data).hexdigest():
        raise ValueError("Lean output changed during admission")
    if args.eels is not None:
        eels = args.eels.resolve()
        destination = args.report.resolve()
        if (destination in {target, SOURCE.ROOT / "reference.toml"} or
                destination.is_relative_to(eels) or destination.is_relative_to(HERE)):
            parser.error("report must be outside EELS, conformance sources and the supplied target")
        report = {"status": "FAILED", "executions": []}
        try:
            compare_source(eels, target, rows, report)
            strict_equal(SOURCE.file_identity(target), target_identity, "admitted target identity")
            report["status"] = "PASS"
        except Exception as error:
            report["error"] = f"{type(error).__name__}: {error}"
            raise
        finally:
            destination.write_text(json.dumps(report, indent=2) + "\n")
        print(f"matched {report['source_writes']} EELS writes in both modes")
    print(f"checked {len(rows)} histories and {sum(len(row['snapshots']) - 1 for row in rows)} writes")


if __name__ == "__main__":
    main()
