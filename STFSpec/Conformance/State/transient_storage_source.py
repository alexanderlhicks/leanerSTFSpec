#!/usr/bin/env python3
"""Compare the transient storage read with a frozen pinned EELS environment.

Run from the repository root after capturing native and interpreted target streams.
Pass --eels EELS, one --check-target per stream, and --report REPORT.json.
The driver runs EELS/.venv/bin/python -I -B directly in both optimization modes.
The report retains the workers' complete stdout, stderr and authentication.
"""

import argparse
import dataclasses
import importlib.util
import inspect
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_module(name):
    path = HERE / (name + ".py")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


DRIVER = load_module("pre_state_account_source")
MODEL = load_module("transient_storage_differential")
TRACKER = "ethereum.forks.amsterdam.state_tracker"


def probe(tracker, account_type, address_type, slot_type, uint, word):
    def address(n):
        return address_type(n.to_bytes(20, "big"))

    def slot(n):
        return slot_type(n.to_bytes(32, "big"))

    def number(key):
        return int.from_bytes(key, "big")

    def seed(layer, a, k, salt):
        layer.account_writes[a] = account_type(
            uint(2**180 + salt), word(2**200 + salt), slot(2**255 + salt))
        layer.account_writes[address(salt + 1)] = None
        layer.storage_writes[a] = {k: word(2**170 + salt)}
        layer.storage_writes[address(salt + 3)] = {}
        layer.code_writes[slot(2**153 + salt)] = bytes([0, salt, 255])
        layer.storage_clears.add(address(salt + 1))
        layer.account_reads.add(address(salt + 2))
        layer.storage_reads.add((address(salt + 2), slot(2**155 + salt)))
        layer.code_reads.add(slot(2**154 + salt))

    def observe_account(account):
        if account is None:
            return None
        return [int(account.nonce), int(account.balance), number(account.code_hash)]

    def observe_layer(layer):
        return {
            "accountWrites": sorted([number(a), observe_account(v)]
                                    for a, v in layer.account_writes.items()),
            "storageWrites": sorted([number(a), sorted([number(k), int(v)]
                                                       for k, v in slots.items())]
                                    for a, slots in layer.storage_writes.items()),
            "codeWrites": sorted([number(k), list(v)] for k, v in layer.code_writes.items()),
            "storageClears": sorted(map(number, layer.storage_clears)),
            "accountReads": sorted(map(number, layer.account_reads)),
            "storageReads": sorted([number(a), number(k)] for a, k in layer.storage_reads),
            "codeReads": sorted(map(number, layer.code_reads)),
        }

    calls = []

    class Provider:
        def __getattr__(self, name):
            calls.append(name)
            raise ValueError("unexpected pre-state access " + name)

    block_fields = {"pre_state"} | DRIVER.BLOCK_FIELDS
    tx_fields = {"parent", "account_reads"} | DRIVER.TX_FIELDS
    for record, fields in [(tracker.BlockState, block_fields), (tracker.TransactionState, tx_fields)]:
        if {field.name for field in dataclasses.fields(record)} != fields:
            raise ValueError("source tracker fields differ from the frame")

    for case in MODEL.inputs():
        a, k = address(case["address"]), slot(case["slot"])
        provider = Provider()
        block = tracker.BlockState(provider)
        tx = tracker.TransactionState(block)
        seed(block, a, k, 40)
        seed(tx, a, k, 80)
        block.oldest_ancestor_offset = uint(2**140 + 13)
        tx.created_accounts.add(address(97))
        tx.transient_storage = {(address(x), slot(y)): word(value)
                                for x, y, value in case["transient"]}

        def frame():
            if tx.parent is not block or block.pre_state is not provider:
                raise ValueError("source context identity changed")
            return {
                "block": observe_layer(block) | {
                    "oldestAncestorOffset": int(block.oldest_ancestor_offset)},
                "tx": observe_layer(tx) | {"createdAccounts": sorted(map(number, tx.created_accounts)),
                    "transient": sorted([number(x), number(y), int(value)]
                                        for (x, y), value in tx.transient_storage.items())},
            }

        calls.clear()
        answers, frames = [], [frame()]
        for _ in range(case["repeat"]):
            value = tracker.get_transient_storage(tx, a, k)
            if type(value) is not word:
                raise ValueError("source transient storage did not return U256")
            answers.append(int(value))
            frames.append(frame())
        yield {"id": case["id"], "answers": answers, "calls": calls.copy(), "frames": frames}


def worker(eels):
    policy = DRIVER.install_source_only_imports()
    from ethereum.forks.amsterdam import state_tracker as tracker
    from ethereum.state import Account, Address
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import Uint, U256

    observations = "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in
                           probe(tracker, Account, Address, Bytes32, Uint, U256))
    auth = DRIVER.authenticate(eels, policy)
    auth["operation_source"] = inspect.getsource(tracker.get_transient_storage)
    print(json.dumps({"authentication": auth, "observations": observations}))


def source_projection(target_rows):
    return [row | {"frames": [{key: frame[key] for key in ("block", "tx")}
                             for frame in row["frames"]]} for row in target_rows]


def compare(eels, targets, report):
    paths = [Path(__file__), MODEL.INPUTS, HERE / "transient_storage_differential.py",
             HERE / "account_optional_differential.py", HERE / "pre_state_account_source.py",
             HERE / "pre_state_account_differential.py", DRIVER.ROOT / "reference.toml",
             eels / ".venv/bin/python", *targets]
    report["inputs_before"] = [DRIVER.file_identity(path) for path in paths]
    projections = [source_projection(MODEL.parse_rows(target.read_bytes())) for target in targets]
    report["source_before"] = DRIVER.source_identity(eels, report)
    envelopes = []
    for flags in ([], ["-O"]):
        argv = [eels / ".venv/bin/python", "-I", "-B", *flags, Path(__file__).resolve(),
                "--worker", "--eels", eels]
        envelope = MODEL.READER.decode(DRIVER.run_child(argv, report))
        if type(envelope) is not dict or envelope.keys() != {"authentication", "observations"}:
            raise ValueError("invalid source worker envelope")
        envelopes.append(envelope)
    auth = [envelope["authentication"] for envelope in envelopes]
    DRIVER.check_authentication(*auth)
    for identity in auth:
        MODEL.READER.strict_equal(identity["source_loading"]["compiled_sources"][TRACKER],
                                 report["source_before"]["files"][0], "compiled tracker")
    normal, optimized = (envelope["observations"].encode("utf-8") for envelope in envelopes)
    if normal != optimized:
        raise ValueError("source observations differ between Python modes")
    rows = MODEL.parse_rows(normal, source=True)
    for projection in projections:
        MODEL.READER.strict_equal(rows, projection, "source and target projection")
    report["source_after"] = DRIVER.source_identity(eels, report)
    report["inputs_after"] = [DRIVER.file_identity(path) for path in paths]
    MODEL.READER.strict_equal(report["source_before"], report["source_after"])
    MODEL.READER.strict_equal(report["inputs_before"], report["inputs_after"])
    report.update(status="PASS", cases=len(rows), reads=sum(len(row["answers"]) for row in rows),
                  source_modes_byte_equal=True, compared_targets=len(targets))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eels", type=Path, required=True)
    parser.add_argument("--check-target", action="append", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    eels = args.eels.resolve()
    if args.worker:
        worker(eels)
        return
    if not args.check_target or args.report is None:
        parser.error("--check-target and --report are required")
    targets = [target.resolve() for target in args.check_target]
    destination = args.report.resolve()
    if destination.is_relative_to(eels):
        parser.error("report must be outside EELS")
    report = {"status": "FAILED", "executions": []}
    with destination.open("x") as out:
        try:
            compare(eels, targets, report)
        except Exception as error:
            report["error"] = type(error).__name__ + ": " + str(error)
            raise
        finally:
            json.dump(report, out, indent=2)
            out.write("\n")
    print(f"PASS transient storage source: {report['cases']} cases and {report['reads']} reads per mode")


if __name__ == "__main__":
    main()
