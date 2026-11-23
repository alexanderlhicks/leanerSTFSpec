#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Check complete standalone TLOAD observations.

Check native and interpreted streams with --check-target. To also compare pinned
EELS, pass --eels EELS, both --check-target paths, and --report REPORT.json.
The source driver calls EELS/.venv/bin/python -I -B directly, normally and with -O.
"""

import argparse
import copy
import dataclasses
import hashlib
import importlib.util
import inspect
import json
import os
from pathlib import Path
import sys
import tomllib
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
INPUTS = HERE / "tload_inputs.json"
STATE = HERE.parents[1] / "State"
AUTH = STATE / "pre_state_account_source.py"
spec = importlib.util.spec_from_file_location("tload_source_policy", AUTH)
driver = importlib.util.module_from_spec(spec)
exec(compile(AUTH.read_bytes(), str(AUTH), "exec"), driver.__dict__)
reader = driver.READER


def require(condition, message):
    if not condition:
        raise ValueError(message)


def inputs():
    rows = reader.decode(INPUTS.read_bytes())
    require(type(rows) is list and rows and len(rows) <= 32, "invalid input catalogue")
    ids = set()
    fields = {"id", "stackBottomFirst", "prefixCount", "gas", "target", "transient",
              "cost", "pc", "static", "eels"}

    def nat(value, limit):
        return type(value) is int and 0 <= value < limit

    for row in rows:
        require(type(row) is dict and row.keys() == fields, "invalid input fields")
        label = row["id"]
        require(type(label) is str and 0 < len(label) <= 64 and label not in ids, "invalid case ID")
        ids.add(label)
        require(all(nat(row[key], 2**512) for key in ("gas", "cost", "pc")), "invalid gas or pc")
        require(type(row["static"]) is bool and type(row["eels"]) is bool, "invalid input flags")
        require(row["eels"] == (row["cost"] == 100), "invalid source price selection")
        require(nat(row["target"], 2**160), "invalid target")
        words = row["stackBottomFirst"]
        require(type(words) is list and nat(row["prefixCount"], 1025)
                and len(words) + row["prefixCount"] <= 1024
                and all(nat(word, 2**256) for word in words), "invalid stack")
        entries = row["transient"]
        require(type(entries) is list and len(entries) <= 32, "invalid transient table")
        keys = set()
        for entry in entries:
            require(type(entry) is list and len(entry) == 3, "invalid transient entry")
            address, slot, word = entry
            require(nat(address, 2**160) and nat(slot, 2**256) and nat(word, 2**256),
                    "invalid transient entry fields")
            require((address, slot) not in keys, "duplicate transient key")
            keys.add((address, slot))
    return rows


def stack(case):
    return list(range(case["prefixCount"])) + case["stackBottomFirst"]


def seed_projection(case, salt):
    target, words = case["target"], stack(case)
    key = words[-1] if words else 0
    return {
        "accountWrites": [[target, [salt + 1, salt + 2, salt + 3]]],
        "storageWrites": [[target, [[key, salt + 4]]]],
        "codeWrites": [[salt + 5, [0, salt, 255]]],
        "storageClears": [salt + 6],
        "accountReads": [salt + 7],
        "storageReads": [[salt + 8, salt + 9]],
        "codeReads": [salt + 10],
    }


def expected(case):
    words = stack(case)
    target, key = case["target"], words[-1] if words else 0
    frame = {
        "pc": case["pc"], "stack": list(reversed(words)),
        "memory": [0, 0, 0, 128, 255, 1] + [0] * 26,
        "meter": [case["gas"], 11, 13, -17, 19, 23],
        "logs": [[256, [256, 1, 256], [255, 0, 128]]] * 2,
        "deleted": [256], "returnData": [0, 255, 128, 0],
        "warmAddresses": [1], "warmSlots": [[1, 256], [256, 1]],
    }

    def index(value, salt):
        return [salt + 11, [[value, salt + 3]], [[salt + 5, value]]]

    def order(salt):
        return [index(target, salt), index(target, salt + 1), [[target, index(key, salt + 2)]]]

    world = {
        "block": seed_projection(case, 40) | {"oldestAncestorOffset": 2**140 + 13},
        "tx": seed_projection(case, 80) | {
            "createdAccounts": [97], "transient": sorted(case["transient"])},
        "consts": [101, 103, 107, 109], "blockOrder": order(40), "txOrder": order(80),
        "provider": [[13, 17, 19], 107, [0, 128, 255], 113], "sampleCalls": [1, 2, 3, 4],
    }
    after = copy.deepcopy(frame)
    tag, events = "underflow", []
    if words:
        after["stack"] = after["stack"][1:]
        events.append(["charge", case["cost"]])
        tag = "outOfGas"
        if case["gas"] >= case["cost"]:
            table = {(a, k): v for a, k, v in case["transient"]}
            after["stack"].insert(0, table.get((target, key), 0))
            after["meter"][0] -= case["cost"]
            after["pc"] += 1
            events.append(["read", target, key])
            tag = "continue"
    return {
        "id": case["id"], "tag": tag, "calls": [], "before": frame, "after": after,
        "worldBefore": world, "worldAfter": world,
    }, events


def parse_target(data, cases):
    require(type(data) is bytes and len(data) <= 2**20, "invalid or oversized output")
    lines = data.splitlines()
    require(len(lines) == len(cases), "wrong output row count")
    rows = [reader.decode(line) for line in lines]
    for case, row in zip(cases, rows, strict=True):
        reader.strict_equal(row, expected(case)[0], case["id"])
    return rows


def source_projection(row):
    return row | {
        key: {field: row[key][field] for field in ("block", "tx")}
        for key in ("worldBefore", "worldAfter")
    }


def probe(cases):
    from ethereum.forks.amsterdam import state_tracker as tracker
    from ethereum.forks.amsterdam.block_access_lists import BlockAccessListBuilder
    from ethereum.forks.amsterdam.blocks import Log
    from ethereum.forks.amsterdam.vm import BlockEnvironment, Evm, TransactionEnvironment, gas, stack as ops
    from ethereum.forks.amsterdam.vm.exceptions import OutOfGasError, StackUnderflowError
    from ethereum.forks.amsterdam.vm.instructions import storage
    from ethereum.state import Account
    from ethereum.trace import GasAndRefund, set_evm_trace
    from ethereum_types.bytes import Bytes20, Bytes32
    from ethereum_types.numeric import U64, U256, Uint

    def address(n):
        return Bytes20(n.to_bytes(20, "big"))

    def slot(n):
        return Bytes32(n.to_bytes(32, "big"))

    def number(value):
        return int.from_bytes(value, "big")

    def seed(layer, case, salt):
        target, values = address(case["target"]), stack(case)
        key = slot(values[-1] if values else 0)
        layer.account_writes[target] = Account(Uint(salt + 1), U256(salt + 2), slot(salt + 3))
        layer.storage_writes[target] = {key: U256(salt + 4)}
        layer.code_writes[slot(salt + 5)] = bytes([0, salt, 255])
        layer.storage_clears.add(address(salt + 6))
        layer.account_reads.add(address(salt + 7))
        layer.storage_reads.add((address(salt + 8), slot(salt + 9)))
        layer.code_reads.add(slot(salt + 10))

    def account(value):
        return None if value is None else [int(value.nonce), int(value.balance), number(value.code_hash)]

    def layer_json(layer):
        return {
            "accountWrites": sorted([number(a), account(v)] for a, v in layer.account_writes.items()),
            "storageWrites": sorted([number(a), sorted([number(k), int(v)] for k, v in slots.items())]
                                    for a, slots in layer.storage_writes.items()),
            "codeWrites": sorted([number(k), list(v)] for k, v in layer.code_writes.items()),
            "storageClears": sorted(map(number, layer.storage_clears)),
            "accountReads": sorted(map(number, layer.account_reads)),
            "storageReads": sorted([number(a), number(k)] for a, k in layer.storage_reads),
            "codeReads": sorted(map(number, layer.code_reads)),
        }

    def frame_json(frame):
        meter = frame.gas_meter
        return {
            "pc": int(frame.pc), "stack": list(map(int, reversed(frame.stack))), "memory": list(frame.memory),
            "meter": [int(meter.gas_left), int(meter.state_gas_left), int(meter.state_gas_baseline),
                      int(meter.refund_counter), int(meter.state_gas_spilled),
                      int(meter.state_gas_committed_spill)],
            "logs": [[number(log.address), list(map(number, log.topics)), list(log.data)] for log in frame.logs],
            "deleted": sorted(map(number, frame.accounts_to_delete)),
            "returnData": list(frame.return_data),
            "warmAddresses": sorted(map(number, frame.accessed_addresses)),
            "warmSlots": sorted([number(a), number(k)] for a, k in frame.accessed_storage_keys),
        }

    def snapshot(value):
        if dataclasses.is_dataclass(value):
            return untouched(value, set())
        if isinstance(value, dict):
            return {key: snapshot(item) for key, item in value.items()}
        if isinstance(value, (tuple, list)):
            return tuple(map(snapshot, value))
        if isinstance(value, set):
            return frozenset(value)
        if isinstance(value, bytearray):
            return bytes(value)
        return value

    def untouched(record, excluded):
        return {field.name: snapshot(getattr(record, field.name))
                for field in dataclasses.fields(record) if field.name not in excluded}

    calls = []

    class Provider:
        def __getattr__(self, name):
            calls.append(name)
            raise ValueError("unexpected pre-state action: " + name)

    require(storage.pop is ops.pop and storage.push is ops.push
            and storage.charge_gas is gas.charge_gas
            and storage.get_transient_storage is tracker.get_transient_storage,
            "unexpected source helper bindings")
    for case in cases:
        if not case["eels"]:
            continue
        calls.clear()
        provider = Provider()
        block = tracker.BlockState(provider)
        tx = tracker.TransactionState(block)
        seed(block, case, 40)
        seed(tx, case, 80)
        block.oldest_ancestor_offset = Uint(2**140 + 13)
        tx.created_accounts.add(address(97))
        tx.transient_storage = {(address(a), slot(k)): U256(v) for a, k, v in case["transient"]}

        def world_json():
            return {
                "block": layer_json(block) | {"oldestAncestorOffset": int(block.oldest_ancestor_offset)},
                "tx": layer_json(tx) | {"createdAccounts": sorted(map(number, tx.created_accounts)),
                    "transient": sorted([number(a), number(k), int(v)] for (a, k), v in tx.transient_storage.items())},
            }

        be = BlockEnvironment(U64(11), block, Uint(13), [slot(17), slot(19)], address(23),
                              Uint(29), Uint(31), U256(37), slot(41), U64(43), slot(47),
                              BlockAccessListBuilder(), U64(53))
        te = TransactionEnvironment(address(59), address(61), True, bytes([0, 128, 0]), U256(67),
                                    Uint(71), Uint(73), gas.ExecutionGas(Uint(79)), gas.StateGas(Uint(83)),
                                    Uint(89), set(), set(), set(), tx, (), (), Uint(0), slot(97))
        meter = gas.GasMeter(gas.ExecutionGas(Uint(case["gas"])), gas.StateGas(Uint(11)),
                             gas.StateGas(Uint(13)), -17, gas.StateGas(Uint(19)), gas.StateGas(Uint(23)))
        log = Log(address(256), (slot(256), slot(1), slot(256)), bytes([255, 0, 128]))
        frame = Evm(
            pc=Uint(case["pc"]), stack=list(map(U256, stack(case))),
            memory=bytearray(bytes([0, 0, 0, 128, 255, 1]) + bytes(26)),
            code=b"\x5c", gas_meter=meter, valid_jump_destinations={Uint(0), Uint(2)},
            logs=(log, log), running=True, block_env=be, tx_env=te, caller=address(101),
            current_target=address(case["target"]), value=U256(2**256 - 1), call_data=bytes([255, 0, 128]),
            code_address=address(103), depth=Uint(7), should_transfer_value=True, is_static=case["static"],
            disable_precompiles=False, parent_evm=None, output=b"\xff", accounts_to_delete={address(256)},
            return_data=bytes([0, 255, 128, 0]), error=None, accessed_addresses={address(1)},
            accessed_storage_keys={(address(1), slot(256)), (address(256), slot(1))},
        )
        world_before, frame_before = world_json(), frame_json(frame)
        context_before = (untouched(frame, {"pc", "stack", "gas_meter", "block_env", "tx_env"}),
                          untouched(be, {"state"}), untouched(te, {"state"}),
                          untouched(block, {"pre_state"}), untouched(tx, {"parent"}))
        events = []

        def record_read(state, owner, key):
            require(state is tx and type(owner) is Bytes20 and type(key) is Bytes32, "wrong transient read inputs")
            events.append(["read", number(owner), number(key)])
            return tracker.get_transient_storage(state, owner, key)

        def trace(subject, event):
            require(subject is frame and type(event) is GasAndRefund, "unexpected gas trace")
            events.append(["charge", event.gas_cost])

        tag = "continue"
        previous = set_evm_trace(trace)
        try:
            with patch.object(storage, "get_transient_storage", side_effect=record_read):
                storage.tload(frame)
        except StackUnderflowError:
            tag = "underflow"
        except OutOfGasError:
            tag = "outOfGas"
        finally:
            set_evm_trace(previous)

        require(frame.gas_meter is meter and frame.block_env is be and frame.tx_env is te
                and te.state is tx and be.state is block and tx.parent is block and block.pre_state is provider,
                case["id"] + ": source context identity changed")
        require(context_before == (
                    untouched(frame, {"pc", "stack", "gas_meter", "block_env", "tx_env"}),
                    untouched(be, {"state"}), untouched(te, {"state"}),
                    untouched(block, {"pre_state"}), untouched(tx, {"parent"})),
                case["id"] + ": preserved source fields changed")
        require(all(type(value) is U256 for value in frame.stack), "source stack contains a non-word")
        yield {
            "id": case["id"], "tag": tag, "calls": calls.copy(),
            "before": frame_before, "after": frame_json(frame),
            "worldBefore": world_before, "worldAfter": world_json(),
            "events": events,
        }


def worker(eels):
    policy = driver.install_source_only_imports()
    from ethereum.forks.amsterdam.vm.instructions import storage

    observations = list(probe(inputs()))
    auth = driver.authenticate(eels, policy)
    auth["operation_source"] = inspect.getsource(storage.tload)
    print(json.dumps({"observations": observations, "authentication": auth}, sort_keys=True))


def source_inventory(eels, report):
    def git(*args):
        return driver.run_child(["git", "--no-replace-objects", "-C", eels, *args], report)

    pin = tomllib.loads((driver.ROOT / "reference.toml").read_text())["release"]["commit"]
    require(git("rev-parse", "HEAD").decode().strip() == pin, "wrong source commit")
    require(not git("status", "--porcelain=v1", "--untracked-files=all"), "dirty source checkout")
    result = {}
    for entry in git("ls-tree", "-rz", pin, "--", "src/ethereum", "uv.lock").split(b"\0"):
        if not entry:
            continue
        header, path = entry.decode().split("\t", 1)
        mode, kind, oid = header.split()
        file = eels / path
        require(kind == "blob" and mode in ("100644", "100755") and file.resolve() == file,
                "unexpected source file kind")
        data = file.read_bytes()
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        require(hashlib.sha1(blob).hexdigest() == oid, "source differs from pin: " + path)
        result[str(file)] = {"path": str(file), "size": len(data),
                             "sha256": hashlib.sha256(data).hexdigest()}
    return result


def compare_source(eels, paths, cases, report):
    executable = eels / ".venv/bin/python"
    inputs_paths = [Path(__file__), INPUTS, AUTH, STATE / "pre_state_account_differential.py",
                    driver.ROOT / "reference.toml", executable, *paths]
    report["inputs_before"] = [driver.file_identity(path) for path in inputs_paths]
    targets = [parse_target(path.read_bytes(), cases) for path in paths]
    report["source_before"] = source_inventory(eels, report)

    workers = []
    for flags in ([], ["-O"]):
        data = driver.run_child([executable, "-I", "-B", *flags, Path(__file__), "--worker",
                                 "--eels", eels], report)
        require(len(data) <= 2**21, "oversized source output")
        worker_result = reader.decode(data)
        require(type(worker_result) is dict and worker_result.keys() == {"observations", "authentication"},
                "invalid source worker envelope")
        workers.append(worker_result)

    driver.check_authentication(*(worker_result["authentication"] for worker_result in workers))
    reader.strict_equal(workers[0]["observations"], workers[1]["observations"], "source modes")
    required_modules = {"ethereum.forks.amsterdam.vm", "ethereum.forks.amsterdam.vm.instructions.storage",
                        "ethereum.forks.amsterdam.vm.stack", "ethereum.forks.amsterdam.vm.gas",
                        "ethereum.forks.amsterdam.state_tracker", "ethereum.trace"}
    for result in workers:
        auth = result["authentication"]
        compiled = auth["source_loading"]["compiled_sources"]
        require(required_modules <= compiled.keys(), "missing executed EELS module")
        verified = {file["path"]: file for package in auth["dependencies"]
                    for file in package["verified_files"]}
        for name, identity in compiled.items():
            package = name.partition(".")[0]
            if package == "ethereum":
                module = eels / "src" / name.replace(".", "/")
                require(identity["path"] in {str(module.with_suffix(".py")), str(module / "__init__.py")},
                        "wrong path for loaded " + name)
                reader.strict_equal(identity, report["source_before"].get(identity["path"]), "loaded " + name)
            elif package in {"ethereum_types", "ethereum_rlp"}:
                reader.strict_equal(identity, verified.get(identity["path"]), "loaded " + name)
        reader.strict_equal(auth["uv_lock"], report["source_before"][str(eels / "uv.lock")], "lock")

    source_cases = [case for case in cases if case["eels"]]
    observations = workers[0]["observations"]
    require(type(observations) is list and len(observations) == len(source_cases),
            "wrong EELS observation count")
    for case, row in zip(source_cases, observations, strict=True):
        expected_row, events = expected(case)
        reader.strict_equal(row, source_projection(expected_row) | {"events": events}, case["id"])
    for target in targets:
        selected = [source_projection(row) for case, row in zip(cases, target, strict=True) if case["eels"]]
        reader.strict_equal([{name: value for name, value in row.items() if name != "events"}
                             for row in observations], selected, "source and target")

    report["source_after"] = source_inventory(eels, report)
    report["inputs_after"] = [driver.file_identity(path) for path in inputs_paths]
    reader.strict_equal(report["source_before"], report["source_after"], "pinned source stability")
    reader.strict_equal(report["inputs_before"], report["inputs_after"], "input stability")
    report.update(status="PASS", source_cases=len(source_cases), target_cases=len(cases),
                  compared_targets=len(paths), source_modes_equal=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", action="append", type=Path, default=[])
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        worker(args.eels.resolve())
        return
    if not args.check_target:
        parser.error("expected --check-target")
    cases = inputs()
    if args.eels is None:
        for path in args.check_target:
            parse_target(path.read_bytes(), cases)
        print(f"PASS TLOAD target: {len(cases)} complete cases per stream")
        return
    if args.report is None:
        parser.error("source comparison requires --report")
    eels, destination = args.eels.resolve(), args.report.resolve()
    if destination.is_relative_to(eels):
        parser.error("report must be outside EELS")
    os.environ["GIT_OPTIONAL_LOCKS"] = "0"
    report = {"status": "FAILED", "executions": []}
    with destination.open("x") as out:
        try:
            compare_source(eels, [path.resolve() for path in args.check_target], cases, report)
        except Exception as error:
            report["error"] = type(error).__name__ + ": " + str(error)
            raise
        finally:
            json.dump(report, out, indent=2)
            out.write("\n")
    print(f"PASS TLOAD source: {report['source_cases']} cases per mode")


if __name__ == "__main__":
    main()
