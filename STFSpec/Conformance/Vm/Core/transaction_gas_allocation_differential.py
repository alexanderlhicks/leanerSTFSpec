#!/usr/bin/env python3
"""WI302 complete allocation frames; original imports are lazy and explicit.

Local limits bound evidence processing, never the Lean or guest input domain.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

SCHEMA = "transaction-gas-allocation-v1"
METER_FIELDS = ("gasLeft", "stateGasLeft", "stateGasBaseline", "refundCounter",
                "stateGasSpilled", "stateGasCommittedSpill")
# Hand-frozen complete CATALOG literals, independent of the target implementation.
TARGET = [{'id': 'P01', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '0', 'intrinsicExecution': '0', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P02', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '1', 'intrinsicExecution': '0', 'allocation': {'executionGas': '1', 'stateGasReservoir': '0'}}}, {'id': 'P03', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '1', 'intrinsicExecution': '1', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P04', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777215', 'intrinsicExecution': '0', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '0'}}}, {'id': 'P05', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777216', 'intrinsicExecution': '0', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '0'}}}, {'id': 'P06', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777217', 'intrinsicExecution': '0', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '1'}}}, {'id': 'P07', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777216', 'intrinsicExecution': '1', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '0'}}}, {'id': 'P08', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777217', 'intrinsicExecution': '1', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '1'}}}, {'id': 'P09', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777215', 'intrinsicExecution': '16777215', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P10', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777216', 'intrinsicExecution': '16777216', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P11', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '16777217', 'intrinsicExecution': '16777216', 'allocation': {'executionGas': '0', 'stateGasReservoir': '1'}}}, {'id': 'P12', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '4294967295', 'intrinsicExecution': '16777216', 'allocation': {'executionGas': '0', 'stateGasReservoir': '4278190079'}}}, {'id': 'P13', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '4294967296', 'intrinsicExecution': '0', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '4278190080'}}}, {'id': 'P14', 'kind': 'allocation', 'payload': {'cap': '16777216', 'txGas': '5', 'intrinsicExecution': '2', 'allocation': {'executionGas': '3', 'stateGasReservoir': '0'}}}, {'id': 'G01', 'kind': 'allocation', 'payload': {'cap': '0', 'txGas': '0', 'intrinsicExecution': '0', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'G02', 'kind': 'allocation', 'payload': {'cap': '0', 'txGas': '7', 'intrinsicExecution': '0', 'allocation': {'executionGas': '0', 'stateGasReservoir': '7'}}}, {'id': 'G03', 'kind': 'allocation', 'payload': {'cap': '7', 'txGas': '5', 'intrinsicExecution': '2', 'allocation': {'executionGas': '3', 'stateGasReservoir': '0'}}}, {'id': 'G04', 'kind': 'allocation', 'payload': {'cap': '7', 'txGas': '9', 'intrinsicExecution': '2', 'allocation': {'executionGas': '5', 'stateGasReservoir': '2'}}}, {'id': 'G05', 'kind': 'allocation', 'payload': {'cap': '9', 'txGas': '9', 'intrinsicExecution': '2', 'allocation': {'executionGas': '7', 'stateGasReservoir': '0'}}}, {'id': 'G06', 'kind': 'allocation', 'payload': {'cap': '7', 'txGas': '9', 'intrinsicExecution': '0', 'allocation': {'executionGas': '7', 'stateGasReservoir': '2'}}}, {'id': 'W01', 'kind': 'allocation', 'payload': {'cap': '7', 'txGas': '18446744073709551616', 'intrinsicExecution': '2', 'allocation': {'executionGas': '5', 'stateGasReservoir': '18446744073709551609'}}}, {'id': 'W02', 'kind': 'allocation', 'payload': {'cap': '18446744073709551623', 'txGas': '18446744073709551625', 'intrinsicExecution': '2', 'allocation': {'executionGas': '18446744073709551621', 'stateGasReservoir': '2'}}}, {'id': 'W03', 'kind': 'allocation', 'payload': {'cap': '115792089237316195423570985008687907853269984665640564039457584007913129639943', 'txGas': '115792089237316195423570985008687907853269984665640564039457584007913129639945', 'intrinsicExecution': '2', 'allocation': {'executionGas': '115792089237316195423570985008687907853269984665640564039457584007913129639941', 'stateGasReservoir': '2'}}}, {'id': 'W04', 'kind': 'allocation', 'payload': {'cap': '115792089237316195423570985008687907853269984665640564039457584007913129639937', 'txGas': '115792089237316195423570985008687907853269984665640564039457584007913129639937', 'intrinsicExecution': '115792089237316195423570985008687907853269984665640564039457584007913129639937', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'D01', 'kind': 'raw', 'payload': {'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}, 'reconstructed': {'executionGas': '0', 'stateGasReservoir': '0'}, 'equal': True}}, {'id': 'D02', 'kind': 'raw', 'payload': {'allocation': {'executionGas': '1', 'stateGasReservoir': '0'}, 'reconstructed': {'executionGas': '1', 'stateGasReservoir': '0'}, 'equal': True}}, {'id': 'D03', 'kind': 'raw', 'payload': {'allocation': {'executionGas': '0', 'stateGasReservoir': '1'}, 'reconstructed': {'executionGas': '0', 'stateGasReservoir': '1'}, 'equal': True}}, {'id': 'D04', 'kind': 'raw', 'payload': {'allocation': {'executionGas': '115792089237316195423570985008687907853269984665640564039457584007913129639937', 'stateGasReservoir': '18446744073709551617'}, 'reconstructed': {'executionGas': '115792089237316195423570985008687907853269984665640564039457584007913129639937', 'stateGasReservoir': '18446744073709551617'}, 'equal': True}}, {'id': 'E01', 'kind': 'relation', 'payload': {'left': {'executionGas': '5', 'stateGasReservoir': '2'}, 'right': {'executionGas': '5', 'stateGasReservoir': '2'}, 'equal': True}}, {'id': 'E02', 'kind': 'relation', 'payload': {'left': {'executionGas': '5', 'stateGasReservoir': '2'}, 'right': {'executionGas': '7', 'stateGasReservoir': '0'}, 'equal': False}}, {'id': 'M01', 'kind': 'entry', 'payload': {'meter': {'gasLeft': '5', 'stateGasLeft': '2', 'stateGasBaseline': '2', 'refundCounter': '0', 'stateGasSpilled': '0', 'stateGasCommittedSpill': '0'}, 'phi': '5', 'usage': '0'}}, {'id': 'M02', 'kind': 'charge', 'payload': {'status': 'ok', 'meter': {'gasLeft': '5', 'stateGasLeft': '2', 'stateGasBaseline': '2', 'refundCounter': '0', 'stateGasSpilled': '0', 'stateGasCommittedSpill': '0'}, 'phi': '5'}}, {'id': 'M03', 'kind': 'charge', 'payload': {'status': 'ok', 'meter': {'gasLeft': '2', 'stateGasLeft': '2', 'stateGasBaseline': '2', 'refundCounter': '0', 'stateGasSpilled': '0', 'stateGasCommittedSpill': '0'}, 'phi': '2'}}, {'id': 'M04', 'kind': 'charge', 'payload': {'status': 'ok', 'meter': {'gasLeft': '0', 'stateGasLeft': '2', 'stateGasBaseline': '2', 'refundCounter': '0', 'stateGasSpilled': '0', 'stateGasCommittedSpill': '0'}, 'phi': '0'}}, {'id': 'M05', 'kind': 'charge', 'payload': {'status': 'error', 'error': 'outOfGas'}}, {'id': 'M06', 'kind': 'charge', 'payload': {'status': 'ok', 'meter': {'gasLeft': '4', 'stateGasLeft': '0', 'stateGasBaseline': '2', 'refundCounter': '0', 'stateGasSpilled': '1', 'stateGasCommittedSpill': '0'}, 'phi': '5', 'usage': '3'}}]
SOURCE = [{'id': 'P01', 'kind': 'source-success', 'payload': {'txGas': '0', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P02', 'kind': 'source-success', 'payload': {'txGas': '1', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '1', 'stateGasReservoir': '0'}}}, {'id': 'P03', 'kind': 'source-success', 'payload': {'txGas': '1', 'intrinsic': {'execution': '1', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P04', 'kind': 'source-success', 'payload': {'txGas': '16777215', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '0'}}}, {'id': 'P05', 'kind': 'source-success', 'payload': {'txGas': '16777216', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '0'}}}, {'id': 'P06', 'kind': 'source-success', 'payload': {'txGas': '16777217', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '1'}}}, {'id': 'P07', 'kind': 'source-success', 'payload': {'txGas': '16777216', 'intrinsic': {'execution': '1', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '0'}}}, {'id': 'P08', 'kind': 'source-success', 'payload': {'txGas': '16777217', 'intrinsic': {'execution': '1', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777215', 'stateGasReservoir': '1'}}}, {'id': 'P09', 'kind': 'source-success', 'payload': {'txGas': '16777215', 'intrinsic': {'execution': '16777215', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P10', 'kind': 'source-success', 'payload': {'txGas': '16777216', 'intrinsic': {'execution': '16777216', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '0'}}}, {'id': 'P11', 'kind': 'source-success', 'payload': {'txGas': '16777217', 'intrinsic': {'execution': '16777216', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '1'}}}, {'id': 'P12', 'kind': 'source-success', 'payload': {'txGas': '4294967295', 'intrinsic': {'execution': '16777216', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '0', 'stateGasReservoir': '4278190079'}}}, {'id': 'P13', 'kind': 'source-success', 'payload': {'txGas': '4294967296', 'intrinsic': {'execution': '0', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '16777216', 'stateGasReservoir': '4278190080'}}}, {'id': 'P14', 'kind': 'source-success', 'payload': {'txGas': '5', 'intrinsic': {'execution': '2', 'calldata_floor': '16777217'}, 'numericClass': 'ethereum_types.numeric.Uint', 'allocation': {'executionGas': '3', 'stateGasReservoir': '0'}}}, {'id': 'F01', 'kind': 'source-error', 'payload': {'txGas': '1', 'intrinsic': {'execution': '2', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'error': {'class': 'builtins.OverflowError', 'message': '', 'args': []}}}, {'id': 'F02', 'kind': 'source-error', 'payload': {'txGas': '16777218', 'intrinsic': {'execution': '16777217', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'error': {'class': 'builtins.OverflowError', 'message': '', 'args': []}}}, {'id': 'F03', 'kind': 'source-error', 'payload': {'txGas': '16777215', 'intrinsic': {'execution': '16777217', 'calldata_floor': '0'}, 'numericClass': 'ethereum_types.numeric.Uint', 'error': {'class': 'builtins.OverflowError', 'message': '', 'args': []}}}]


class AdmissionError(ValueError):
    def __init__(self, reason, detail=""):
        self.reason = reason
        super().__init__(reason + (": " + detail if detail else ""))


def require(condition, reason, detail=""):
    if not condition:
        raise AdmissionError(reason, detail)


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), "shape")


def nat(value):
    require(type(value) is str and len(value) <= 1024 and
            re.fullmatch(r"0|[1-9][0-9]*", value, re.ASCII) is not None, "scalar")
    return value


def integer(value):
    require(type(value) is str and len(value.lstrip("-")) <= 1024 and
            re.fullmatch(r"0|-?[1-9][0-9]*", value, re.ASCII) is not None, "scalar")
    return value


def boolean(value):
    require(type(value) is bool, "scalar")
    return value


def allocation(value):
    keys(value, ("executionGas", "stateGasReservoir"))
    for field in value:
        nat(value[field])
    return value


def meter(value):
    keys(value, METER_FIELDS)
    for field in METER_FIELDS:
        (integer if field == "refundCounter" else nat)(value[field])
    return value


def success(value):
    require(type(value) is dict, "shape")
    keys(value, ("status", "meter", "phi", "usage") if "usage" in value else ("status", "meter", "phi"))
    require(value["status"] == "ok", "error")
    meter(value["meter"])
    nat(value["phi"])
    if "usage" in value:
        integer(value["usage"])
    return value


def failure(value):
    keys(value, ("status", "error"))
    require(value["status"] == "error" and value["error"] == "outOfGas", "error")
    return value


def source_error(value):
    keys(value, ("class", "message", "args"))
    require(value["class"] == "builtins.OverflowError" and type(value["message"]) is str
            and type(value["args"]) is list, "error")
    require(value["message"] == "" and value["args"] == [], "error")
    return value


def end_record(value, count):
    keys(value, ("end", "count"))
    require(type(value["end"]) is bool and value["end"] is True and
            type(value["count"]) is int and value["count"] == count, "end")
    return value


def expected_records(mode):
    require(mode in ("target", "source"), "header")
    return copy.deepcopy(TARGET if mode == "target" else SOURCE)


def encode_frame(records, mode):
    frames = [{"schema": SCHEMA, "mode": mode, "count": len(records)}, *records,
              {"end": True, "count": len(records)}]
    return ("\n".join(json.dumps(row, separators=(",", ":"), allow_nan=False) for row in frames) + "\n").encode("ascii")


def unique_pairs(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "json", "duplicate key")
        out[key] = value
    return out


def invalid_constant(value):
    raise AdmissionError("json", value)


def decode_payload(kind, value):
    require(type(value) is dict, "shape")
    if kind == "allocation":
        keys(value, ("cap", "txGas", "intrinsicExecution", "allocation"))
        for field in ("cap", "txGas", "intrinsicExecution"):
            nat(value[field])
        allocation(value["allocation"])
    elif kind == "raw":
        keys(value, ("allocation", "reconstructed", "equal"))
        allocation(value["allocation"])
        allocation(value["reconstructed"])
        boolean(value["equal"])
    elif kind == "relation":
        keys(value, ("left", "right", "equal"))
        allocation(value["left"])
        allocation(value["right"])
        boolean(value["equal"])
    elif kind == "entry":
        keys(value, ("meter", "phi", "usage"))
        meter(value["meter"])
        nat(value["phi"])
        integer(value["usage"])
    elif kind == "charge":
        (failure if value.get("status") == "error" else success)(value)
    elif kind in ("source-success", "source-error"):
        keys(value, ("txGas", "intrinsic", "numericClass", "allocation" if kind == "source-success" else "error"))
        nat(value["txGas"])
        keys(value["intrinsic"], ("execution", "calldata_floor"))
        nat(value["intrinsic"]["execution"])
        nat(value["intrinsic"]["calldata_floor"])
        require(value["numericClass"] == "ethereum_types.numeric.Uint", "class")
        (allocation if kind == "source-success" else source_error)(value["allocation" if kind == "source-success" else "error"])
    else:
        raise AdmissionError("shape", "unknown kind")


def parse_frame(data, mode):
    require(type(data) is bytes, "json")
    require(len(data) <= 262144, "frame-limit")
    lines = data.splitlines()
    require(all(len(line) <= 32768 for line in lines), "line-limit")
    try:
        frames = [json.loads(line, object_pairs_hook=unique_pairs, parse_constant=invalid_constant)
                  for line in lines]
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as error:
        raise AdmissionError("json", str(error)) from error
    expected = expected_records(mode)
    require(len(frames) == len(expected) + 2, "count")
    header = frames[0]
    keys(header, ("schema", "mode", "count"))
    require(header["schema"] == SCHEMA and header["mode"] == mode and
            type(header["count"]) is int and header["count"] == len(expected), "header")
    for actual, frozen in zip(frames[1:-1], expected, strict=True):
        keys(actual, ("id", "kind", "payload"))
        require(type(actual["id"]) is str and actual["id"] == frozen["id"], "order")
        require(actual["kind"] == frozen["kind"], "shape")
        decode_payload(actual["kind"], actual["payload"])
        require(actual == frozen, "value", actual["id"])
    end_record(frames[-1], len(expected))
    require(data.endswith(b"\n"), "json", "missing final newline")
    return frames[1:-1]


def run_original(eels, evidence, profile, target_path):
    """One closed original schedule, after zero-call typed/provenance admission.

    CPython/NewType/generated dataclass/installed dependencies are explicit host
    premises. Raw loaded-code marshal hashes describe this interpreter's objects;
    they are not portable canonical source hashes or whole-host certification.
    """
    import base64
    import dataclasses
    import hashlib
    import importlib
    import importlib.metadata
    import inspect
    import marshal
    import platform
    import traceback

    require(profile in ("WI302-ALLOCATION-author-01", "WI302-ALLOCATION-root-01",
                        "WI302-ALLOCATION-review-a-01", "WI302-ALLOCATION-review-b-01"), "provenance", "unreleased profile")
    # Read/check the actual target stdout before loading any original dependency.
    target = parse_frame(target_path.read_bytes(), "target")
    require(not any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
                    for name in sys.modules), "provenance", "original already loaded")
    eels = eels.resolve(strict=True)
    evidence = evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    journal = (evidence / "events.jsonl").open("x", encoding="ascii")

    def write(event):
        # Finite primitive metadata only. Serialization must succeed before entry.
        journal.write(json.dumps(event, separators=(",", ":"), allow_nan=False) + "\n")
        journal.flush()

    def file_info(path):
        path = Path(path).resolve(strict=True)
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        retained = evidence / "inputs" / (digest + ".bin")
        retained.parent.mkdir(exist_ok=True)
        if not retained.exists():
            retained.write_bytes(data)
        require(retained.read_bytes() == data, "provenance", "retained input bytes")
        return {"path": str(path), "retained": str(retained), "sha256": digest,
                "bytes": len(data), "mode": oct(path.stat().st_mode & 0o777)}

    interpreter = Path(sys.executable).resolve(strict=True)
    require(platform.python_implementation() == "CPython" and platform.python_version() == "3.13.7"
            and sys.flags.isolated == 1 and sys.flags.dont_write_bytecode == 1
            and sys.flags.optimize == 0, "provenance", "runtime/options")
    require(interpreter == Path("/home/alh/.local/share/uv/python/cpython-3.13.7-linux-x86_64-gnu/bin/python3.13"),
            "provenance", "interpreter path")
    expected_text = {
        "src/ethereum/forks/amsterdam/vm/gas.py": "91d7240e67b18b1f4406e17c11c1e9a8cf2e83b93e0dd0eb5071a23ba2a2ccc0",
        "src/ethereum/forks/amsterdam/fork_types.py": "3e0013e251867df02aca7b746b77403b36b41d73f7c4158bed09964838c935ca",
        "src/ethereum/forks/amsterdam/transactions.py": "120507bf6258289b2072cba60446b29ce9e86e987d063f82b0c9e926a84987da",
        ".venv/lib/python3.13/site-packages/ethereum_types/numeric.py": "47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46",
    }
    source_files = [file_info(eels / path) for path in expected_text]
    for path, info in zip(expected_text, source_files, strict=True):
        require(info["sha256"] == expected_text[path], "provenance", path)
    sys.path.insert(0, str(eels / "src"))
    gas = importlib.import_module("ethereum.forks.amsterdam.vm.gas")
    numeric = importlib.import_module("ethereum_types.numeric")
    fork_types = importlib.import_module("ethereum.forks.amsterdam.fork_types")
    transactions = importlib.import_module("ethereum.forks.amsterdam.transactions")
    Uint = numeric.Uint
    original = gas.allocate_evm_gas
    require(Path(gas.__file__).resolve() == eels / "src/ethereum/forks/amsterdam/vm/gas.py",
            "provenance", "whole module path")
    require(gas.Uint is Uint and gas.ExecutionGas is fork_types.ExecutionGas and
            gas.StateGas is fork_types.StateGas and gas.IntrinsicGasCost is transactions.IntrinsicGasCost,
            "provenance", "original bindings")
    require(original.__globals__ is gas.__dict__ and original.__defaults__ is None and
            original.__kwdefaults__ is None and tuple(inspect.signature(original).parameters) == ("tx_gas", "intrinsic"),
            "provenance", "callable/globals/defaults")
    require(original.__code__.co_filename == gas.__file__ and original.__code__.co_firstlineno == 1120,
            "provenance", "loaded code location")
    require(gas.ExecutionGas.__supertype__ is Uint and gas.StateGas.__supertype__ is Uint,
            "provenance", "NewType supertypes")
    require(tuple(field.name for field in dataclasses.fields(gas.IntrinsicGasCost)) == ("execution", "calldata_floor")
            and tuple(field.name for field in dataclasses.fields(gas.EvmGasAllocation)) == ("execution_gas", "state_gas_reservoir"),
            "provenance", "ordered dataclass fields")

    def observation(value):
        # Admission precedes conversion/equality, including Python bool/int traps.
        require(type(value) is Uint, "class", "expected actual Uint")
        raw = value._number
        require(type(raw) is int and raw >= 0, "class", "Uint._number")
        return {"class": "ethereum_types.numeric.Uint", "numberClass": "builtins.int", "value": str(raw)}

    def code_info(value):
        code = getattr(value, "__code__", None)
        item = {"id": id(value), "runtimeClass": type(value).__module__ + "." + type(value).__qualname__}
        if code is not None:
            marshalled = marshal.dumps(code)
            retained = evidence / "loaded-code" / (hashlib.sha256(marshalled).hexdigest() + ".marshal")
            retained.parent.mkdir(exist_ok=True)
            if not retained.exists():
                retained.write_bytes(marshalled)
            item.update(codeId=id(code), codeFile=code.co_filename, firstLine=code.co_firstlineno,
                        bytecodeSha256=hashlib.sha256(code.co_code).hexdigest())
        else:
            item["interpretation"] = "native/runtime callable; no ordinary Python code object"
        return item

    def context():
        require(gas.allocate_evm_gas is original and original.__globals__ is gas.__dict__ and
                original.__defaults__ is None and original.__kwdefaults__ is None and gas.Uint is Uint
                and gas.ExecutionGas is fork_types.ExecutionGas and gas.StateGas is fork_types.StateGas
                and gas.IntrinsicGasCost is transactions.IntrinsicGasCost,
                "provenance", "binding changed")
        require(gas.ExecutionGas.__supertype__ is Uint and gas.StateGas.__supertype__ is Uint,
                "provenance", "NewType changed")
        cap = observation(gas.GasCosts.TX_MAX_GAS_LIMIT)
        total = observation(gas.GasCosts.TX_MAX_TOTAL_GAS_LIMIT)
        require(cap["value"] == "16777216" and total["value"] == "4294967295", "provenance", "live caps")
        return {"allocate": code_info(original), "globalsId": id(original.__globals__),
                "UintId": id(Uint), "ExecutionGas": code_info(gas.ExecutionGas),
                "StateGas": code_info(gas.StateGas), "NewTypeCall": code_info(type(gas.ExecutionGas).__call__),
                "IntrinsicGasCostId": id(gas.IntrinsicGasCost), "EvmGasAllocationId": id(gas.EvmGasAllocation),
                "intrinsicFields": [field.name for field in dataclasses.fields(gas.IntrinsicGasCost)],
                "allocationFields": [field.name for field in dataclasses.fields(gas.EvmGasAllocation)],
                "intrinsicInit": code_info(gas.IntrinsicGasCost.__init__),
                "allocationInit": code_info(gas.EvmGasAllocation.__init__),
                "GasCostsId": id(gas.GasCosts), "capId": id(gas.GasCosts.TX_MAX_GAS_LIMIT),
                "cap": cap, "totalCapId": id(gas.GasCosts.TX_MAX_TOTAL_GAS_LIMIT), "totalCap": total,
                "numericMethods": {name: code_info(getattr(Uint, name)) for name in
                                   ("__init__", "__sub__", "__rsub__", "__lt__", "__le__", "__eq__", "__int__", "_in_range")}}

    def input_info(tx, intrinsic):
        require(type(intrinsic) is gas.IntrinsicGasCost, "class", "intrinsic record")
        return {"txGas": observation(tx), "intrinsicClass": "ethereum.forks.amsterdam.transactions.IntrinsicGasCost",
                "fields": [{"name": "execution", **observation(intrinsic.execution)},
                           {"name": "calldata_floor", **observation(intrinsic.calldata_floor)}]}

    # Compile complete physical modules without executing them. Match ordinary
    # loaded Python code to its whole-file compilation, without extracting a helper.
    import types
    compiled = {}
    def collect_code(code):
        compiled[(code.co_filename, code.co_qualname, code.co_firstlineno)] = code
        for constant in code.co_consts:
            if type(constant) is types.CodeType:
                collect_code(constant)
    for relative in expected_text:
        path = eels / relative
        collect_code(compile(path.read_bytes(), str(path), "exec", dont_inherit=True, optimize=0))
    matched_code = []
    for name, function in [("allocate_evm_gas", original)] + [
            ("Uint." + method, getattr(Uint, method)) for method in
            ("__init__", "__sub__", "__rsub__", "__lt__", "__le__", "__eq__", "__int__", "_in_range")]:
        code = function.__code__
        key = (code.co_filename, code.co_qualname, code.co_firstlineno)
        require(key in compiled and code == compiled[key],
                "provenance", "whole-file loaded code mismatch: " + name)
        matched_code.append({"name": name, "structuralCodeEqual": True,
                             "loadedCodeMarshalSha256": hashlib.sha256(marshal.dumps(code)).hexdigest(),
                             "wholeFileCompiledMarshalSha256": hashlib.sha256(marshal.dumps(compiled[key])).hexdigest(),
                             **code_info(function)})

    # Exactly the released 17 fixture constructions; no source invocation here.
    prepared = []
    for frozen in SOURCE:
        payload = frozen["payload"]
        tx = Uint(int(nat(payload["txGas"])))
        execution = Uint(int(nat(payload["intrinsic"]["execution"])))
        floor = Uint(int(nat(payload["intrinsic"]["calldata_floor"])))
        intrinsic = gas.IntrinsicGasCost(gas.ExecutionGas(execution), gas.ExecutionGas(floor))
        require(intrinsic.execution is execution and intrinsic.calldata_floor is floor and
                gas.ExecutionGas(execution) is execution and gas.StateGas(tx) is tx,
                "provenance", "native NewType identity behavior")
        prepared.append((frozen["id"], tx, intrinsic, input_info(tx, intrinsic)))
    before = context()
    distribution = importlib.metadata.distribution("ethereum-types")
    require(distribution.version == "0.4.1", "provenance", "dependency version")
    record_path = Path(distribution._path) / "RECORD"
    record = distribution.read_text("RECORD")
    require(type(record) is str, "provenance", "installed RECORD")
    # Authenticate each hashed installed distribution row, not just its metadata.
    import csv
    import io
    installed = []
    for relative, digest, length in csv.reader(io.StringIO(record)):
        path = Path(distribution.locate_file(relative)).resolve(strict=True)
        info = file_info(path)
        if digest:
            algorithm, expected = digest.split("=", 1)
            require(algorithm == "sha256" and base64.urlsafe_b64encode(bytes.fromhex(info["sha256"])).rstrip(b"=").decode() == expected
                    and str(info["bytes"]) == length, "provenance", "installed RECORD mismatch")
        installed.append(info)
    loaded_files = []
    for name, module in sorted(sys.modules.items()):
        path = getattr(module, "__file__", None)
        if path and (name.startswith(("ethereum.", "ethereum_types")) or name in ("typing", "dataclasses", "_typing")):
            loaded_files.append({"module": name, **file_info(path)})
    import sysconfig
    runtime_library = Path(sysconfig.get_config_var("LIBDIR")) / sysconfig.get_config_var("LDLIBRARY")
    runtime_library_info = file_info(runtime_library)
    write({"event": "preflight", "selectedCalls": 0, "profile": profile, "seed": 30201, "rngUsed": False,
           "interpreter": file_info(interpreter), "runtimeLibrary": runtime_library_info, "runtime": sys.version,
           "runtimeFlags": {"isolated": sys.flags.isolated, "optimize": sys.flags.optimize,
                            "dontWriteBytecode": sys.flags.dont_write_bytecode},
           "sourcePin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36", "sourceFiles": source_files,
           "venv": file_info(eels / ".venv/pyvenv.cfg"), "lock": file_info(eels / "uv.lock"),
           "record": file_info(record_path), "installedFiles": installed, "loadedFiles": loaded_files,
           "wholeFileCodeMatches": matched_code, "context": before, "prepared": [{"id": case, "input": inputs} for case, _, _, inputs in prepared]})
    records = []
    for index, (case, tx, intrinsic, inputs) in enumerate(prepared):
        require(context() == before and input_info(tx, intrinsic) == inputs, "provenance", "before-entry changed")
        write({"event": "planned-before-entry", "index": index, "id": case, "input": inputs, "context": before})
        try:
            result = original(tx, intrinsic)  # Sole selected original entry, exactly once per released row.
        except Exception as error:
            require(type(error) is OverflowError and case.startswith("F"), "source-error", "unexpected exception")
            require(type(error.args) is tuple and len(error.args) == 0, "source-error", "exception args")
            actual_error = {"class": "builtins.OverflowError", "message": str(error), "args": list(error.args)}
            source_error(actual_error)
            payload = {"txGas": inputs["txGas"]["value"],
                       "intrinsic": {item["name"]: item["value"] for item in inputs["fields"]},
                       "numericClass": "ethereum_types.numeric.Uint", "error": actual_error}
            frame = {"id": case, "kind": "source-error", "payload": payload}
            result_info = {"error": actual_error, "traceback": [{"file": row.filename, "line": row.lineno, "name": row.name}
                                                                for row in traceback.extract_tb(error.__traceback__)]}
        else:
            require(type(result) is gas.EvmGasAllocation and case.startswith("P"), "class", "result record")
            e = observation(result.execution_gas)
            r = observation(result.state_gas_reservoir)
            payload = {"txGas": inputs["txGas"]["value"],
                       "intrinsic": {item["name"]: item["value"] for item in inputs["fields"]},
                       "numericClass": "ethereum_types.numeric.Uint", "allocation": {"executionGas": e["value"], "stateGasReservoir": r["value"]}}
            frame = {"id": case, "kind": "source-success", "payload": payload}
            require(payload["allocation"] == target[index]["payload"]["allocation"], "value", "source/native comparison")
            result_info = {"class": "ethereum.forks.amsterdam.vm.gas.EvmGasAllocation",
                           "fields": [{"name": "execution_gas", **e}, {"name": "state_gas_reservoir", **r}]}
        after = context()
        after_input = input_info(tx, intrinsic)
        require(after == before and after_input == inputs, "provenance", "post-call changed")
        require(frame == SOURCE[index], "value", case)
        records.append(frame)
        write({"event": "observed", "index": index, "id": case, "inputBefore": inputs,
               "inputAfter": after_input, "result": result_info, "contextAfter": after})
    data = encode_frame(records, "source")
    parse_frame(data, "source")
    write({"event": "finished", "selectedCalls": 17, "successesComparedToTarget": 14,
           "sourceOnlyFailures": 3, "contextUnchanged": context() == before})
    journal.close()
    sys.stdout.buffer.write(data)
    sys.stdout.buffer.flush()
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-target", type=Path)
    mode.add_argument("--check-source", type=Path)
    mode.add_argument("--source-eels", type=Path)
    parser.add_argument("--source-evidence", type=Path)
    parser.add_argument("--profile")
    parser.add_argument("--target-native", type=Path)
    args = parser.parse_args(argv)
    if args.source_eels:
        if not args.source_evidence or not args.profile or not args.target_native:
            parser.error("source requires --source-evidence, --profile and --target-native")
    elif args.source_evidence or args.profile or args.target_native:
        parser.error("source options require --source-eels")
    try:
        if args.source_eels:
            return run_original(args.source_eels, args.source_evidence, args.profile, args.target_native)
        selected = "target" if args.check_target else "source"
        path = args.check_target or args.check_source
        with path.open("rb") as stream:
            data = stream.read(262145)
        records = parse_frame(data, selected)
        require(not any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
                        for name in sys.modules), "class", "unexpected original import")
        print(f"PASS allocation {selected}: {len(records)} complete groups; original imports/calls 0")
        return 0
    except (AdmissionError, OSError) as error:
        print(f"FAIL allocation: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
