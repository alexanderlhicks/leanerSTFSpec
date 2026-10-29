#!/usr/bin/env python3
"""Finite interpreted transfer-log producer/comparator; no source execution.

The authenticated catalogue is qualified SOURCE input only. Python source stack
storage is bottom first: generated checked pushes preserve that storage order;
the target observer explicitly reverses Stack.toList. Exactly three finite-set
arrays compare by membership. All logs/topics/bytes and slot coordinates retain
order. Complete byte contents compare, not cross-language runtime classes.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess

CATALOGUE_SHA256 = "fad89d538c7e6b9e188432de31564e4fecd90d8c6ba698af49f1f69b432e4779"
SOURCE_SHA256 = {
    "9583379bdf193fd135982226095c4b32617a9b1326bd59ad875909c2906b1d4f",
    "f4c57775b0377bc5627c3df78c210eef0c48a819d54af3134403e4fb3bc52649",
}
SYSTEM_ADDRESS = "ff" * 19 + "fe"
TRANSFER_TOPIC = "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"
FIELDS = ("pc", "stack", "memory", "gas_meter", "logs", "accounts_to_delete",
          "return_data", "accessed_addresses", "accessed_storage_keys")
METER = ("gas_left", "state_gas_left", "state_gas_baseline", "refund_counter",
         "state_gas_spilled", "state_gas_committed_spill")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for k, v in pairs:
        require(k not in result, "duplicate JSON field")
        result[k] = v
    return result


def read_json(path, hashes=None):
    data = path.read_bytes()
    if hashes is not None:
        require(hashlib.sha256(data).hexdigest() in hashes, "unauthenticated input bytes")
    return json.loads(data, object_pairs_hook=unique_object)


def integer(x, minimum=None, limit=None):
    require(type(x) is int, "integer type (bool/float aliases rejected)")
    require(minimum is None or minimum <= x, "integer lower bound")
    require(limit is None or x < limit, "integer upper bound")


def hex_bytes(x, width=None):
    require(type(x) is str and re.fullmatch(r"(?:[0-9a-f]{2})*", x) is not None,
            "canonical complete hex bytes")
    require(width is None or len(x) == 2 * width, "fixed byte width")
    return list(bytes.fromhex(x))


def fields(x, keys):
    require(type(x) is dict and set(x) == set(keys), "exact object fields")


def sequence(x):
    require(type(x) is list, "list type")


def check_model(m):
    fields(m, FIELDS)
    integer(m["pc"], 0)
    sequence(m["stack"])
    require(len(m["stack"]) <= 1024, "stack bound")
    for n in m["stack"]:
        integer(n, 0, 2**256)
    hex_bytes(m["memory"])
    require(len(m["memory"]) % 64 == 0, "memory alignment")
    fields(m["gas_meter"], METER)
    for k in METER:
        integer(m["gas_meter"][k], None if k == "refund_counter" else 0)
    sequence(m["logs"])
    for log in m["logs"]:
        fields(log, ("address", "topics", "data"))
        hex_bytes(log["address"], 20)
        sequence(log["topics"])
        for topic in log["topics"]:
            hex_bytes(topic, 32)
        hex_bytes(log["data"])
    hex_bytes(m["return_data"])
    for k in ("accounts_to_delete", "accessed_addresses"):
        sequence(m[k])
        for address in m[k]:
            hex_bytes(address, 20)
        require(len(set(m[k])) == len(m[k]), "set duplicate")
    sequence(m["accessed_storage_keys"])
    for pair in m["accessed_storage_keys"]:
        sequence(pair)
        require(len(pair) == 2, "slot pair arity")
        hex_bytes(pair[0], 20)
        hex_bytes(pair[1], 32)
    require(len({tuple(p) for p in m["accessed_storage_keys"]}) ==
            len(m["accessed_storage_keys"]), "slot set duplicate")


def projected(m):
    """Finite membership adapter only; never sort ordered model fields."""
    check_model(m)
    out = copy.deepcopy(m)
    for k in ("accounts_to_delete", "accessed_addresses", "accessed_storage_keys"):
        out[k].sort()
    return out


def strict_equal(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(strict_equal(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(strict_equal(x, y) for x, y in zip(a, b))
    return a == b


def equal(a, b):
    require(strict_equal(a, b), "complete typed model mismatch")


def expected(case):
    out = copy.deepcopy(case["before"])
    if case["amount"] != 0:
        out["logs"].append({
            "address": case["system_address"],
            "topics": [case["topic"], "00" * 12 + case["sender"],
                       "00" * 12 + case["recipient"]],
            "data": case["amount"].to_bytes(32, "big").hex(),
        })
    return out


def catalogue_cases(catalogue):
    sequence(catalogue["cases"])
    require(len(catalogue["cases"]) == 32, "32 source cases")
    result = []
    for i, c in enumerate(catalogue["cases"], 1):
        fields(c, ("id", "sender", "recipient", "amount", "before", "expected_after",
                   "expected_return_type", "expected_return"))
        require(c["id"] == f"c{i:02}", "case order and identity")
        hex_bytes(c["sender"], 20)
        hex_bytes(c["recipient"], 20)
        integer(c["amount"], 0, 2**256)
        check_model(c["before"])
        check_model(c["expected_after"])
        require(c["expected_return_type"] == "builtins.NoneType" and
                c["expected_return"] is None, "source return contract")
        c = dict(c, system_address=SYSTEM_ADDRESS, topic=TRANSFER_TOPIC)
        equal(projected(expected(c)), projected(c["expected_after"]))
        result.append(c)
    # Synthetic calls separately vary emitter and first topic, including equal parties.
    for i, (addr, topic, amount) in enumerate([
        (0, 0, 0), (1, 1, 1), (256, 1, 1), (1, 256, 1),
        (2**159 + 128, 2**255 + 257, 2**255),
        (2**160 - 1, 2**256 - 1, 2**256 - 1),
        (1, 2**255, 1), (0, 1, 2**256 - 1),
    ], 1):
        c = copy.deepcopy(result[2])
        c.update(id=f"s{i:02}", system_address=addr.to_bytes(20, "big").hex(),
                 topic=topic.to_bytes(32, "big").hex(), amount=amount)
        if i in (2, 3, 4, 8):
            c["recipient"] = c["sender"]
        c["expected_after"] = expected(c)
        result.append(c)
    return result


def lean_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def lean_bytes(h):
    return "(Bytes.ofList " + lean_list(hex_bytes(h)) + ")"


def address(h):
    return f"(Address.ofNat {int(h, 16)})"


def topic(h):
    return f"(Hash32.ofBytes32 (FixedBytes.ofNat {int(h, 16)}))"


def lean_log(log):
    topics = "#[" + ", ".join(topic(t) for t in log["topics"]) + "]"
    return f"Log.mk {address(log['address'])} {topics} {lean_bytes(log['data'])}"


PRELUDE = '''import STFSpec.Vm.Core
import Lean
open STFSpec.Base STFSpec.Vm.Core Lean
private def bytesJson (b : Bytes) : Json := toJson (b.toList.map UInt8.toNat)
private def addressJson (a : Address) : Json := bytesJson a.toBytes
private def topicJson (t : Hash32) : Json := bytesJson t.toBytes
private def logJson (l : Log) : Json := Json.mkObj [
  ("address", addressJson l.address),
  ("topics", toJson (l.topics.toList.map topicJson)), ("data", bytesJson l.data)]
private def frameJson (f : Frame) : Json := Json.mkObj [
  ("pc", toJson f.pc),
  -- SOURCE Python storage is bottom first; Core's model is top first.
  ("stack", toJson (f.stack.toList.reverse.map U256.toNat)),
  ("memory", toJson (f.memory.toBytes.map UInt8.toNat)),
  ("gas_meter", Json.mkObj [
    ("gas_left", toJson f.gasMeter.gasLeft),
    ("state_gas_left", toJson f.gasMeter.stateGasLeft),
    ("state_gas_baseline", toJson f.gasMeter.stateGasBaseline),
    ("refund_counter", toJson f.gasMeter.refundCounter),
    ("state_gas_spilled", toJson f.gasMeter.stateGasSpilled),
    ("state_gas_committed_spill", toJson f.gasMeter.stateGasCommittedSpill)]),
  ("logs", toJson (f.logs.toList.map logJson)),
  ("accounts_to_delete", toJson (f.accountsToDelete.toList.map addressJson)),
  ("return_data", bytesJson f.returnData),
  ("accessed_addresses", toJson (f.accessedAddresses.toList.map addressJson)),
  ("accessed_storage_keys", toJson (f.accessedStorageKeys.toList.map fun (a, k) ↦
    toJson [addressJson a, bytesJson k.toBytes]))]
'''


def producer(cases):
    text = PRELUDE
    for c in cases:
        name = c["id"]
        m = c["before"]
        stack = "Stack.empty"
        # Checked pushes in SOURCE bottom-first storage order. No failure fallback.
        for n in m["stack"]:
            stack = f"(({stack}).push (U256.ofNat {n})).toOption.get (by decide)"
        text += f"private def {name}Stack : Stack := {stack}\n"
        n = len(m["memory"]) // 2
        text += f"private def {name}Expanded : Memory := Memory.empty.expand {n} (by decide)\n"
        text += f'''private theorem {name}Expanded_size : {name}Expanded.size = {n} := by
  rw [← Memory.length_toBytes, {name}Expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl
private def {name}Memory : Memory := {name}Expanded.write 0 {lean_bytes(m['memory'])} (by
  right
  rw [{name}Expanded_size, Bytes.size_ofList]
  decide)
'''
        sets = []
        for k, typ in [("accounts_to_delete", "AddrSet"), ("accessed_addresses", "AddrSet"),
                       ("accessed_storage_keys", "SlotSet")]:
            expr = f"(∅ : {typ})"
            for v in m[k]:
                item = (address(v) if typ == "AddrSet" else
                        f"({address(v[0])}, (FixedBytes.ofNat {int(v[1], 16)} : Bytes32))")
                expr = f"({expr}.insert {item})"
            sets.append(expr)
        logs = "[" + ", ".join(lean_log(l) for l in m["logs"]) + "]"
        # Independently alternate raw shapes; complete old chronological list is retained.
        rope = f"LogRope.leaf ({logs})"
        if int(name[1:]) % 2 == 0:
            rope = f"LogRope.concat (LogRope.leaf []) ({rope})"
        gas = m["gas_meter"]
        meter = "GasMeter.mk " + " ".join(f"({gas[k]})" for k in METER)
        text += (f"private def {name} : Frame := Frame.mk {m['pc']} {name}Stack "
                 f"{name}Memory ({meter}) ({rope}) {sets[0]} "
                 f"{lean_bytes(m['return_data'])} {sets[1]} {sets[2]}\n")
        args = (f"{address(c['system_address'])} {topic(c['topic'])} "
                f"{address(c['sender'])} {address(c['recipient'])} (U256.ofNat {c['amount']})")
        text += f'''private def {name}After : Frame := emitTransferLog {name} {args}
#eval IO.println ((Json.mkObj [
  ("id", toJson "{name}"), ("system_address", addressJson {address(c['system_address'])}),
  ("topic", topicJson {topic(c['topic'])}),
  ("sender", addressJson {address(c['sender'])}),
  ("recipient", addressJson {address(c['recipient'])}),
  ("amount", toJson ((U256.ofNat {c['amount']}).toNat)),
  ("before", frameJson {name}), ("after", frameJson {name}After),
  ("retained", frameJson {name})]).compress)
'''
    return text


def byte_array(x, width=None):
    sequence(x)
    for n in x:
        integer(n, 0, 256)
    require(width is None or len(x) == width, "target byte width")
    return bytes(x).hex()


def decode_model(m):
    fields(m, FIELDS)
    out = copy.deepcopy(m)
    for k in ("memory", "return_data"):
        out[k] = byte_array(out[k])
    sequence(out["logs"])
    for log in out["logs"]:
        fields(log, ("address", "topics", "data"))
        log["address"] = byte_array(log["address"], 20)
        sequence(log["topics"])
        log["topics"] = [byte_array(t, 32) for t in log["topics"]]
        log["data"] = byte_array(log["data"])
    for k in ("accounts_to_delete", "accessed_addresses"):
        sequence(out[k])
        out[k] = [byte_array(a, 20) for a in out[k]]
    sequence(out["accessed_storage_keys"])
    slots = []
    for pair in out["accessed_storage_keys"]:
        sequence(pair)
        require(len(pair) == 2, "target slot arity")
        slots.append([byte_array(pair[0], 20), byte_array(pair[1], 32)])
    out["accessed_storage_keys"] = slots
    check_model(out)
    return out


def compare_target(rows, cases):
    require(len(rows) == len(cases), "complete target case count")
    for row, c in zip(rows, cases):
        fields(row, ("id", "system_address", "topic", "sender", "recipient", "amount",
                     "before", "after", "retained"))
        equal(row["id"], c["id"])
        for key, width in [("system_address", 20), ("topic", 32),
                           ("sender", 20), ("recipient", 20)]:
            equal(byte_array(row[key], width), c[key])
        integer(row["amount"], 0, 2**256)
        equal(row["amount"], c["amount"])
        for key, model in [("before", c["before"]), ("after", c["expected_after"]),
                           ("retained", c["before"])]:
            equal(projected(decode_model(row[key])), projected(model))


def parser_controls(rows, cases):
    """Exercise every complete field and meter scalar, order and type boundary."""
    mutants = []
    def mutate(path, value=None, delete=False, index=2):
        m = copy.deepcopy(rows)
        obj = m[index]
        for key in path[:-1]:
            obj = obj[key]
        if delete:
            del obj[path[-1]]
        else:
            obj[path[-1]] = value
        mutants.append(m)
    for part in ("before", "after", "retained"):
        for field in FIELDS:
            mutate([part, field], delete=True)
        for key in METER:
            mutate([part, "gas_meter", key], True)
            mutate([part, "gas_meter", key], delete=True)
        mutate([part, "pc"], float(rows[2][part]["pc"]))
        mutate([part, "pc"], rows[2][part]["pc"] + 1)
        mutate([part, "stack"], list(reversed(rows[2][part]["stack"])))
        mutate([part, "memory", 0], 255 - rows[2][part]["memory"][0])
        mutate([part, "return_data", 0], True)
        mutate([part, "accounts_to_delete"], [])
        mutate([part, "accessed_addresses"], [])
        mutate([part, "accessed_storage_keys", 0],
               list(reversed(rows[2][part]["accessed_storage_keys"][0])))
        mutate([part, "logs"], list(reversed(rows[2][part]["logs"]))[1:])
    # Ordered full-log fields, append position, and each complete new-entry topic.
    logs = rows[2]["after"]["logs"]
    mutate(["after", "logs"], [logs[1], logs[0], *logs[2:]])
    mutate(["after", "logs"], logs + logs[:1])
    index = next(i for i, c in enumerate(cases) if c["amount"] != 0)
    entry = rows[index]["after"]["logs"][-1]
    for j in range(3):
        mutate(["after", "logs", -1, "topics", j, 0],
               255 - entry["topics"][j][0], index=index)
    mutate(["after", "logs", -1, "address", 0],
           255 - entry["address"][0], index=index)
    mutate(["after", "logs", -1, "data", 0], 255 - entry["data"][0], index=index)
    mutate(["after", "logs", -1, "data"], entry["data"][1:], index=index)
    mutate(["after", "logs", -1, "topics"], list(reversed(entry["topics"])), index=index)
    for field in ("system_address", "topic", "sender", "recipient"):
        mutate([field, 0], 255 - rows[2][field][0])
    mutate(["amount"], True)
    mutate(["amount"], float(rows[2]["amount"]))
    mutate(["extra"], 0)
    mutants += [rows[:-1], rows[::-1], rows + rows[:1]]
    for m in mutants:
        try:
            compare_target(m, cases)
        except ValueError:
            continue
        raise ValueError("negative target control accepted")
    return len(mutants)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-catalogue", type=Path, required=True)
    parser.add_argument("--source-output", type=Path, action="append", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    catalogue = read_json(args.source_catalogue, {CATALOGUE_SHA256})
    cases = catalogue_cases(catalogue)
    for path in args.source_output:
        source = read_json(path, SOURCE_SHA256)
        require(source["passed"] is True, "source status")
        require(len(source["observations"]) == 32, "source observations")
        for obs, c in zip(source["observations"], cases[:32]):
            equal(obs["id"], c["id"])
            equal(obs["return"], {"type": "builtins.NoneType", "value": None})
            equal(projected(obs["before_model"]), projected(c["before"]))
            equal(projected(obs["after_model"]), projected(c["expected_after"]))
    args.output_dir.mkdir(parents=True, exist_ok=False)
    target = args.output_dir / "TransferLogTarget.lean"
    target.write_text(producer(cases))
    with (args.output_dir / "target.stdout").open("wb") as out, \
            (args.output_dir / "target.stderr").open("wb") as err:
        command = ["lake", "env", "lean", "-DwarningAsError=true", str(target.resolve())]
        run = subprocess.run(command, stdout=out, stderr=err, check=False)
    (args.output_dir / "target-receipt.json").write_text(json.dumps({
        "argv": command, "exit_code": run.returncode,
        "producer_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
        "stdout_sha256": hashlib.sha256(
            (args.output_dir / "target.stdout").read_bytes()).hexdigest(),
    }, indent=2) + "\n")
    require(run.returncode == 0, "interpreted target failed; see complete stdout/stderr")
    lines = (args.output_dir / "target.stdout").read_text().splitlines()
    rows = [json.loads(line, object_pairs_hook=unique_object) for line in lines]
    compare_target(rows, cases)
    controls = parser_controls(rows, cases)
    print(f"PASS: 32 coherent-source + 8 arbitrary-address/topic complete target cases; "
          f"{len(args.source_output)} authenticated source captures; {controls} negative controls")
    print("Qualified finite semantic projection: stack reversal and three membership adapters; "
          "no literal ordered-JSON, runtime-class, generic-source or whole-Evm claim.")


if __name__ == "__main__":
    main()
