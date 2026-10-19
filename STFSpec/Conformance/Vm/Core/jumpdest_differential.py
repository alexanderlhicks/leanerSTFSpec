# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""One complete-value Jumpdest reader and public-import target emitter.

The manual32 expectations are immutable handwritten evidence. The canonical940
catalog contains inputs only. No reference/dependency oracle or scanner clone is
imported. Source comparisons consume the digest of a frozen preflight binding catalog.
That catalog and the source observations are caller-supplied external evidence;
this reader does not produce or authenticate them.
Reconstructed logical bytes are membership observations, never physical storage.
"""

from pathlib import Path
import argparse
import copy
import datetime
import hashlib
import json
import re
import subprocess
import sys
import tempfile

CATALOG_SHA256 = "f502930e454681563e513ed67e4db7880c7db451476343fda75032c028fa4809"
MANUAL_SHA256 = "71269203c0374574f1466175dcf0127d9e67f798afb3b9b54a6d8f7beda41e03"
MANUAL_CONTROLS_TEXT = (
    "{\n"
    '  "status": "Handwritten complete small-code literals; source/target/model/par'
    'ser unrun",\n'
    '  "date": "2026-10-18",\n'
    '  "pin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",\n'
    '  "observations": "destinations is the complete ascending set, not samples; lo'
    "gical_lsb_bitmap packs public membership with bit i%8 in byte i/8, and does no"
    't prescribe private storage bit order",\n'
    '  "global_target_only_probes": [{"nat_expression": "2^4096", "expected": false'
    "}],\n"
    '  "cases": [\n'
    '    {"id": 1, "name": "empty", "code": [], "destinations": [], "logical_lsb_bi'
    'tmap": [], "probes": [[0,false],[1,false],[8,false]]},\n'
    '    {"id": 2, "name": "single-destination", "code": [91], "destinations": [0],'
    ' "logical_lsb_bitmap": [1], "probes": [[0,true],[1,false],[7,false],[8,false]]'
    "},\n"
    '    {"id": 3, "name": "invalid-0c", "code": [12], "destinations": [], "logical'
    '_lsb_bitmap": [0], "probes": [[0,false],[1,false],[7,false]]},\n'
    '    {"id": 4, "name": "invalid-fe-continues", "code": [254,91], "destinations"'
    ': [1], "logical_lsb_bitmap": [2], "probes": [[0,false],[1,true],[2,false],[7,f'
    "alse]]},\n"
    '    {"id": 5, "name": "two-invalids-continue", "code": [12,254,91], "destinati'
    'ons": [2], "logical_lsb_bitmap": [4], "probes": [[0,false],[1,false],[2,true],'
    "[3,false]]},\n"
    '    {"id": 6, "name": "stop-does-not-end-scan", "code": [0,91], "destinations"'
    ': [1], "logical_lsb_bitmap": [2], "probes": [[0,false],[1,true],[2,false]]},\n'
    '    {"id": 7, "name": "return-revert-selfdestruct-do-not-end-scan", "code": [2'
    '43,91,253,91,255,91], "destinations": [1,3,5], "logical_lsb_bitmap": [42], "pr'
    'obes": [[0,false],[1,true],[3,true],[5,true],[6,false],[7,false]]},\n'
    '    {"id": 8, "name": "push0-has-no-immediate", "code": [95,91], "destinations'
    '": [1], "logical_lsb_bitmap": [2], "probes": [[0,false],[1,true],[2,false]]},\n'
    '    {"id": 9, "name": "push1-hides-destination", "code": [96,91], "destination'
    's": [], "logical_lsb_bitmap": [0], "probes": [[0,false],[1,false],[2,false]]},'
    "\n"
    '    {"id": 10, "name": "push1-resumes", "code": [96,91,91], "destinations": [2'
    '], "logical_lsb_bitmap": [4], "probes": [[0,false],[1,false],[2,true],[3,false'
    "]]},\n"
    '    {"id": 11, "name": "push2-hides-both-bytes", "code": [97,91,91], "destinat'
    'ions": [], "logical_lsb_bitmap": [0], "probes": [[0,false],[1,false],[2,false]'
    ",[3,false]]},\n"
    '    {"id": 12, "name": "push2-resumes", "code": [97,91,91,91], "destinations":'
    ' [3], "logical_lsb_bitmap": [8], "probes": [[1,false],[2,false],[3,true],[4,fa'
    "lse]]},\n"
    '    {"id": 13, "name": "push-opcode-inside-data-is-not-executed", "code": [97,'
    '96,91,91], "destinations": [3], "logical_lsb_bitmap": [8], "probes": [[0,false'
    "],[1,false],[2,false],[3,true],[4,false]]},\n"
    '    {"id": 14, "name": "push32-byte-hidden-by-push1", "code": [96,127,91,91], '
    '"destinations": [2,3], "logical_lsb_bitmap": [12], "probes": [[0,false],[1,fal'
    "se],[2,true],[3,true],[4,false]]},\n"
    '    {"id": 15, "name": "push1-at-end", "code": [96], "destinations": [], "logi'
    'cal_lsb_bitmap": [0], "probes": [[0,false],[1,false],[7,false]]},\n'
    '    {"id": 16, "name": "push2-truncated", "code": [97,91], "destinations": [],'
    ' "logical_lsb_bitmap": [0], "probes": [[0,false],[1,false],[2,false]]},\n'
    '    {"id": 17, "name": "push32-truncated", "code": [127,91,91], "destinations"'
    ': [], "logical_lsb_bitmap": [0], "probes": [[0,false],[1,false],[2,false],[3,f'
    "alse],[32,false]]},\n"
    '    {"id": 18, "name": "destination-before-truncated-push32", "code": [91,127,'
    '91], "destinations": [0], "logical_lsb_bitmap": [1], "probes": [[0,true],[1,fa'
    "lse],[2,false],[3,false]]},\n"
    '    {"id": 19, "name": "dupn-guidance-example", "code": [230,91,96,91,91], "de'
    'stinations": [1,4], "logical_lsb_bitmap": [18], "probes": [[0,false],[1,true],'
    "[2,false],[3,false],[4,true],[5,false]]},\n"
    '    {"id": 20, "name": "swapn-guidance-companion", "code": [231,91,96,91,91], '
    '"destinations": [1,4], "logical_lsb_bitmap": [18], "probes": [[0,false],[1,tru'
    "e],[3,false],[4,true],[5,false]]},\n"
    '    {"id": 21, "name": "exchange-guidance-companion", "code": [232,91,96,91,91'
    '], "destinations": [1,4], "logical_lsb_bitmap": [18], "probes": [[0,false],[1,'
    "true],[3,false],[4,true],[5,false]]},\n"
    '    {"id": 22, "name": "three-extended-ops-do-not-skip", "code": [230,91,231,9'
    '1,232,91], "destinations": [1,3,5], "logical_lsb_bitmap": [42], "probes": [[0,'
    "false],[1,true],[2,false],[3,true],[4,false],[5,true],[6,false]]},\n"
    '    {"id": 23, "name": "dupn-byte-inside-push-data", "code": [96,230,91], "des'
    'tinations": [2], "logical_lsb_bitmap": [4], "probes": [[0,false],[1,false],[2,'
    "true],[3,false]]},\n"
    '    {"id": 24, "name": "jump-and-jumpi-do-not-redirect-scan", "code": [86,91,8'
    '7,91], "destinations": [1,3], "logical_lsb_bitmap": [10], "probes": [[0,false]'
    ",[1,true],[2,false],[3,true],[4,false]]},\n"
    '    {"id": 25, "name": "bitmap-7-8-15-16-boundaries", "code": [0,0,0,0,0,0,0,9'
    '1,91,0,0,0,0,0,0,91,91], "destinations": [7,8,15,16], "logical_lsb_bitmap": [1'
    '28,129,1], "probes": [[6,false],[7,true],[8,true],[9,false],[14,false],[15,tru'
    "e],[16,true],[17,false],[23,false],[24,false]]},\n"
    '    {"id": 26, "name": "nine-consecutive-destinations", "code": [91,91,91,91,9'
    '1,91,91,91,91], "destinations": [0,1,2,3,4,5,6,7,8], "logical_lsb_bitmap": [25'
    '5,1], "probes": [[0,true],[7,true],[8,true],[9,false],[15,false],[16,false]]},'
    "\n"
    '    {"id": 27, "name": "only-final-bit-of-nine", "code": [0,0,0,0,0,0,0,0,91],'
    ' "destinations": [8], "logical_lsb_bitmap": [0,1], "probes": [[0,false],[7,fal'
    "se],[8,true],[9,false],[15,false],[16,false]]},\n"
    '    {"id": 28, "name": "valid-nonpush-nondestinations", "code": [0,1,86,87,95,'
    '230,231,232,243,253,255], "destinations": [], "logical_lsb_bitmap": [0,0], "pr'
    'obes": [[0,false],[7,false],[8,false],[10,false],[11,false],[15,false],[16,fal'
    "se]]},\n"
    '    {"id": 29, "name": "full-push32-then-destination", "code": [127,\n'
    "      91,91,91,91,91,91,91,91,\n"
    "      91,91,91,91,91,91,91,91,\n"
    "      91,91,91,91,91,91,91,91,\n"
    "      91,91,91,91,91,91,91,91,\n"
    '      91], "destinations": [33], "logical_lsb_bitmap": [0,0,0,0,2], "probes": '
    "[[0,false],[1,false],[31,false],[32,false],[33,true],[34,false],[39,false],[40"
    ",false]]},\n"
    '    {"id": 30, "name": "two-push1s-then-destination", "code": [96,91,96,91,91]'
    ', "destinations": [4], "logical_lsb_bitmap": [16], "probes": [[0,false],[1,fal'
    "se],[2,false],[3,false],[4,true],[5,false]]},\n"
    '    {"id": 31, "name": "interleaved-destinations-and-pushes", "code": [91,96,9'
    '1,91,97,91,91,91], "destinations": [0,3,7], "logical_lsb_bitmap": [137], "prob'
    'es": [[0,true],[1,false],[2,false],[3,true],[4,false],[5,false],[6,false],[7,t'
    "rue],[8,false]]},\n"
    '    {"id": 32, "name": "invalid-extended-push0-and-hidden-data", "code": [254,'
    '230,91,96,91,231,91,95,91,232,91], "destinations": [2,6,8,10], "logical_lsb_bi'
    'tmap": [68,5], "probes": [[0,false],[1,false],[2,true],[3,false],[4,false],[5,'
    "false],[6,true],[7,false],[8,true],[9,false],[10,true],[11,false],[15,false],["
    "16,false]]}\n"
    "  ]\n"
    "}\n"
)


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def bad_constant(value):
    raise FrameError("nonfinite JSON constant: " + value)


def load_json(data):
    return json.loads(
        data.decode("utf-8"), object_pairs_hook=pairs, parse_constant=bad_constant
    )


def fields(value, keys, label):
    require(type(value) is dict and set(value) == set(keys), label + " fields/type")


def natural(value):
    require(type(value) is int and value >= 0, "expected actual nonnegative int")
    return value


def decimal(value):
    require(
        type(value) is str and re.fullmatch(r"0|[1-9][0-9]*", value) is not None,
        "expected canonical decimal string",
    )
    return int(value)


def byte_value(value):
    fields(value, ["size", "hex"], "byte value")
    size = natural(value["size"])
    text = value["hex"]
    require(
        type(text) is str
        and len(text) == 2 * size
        and re.fullmatch(r"[0-9a-f]*", text) is not None,
        "complete lowercase bytes",
    )
    return bytes.fromhex(text)


def metadata(value):
    if type(value) is dict:
        for key, item in value.items():
            require(type(key) is str, "metadata key")
            metadata(item)
    elif type(value) is list:
        for item in value:
            metadata(item)
    elif type(value) is int:
        natural(value)
    else:
        require(type(value) in [str, bool] or value is None, "metadata scalar")


def same_metadata(value, expected):
    require(type(value) is type(expected), "metadata exact scalar/container type")
    if type(expected) is dict:
        require(set(value) == set(expected), "metadata exact fields")
        for key in expected:
            same_metadata(value[key], expected[key])
    elif type(expected) is list:
        require(len(value) == len(expected), "metadata exact length")
        for item, wanted in zip(value, expected):
            same_metadata(item, wanted)
    else:
        require(value == expected, "metadata exact value")


def manual_controls():
    require(
        hashlib.sha256(MANUAL_CONTROLS_TEXT.encode()).hexdigest() == MANUAL_SHA256,
        "immutable manual controls changed",
    )
    return load_json(MANUAL_CONTROLS_TEXT.encode())["cases"]


def manual_inputs():
    # Only input transliteration; no scanner or expected destination calculation.
    return [
        dict(
            id=row["id"],
            family="L",
            parameters={"literalId": row["id"]},
            name=row["name"],
            code={"size": len(row["code"]), "hex": bytes(row["code"]).hex()},
            probes=[str(index) for index, _ in row["probes"]] + [str(2**4096)],
        )
        for row in manual_controls()
    ]


def load_cases(path=None, focused=False):
    if path is None:
        require(focused, "full940 operations require the canonical catalog")
        return manual_inputs()
    data = Path(path).read_bytes()
    require(hashlib.sha256(data).hexdigest() == CATALOG_SHA256, "canonical940 catalog identity")
    catalog = load_json(data)
    fields(catalog, ["schema", "pin", "count", "familyCounts", "cases"], "catalog")
    require(
        catalog["schema"] == "jumpdest-inputs-v1" and natural(catalog["count"]) == 940,
        "catalog schema/count",
    )
    require(catalog["pin"] == "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36", "catalog pin")
    require(
        catalog["familyCounts"] == {"L": 32, "H": 256, "P": 592, "B": 24, "R": 32, "W": 4},
        "catalog family counts",
    )
    rows = catalog["cases"]
    require(type(rows) is list and len(rows) == 940, "catalog complete rows")
    for index, row in enumerate(rows, 1):
        fields(row, ["id", "family", "parameters", "name", "code", "probes"], "case")
        require(
            natural(row["id"]) == index
            and row["family"] in "LHPBRW"
            and type(row["family"]) is str
            and len(row["family"]) == 1,
            "case ID/family",
        )
        require(type(row["name"]) is str and type(row["parameters"]) is dict, "case metadata")
        metadata(row["parameters"])
        byte_value(row["code"])
        require(type(row["probes"]) is list, "probe input list")
        for probe in row["probes"]:
            decimal(probe)
    require(rows[:32] == manual_inputs(), "canonical original32 input agreement")
    return rows[:32] if focused else rows


def frame_rows(data, count):
    require(type(data) is bytes and data.endswith(b"\n"), "missing final LF")
    require(b"\r" not in data and not data.startswith(b"\xef\xbb\xbf"), "CR/BOM framing")
    lines = data[:-1].split(b"\n")
    require(len(lines) == count, "complete frame count")
    result = []
    for line in lines:
        require(line.startswith(b"{") and line.endswith(b"}"), "noncanonical line framing")
        row = load_json(line)
        require(type(row) is dict, "row object")
        result.append(row)
    return result


def identity(row, case, target):
    require(natural(row["id"]) == case["id"], "ID/order")
    require(type(row["family"]) is str and row["family"] == case["family"], "family")
    metadata(row["parameters"])
    same_metadata(row["parameters"], case["parameters"])
    if target:
        require(type(row["name"]) is str and row["name"] == case["name"], "name")
    fields(row["input"], ["code"], "input")
    byte_value(row["input"]["code"])
    require(row["input"]["code"] == case["code"], "complete input code")


def destinations(value, cardinality, size):
    require(type(value) is list, "destination list")
    previous = -1
    for index in value:
        natural(index)
        require(previous < index < size, "sorted unique in-code destinations")
        previous = index
    require(natural(cardinality) == len(value), "complete cardinality")
    return set(value)


def observation(row, case):
    fields(
        row,
        ["code", "logical", "memberships", "destinations", "cardinality", "probes"],
        "observation",
    )
    byte_value(row["code"])
    require(row["code"] == case["code"], "snapshot code identity")
    size = case["code"]["size"]
    width = (size + 7) // 8
    members = row["memberships"]
    require(
        type(members) is list
        and len(members) == 8 * width
        and all(type(bit) is bool for bit in members),
        "all membership/padding bits",
    )
    require(not any(members[size:]), "true padding bit")
    marked = destinations(row["destinations"], row["cardinality"], size)
    require(
        row["destinations"] == [i for i, bit in enumerate(members[:size]) if bit],
        "complete set/membership agreement",
    )
    actual_logical = byte_value(row["logical"])
    expected_logical = bytes(
        sum((1 << k) for k in range(8) if members[8 * j + k]) for j in range(width)
    )
    require(actual_logical == expected_logical, "complete logical bytes")
    require(
        type(row["probes"]) is list and len(row["probes"]) == len(case["probes"]),
        "complete ordered probes",
    )
    for probe, expected_index in zip(row["probes"], case["probes"]):
        fields(probe, ["index", "contains"], "probe")
        index = decimal(probe["index"])
        require(
            probe["index"] == expected_index and type(probe["contains"]) is bool,
            "probe index/order/type",
        )
        require(probe["contains"] == (index in marked), "probe/set agreement")
    return marked


def target_rows(data, cases):
    rows = frame_rows(data, len(cases))
    for position, (row, case) in enumerate(zip(rows, cases)):
        fields(
            row,
            [
                "schema",
                "id",
                "family",
                "parameters",
                "name",
                "input",
                "before",
                "distractor",
                "after",
            ],
            "target row",
        )
        require(row["schema"] == "jumpdest-target-v1", "target schema")
        identity(row, case, True)
        observation(row["before"], case)
        observation(row["after"], case)
        require(row["before"] == row["after"], "retained held-map snapshot")
        other = cases[(position + 1) % len(cases)]
        fields(row["distractor"], ["id", "observation"], "distractor")
        require(natural(row["distractor"]["id"]) == other["id"], "distractor order")
        observation(row["distractor"]["observation"], other)
    for position, row in enumerate(rows):
        require(
            row["distractor"]["observation"] == rows[(position + 1) % len(rows)]["before"],
            "complete distractor/next-map agreement",
        )
    return rows


def source_rows(data, cases, binding_digest):
    require(
        type(binding_digest) is str and re.fullmatch(r"[0-9a-f]{64}", binding_digest),
        "frozen preflight catalog binding digest required",
    )
    rows = frame_rows(data, len(cases))
    for row, case in zip(rows, cases):
        fields(
            row,
            ["schema", "id", "family", "parameters", "input", "output", "classes", "adapters"],
            "source row",
        )
        require(row["schema"] == "jumpdest-source-v1", "source schema")
        identity(row, case, False)
        fields(row["output"], ["destinations", "cardinality", "after"], "source output")
        output = row["output"]
        destinations(output["destinations"], output["cardinality"], case["code"]["size"])
        fields(output["after"], ["code"], "source after")
        byte_value(output["after"]["code"])
        require(output["after"]["code"] == case["code"], "source full unchanged input")
        fields(row["classes"], ["input", "result", "elements", "bindingDigest"], "classes")
        require(
            row["classes"]
            == {
                "input": "builtins.bytes",
                "result": "builtins.set",
                "elements": "ethereum_types.numeric.Uint",
                "bindingDigest": binding_digest,
            },
            "authenticated source classes/binding digest",
        )
        fields(
            row["adapters"],
            ["directScannerCalls", "uniqueMemberObservations", "uintToIntConversions"],
            "adapters",
        )
        require(natural(row["adapters"]["directScannerCalls"]) == 1, "direct call count")
        require(
            natural(row["adapters"]["uniqueMemberObservations"]) == output["cardinality"]
            and natural(row["adapters"]["uintToIntConversions"]) == output["cardinality"],
            "actual observation/conversion counts",
        )
    return rows


def compare(data, cases, source=None, binding_digest=None, other=None):
    actual = target_rows(data, cases)
    manual = {row["id"]: row for row in manual_controls()}
    for row in actual:
        if row["family"] == "L":
            expected = manual[row["id"]]
            require(
                row["before"]["destinations"] == expected["destinations"]
                and bytes.fromhex(row["before"]["logical"]["hex"])
                == bytes(expected["logical_lsb_bitmap"]),
                "complete handwritten32 literal",
            )
    if other is not None:
        require(actual == target_rows(other, cases), "complete interpreted/native agreement")
    if source is not None:
        original = source_rows(source, cases, binding_digest)
        for position, row in enumerate(actual):
            require(
                row["before"]["destinations"] == original[position]["output"]["destinations"],
                "complete retained source destination set",
            )
            require(
                row["distractor"]["observation"]["destinations"]
                == original[(position + 1) % len(cases)]["output"]["destinations"],
                "complete retained source distractor set",
            )
    return {
        "complete_rows": len(actual),
        "complete_snapshots": 3 * len(actual),
        "manual_rows": sum(row["family"] == "L" for row in actual),
        "compared_source_rows": len(actual) if source is not None else 0,
        "compared_other_target": other is not None,
    }


def lean_string(value):
    return json.dumps(value, ensure_ascii=False)


def lean_json(value):
    if type(value) is dict:
        return (
            "Json.mkObj ["
            + ", ".join(
                "(" + lean_string(key) + ", " + lean_json(item) + ")"
                for key, item in value.items()
            )
            + "]"
        )
    if type(value) is list:
        return "toJson ([" + ", ".join(lean_json(item) for item in value) + "] : List Json)"
    if type(value) is str:
        return "toJson " + lean_string(value)
    if type(value) is bool:
        return "toJson " + str(value).lower()
    if type(value) is int:
        return "toJson (" + str(value) + " : Nat)"
    require(value is None, "Lean metadata value")
    return "Json.null"


PRODUCER_HEADER = r"""import STFSpec.Vm.Core
import Lean
open STFSpec.Vm.Core STFSpec.Base Lean

set_option maxRecDepth 4096

private def hexDigit (b : UInt8) : Nat :=
  if b.toNat < 58 then b.toNat - 48 else b.toNat - 87

private def decodeHex (s : String) : Bytes :=
  let text := s.toUTF8
  Bytes.generate (text.size / 2) fun i ↦
    if h : 2 * i + 1 < text.size then
      UInt8.ofNat (16 * hexDigit (text[2 * i]'(by omega)) + hexDigit (text[2 * i + 1]))
    else 0

private def byteHex (b : UInt8) : String :=
  let digit := fun n ↦ if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]

private def fullBytes (b : Bytes) : Json :=
  Json.mkObj [("size", toJson b.size), ("hex", toJson (String.join (b.toList.map byteHex)))]

private structure Case where
  id : Nat
  family : String
  parameters : Json
  name : String
  codeHex : String
  probes : List Nat

private def observe (c : Bytes) (m : JumpdestMap) (probes : List Nat) : Json :=
  let width := (c.size + 7) / 8
  let memberships := (List.range (8 * width)).map m.contains
  let marked := (List.range c.size).filter m.contains
  let logical := (List.range width).map fun j ↦
    UInt8.ofNat (((List.range 8).map fun k ↦
      if m.contains (j * 8 + k) then 2 ^ k else 0).sum)
  Json.mkObj [("code", fullBytes c), ("logical", fullBytes (Bytes.ofList logical)),
    ("memberships", toJson memberships), ("destinations", toJson marked),
    ("cardinality", toJson marked.length), ("probes", toJson (probes.map fun i ↦
      Json.mkObj [("index", toJson (toString i)), ("contains", toJson (m.contains i))]))]

"""


PRODUCER_MAIN = r"""
def main : IO Unit := do
  let rows := cases.toList
  for (row, next) in rows.zip (rows.drop 1 ++ rows.take 1) do
    let code := decodeHex row.codeHex
    let held := validJumpDestinations code
    let before := observe code held row.probes
    let otherCode := decodeHex next.codeHex
    let other := validJumpDestinations otherCode
    let distractor := observe otherCode other next.probes
    let after := observe code held row.probes
    IO.println ((Json.mkObj [("schema", toJson "jumpdest-target-v1"),
      ("id", toJson row.id), ("family", toJson row.family), ("parameters", row.parameters),
      ("name", toJson row.name), ("input", Json.mkObj [("code", fullBytes code)]),
      ("before", before), ("distractor", Json.mkObj [("id", toJson next.id),
        ("observation", distractor)]), ("after", after)]).compress)
"""


def emit_target(cases, path):
    # Only input encoding is emitted. No expected destinations or scanner exists here.
    unique = list(dict.fromkeys(probe for row in cases for probe in row["probes"]))
    symbols = {probe: "probe" + str(i) for i, probe in enumerate(unique)}
    text = PRODUCER_HEADER
    for probe, symbol in symbols.items():
        text += "@[noinline] private def " + symbol + " : Nat := " + probe + "\n"
    chunks = []
    for start in range(0, len(cases), 32):
        symbol = "casesChunk" + str(len(chunks))
        chunks.append(symbol)
        text += "\n@[noinline] private def " + symbol + " : Array Case := #[\n"
        for row in cases[start : start + 32]:
            text += "  { id := " + str(row["id"]) + ", family := " + lean_string(row["family"])
            text += ", parameters := " + lean_json(row["parameters"])
            text += ", name := " + lean_string(row["name"]) + ", codeHex := "
            text += lean_string(row["code"]["hex"]) + ", probes := ["
            text += ", ".join(symbols[probe] for probe in row["probes"]) + "] },\n"
        text += "]\n"
    text += "\nprivate def cases : Array Case :=\n"
    text += "  ([" + ", ".join(chunks) + "] : List (Array Case)).foldl Array.append #[]\n"
    text += PRODUCER_MAIN
    Path(path).write_text(text, encoding="utf-8")
    return {
        "emitted_cases": len(cases),
        "producer_sha256": hashlib.sha256(text.encode()).hexdigest(),
    }


def serialized(rows):
    return ("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows)).encode()


def self_test(directory=None):
    # Synthetic wire fixtures from manual complete sets; no source/target execution.
    cases = manual_inputs()
    literals = {row["id"]: row for row in manual_controls()}

    def fixture(case):
        size = case["code"]["size"]
        marked = set(literals[case["id"]]["destinations"])
        width = (size + 7) // 8
        return {
            "code": case["code"],
            "logical": {
                "size": width,
                "hex": bytes(literals[case["id"]]["logical_lsb_bitmap"]).hex(),
            },
            "memberships": [i in marked for i in range(8 * width)],
            "destinations": sorted(marked),
            "cardinality": len(marked),
            "probes": [{"index": i, "contains": int(i) in marked} for i in case["probes"]],
        }

    targets = []
    sources = []
    digest = "0" * 64  # Deliberately synthetic fixture marker, never actual preflight evidence.
    for i, case in enumerate(cases):
        next_case = cases[(i + 1) % len(cases)]
        value = fixture(case)
        targets.append(
            dict(
                schema="jumpdest-target-v1",
                id=case["id"],
                family="L",
                parameters=case["parameters"],
                name=case["name"],
                input={"code": case["code"]},
                before=value,
                distractor={"id": next_case["id"], "observation": fixture(next_case)},
                after=copy.deepcopy(value),
            )
        )
        sources.append(
            dict(
                schema="jumpdest-source-v1",
                id=case["id"],
                family="L",
                parameters=case["parameters"],
                input={"code": case["code"]},
                output={
                    "destinations": value["destinations"],
                    "cardinality": value["cardinality"],
                    "after": {"code": case["code"]},
                },
                classes={
                    "input": "builtins.bytes",
                    "result": "builtins.set",
                    "elements": "ethereum_types.numeric.Uint",
                    "bindingDigest": digest,
                },
                adapters={
                    "directScannerCalls": 1,
                    "uniqueMemberObservations": value["cardinality"],
                    "uintToIntConversions": value["cardinality"],
                },
            )
        )
    valid = serialized(targets)
    original = serialized(sources)
    compare(valid, cases, original, digest, valid)
    rejected = []

    def reject(label, target=valid, source=original):
        try:
            compare(target, cases, source, digest)
        except (FrameError, ValueError, UnicodeError, TypeError):
            rejected.append(label)
        else:
            raise FrameError("accepted corruption: " + label)

    def changed(label, edit, source=False):
        rows = copy.deepcopy(sources if source else targets)
        edit(rows)
        reject(label, source=serialized(rows)) if source else reject(label, serialized(rows))

    changed("boolean ID", lambda rows: rows[0].update(id=True))
    changed(
        "boolean metadata integer", lambda rows: rows[0]["parameters"].update(literalId=True)
    )
    changed("float size", lambda rows: rows[1]["input"]["code"].update(size=1.0))
    changed("middle code", lambda rows: rows[18]["input"]["code"].update(hex="00" * 5))
    changed("extra target field", lambda rows: rows[0].update(extra=0))
    changed("missing snapshot field", lambda rows: rows[0]["before"].pop("probes"))
    changed(
        "same-length middle bitmap",
        lambda rows: rows[24]["before"]["logical"].update(hex="808001"),
    )
    changed("true padding", lambda rows: rows[1]["before"]["memberships"].__setitem__(7, True))
    changed("probe bool alias", lambda rows: rows[1]["before"]["probes"][0].update(contains=1))
    changed(
        "noncanonical probe", lambda rows: rows[1]["before"]["probes"][0].update(index="00")
    )
    changed("retained snapshot changed", lambda rows: rows[1]["after"]["destinations"].clear())
    changed("distractor changed", lambda rows: rows[0]["distractor"].update(id=3))
    changed(
        "source float element", lambda rows: rows[1]["output"].update(destinations=[0.0]), True
    )
    changed(
        "source duplicate set", lambda rows: rows[1]["output"].update(destinations=[0, 0]), True
    )
    changed(
        "source incomplete set", lambda rows: rows[18]["output"]["destinations"].pop(), True
    )
    changed(
        "source alternative class",
        lambda rows: rows[1]["classes"].update(elements="builtins.int"),
        True,
    )
    changed(
        "source binding changed",
        lambda rows: rows[1]["classes"].update(bindingDigest="1" * 64),
        True,
    )
    changed(
        "source calls bool",
        lambda rows: rows[0]["adapters"].update(directScannerCalls=True),
        True,
    )
    changed(
        "source input mutation",
        lambda rows: rows[1]["output"]["after"]["code"].update(hex="00"),
        True,
    )
    reject("missing row", serialized(targets[:-1]))
    reject("extra row", serialized(targets + targets[-1:]))
    reject("reordered rows", serialized(targets[:1] + [targets[2], targets[1]] + targets[3:]))
    reject("duplicate key", valid.replace(b'"id":1', b'"id":1,"id":1', 1))
    reject("nonfinite", valid.replace(b'"id":1', b'"id":NaN', 1))
    framing = [
        ("CRLF", valid.replace(b"\n", b"\r\n", 1)),
        ("missing LF", valid[:-1]),
        ("blank line", valid + b"\n"),
        ("BOM", b"\xef\xbb\xbf" + valid),
        ("invalid UTF8", b"\xff" + valid),
        ("trailing bytes", valid + b"x"),
    ]
    for label, data in framing:
        reject(label, data)
    temporary = (
        tempfile.TemporaryDirectory(prefix="jumpdest-parser-") if directory is None else None
    )
    root = Path(temporary.name if temporary else directory)
    root.mkdir(parents=True, exist_ok=True)
    source_path = root / "synthetic-source.jsonl"
    source_path.write_bytes(original)
    outcomes = []
    for label, data in [("LF-positive", valid)] + framing:
        dest = root / label.replace(" ", "-")
        dest.mkdir(exist_ok=False)
        target_path = dest / "input.jsonl"
        target_path.write_bytes(data)
        argv = [sys.executable, "-B"] + (["-O"] if sys.flags.optimize else [])
        argv += [
            str(Path(__file__).resolve()),
            "--focused32",
            "--compare",
            str(target_path),
            "--source",
            str(source_path),
            "--binding-digest",
            digest,
        ]
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        result = subprocess.run(argv, input=b"", capture_output=True)
        (dest / "stdin").write_bytes(b"")
        (dest / "stdout").write_bytes(result.stdout)
        (dest / "stderr").write_bytes(result.stderr)
        (dest / "command.json").write_text(
            json.dumps(
                {
                    "argv": argv,
                    "cwd": str(Path.cwd()),
                    "start_utc": start,
                    "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "exit_code": result.returncode,
                    "synthetic_fixture_only": True,
                },
                indent=2,
            )
            + "\n"
        )
        if label == "LF-positive":
            require(result.returncode == 0 and not result.stderr, "positive actual CLI")
        else:
            require(
                result.returncode != 0 and not result.stdout, "negative actual CLI: " + label
            )
        outcomes.append({"control": label, "exit_code": result.returncode})
    if temporary:
        temporary.cleanup()
    return {
        "fixture": "synthetic complete handwritten32; no source or target execution",
        "positive_full_comparisons": 1,
        "rejected_controls": rejected,
        "actual_cli": outcomes,
        "optimization": sys.flags.optimize,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--emit-target", metavar="PATH")
    action.add_argument("--compare", metavar="TARGET")
    action.add_argument("--self-test-parser", action="store_true")
    parser.add_argument("--catalog")
    parser.add_argument("--focused32", action="store_true")
    parser.add_argument("--source")
    parser.add_argument(
        "--binding-digest", help="SHA256 of the frozen preflight binding catalog"
    )
    parser.add_argument("--other-target")
    parser.add_argument("--cli-evidence")
    args = parser.parse_args()
    if args.self_test_parser:
        result = self_test(args.cli_evidence)
    else:
        cases = load_cases(args.catalog, args.focused32)
        if args.emit_target:
            require(not args.source and not args.other_target, "emit accepts inputs only")
            result = emit_target(cases, args.emit_target)
        else:
            result = compare(
                Path(args.compare).read_bytes(),
                cases,
                Path(args.source).read_bytes() if args.source else None,
                args.binding_digest,
                Path(args.other_target).read_bytes() if args.other_target else None,
            )
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (FrameError, ValueError, UnicodeError, TypeError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(2)
