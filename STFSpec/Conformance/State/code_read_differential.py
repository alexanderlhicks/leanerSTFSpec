#!/usr/bin/env python3
"""Check complete code-read observations against the input-only catalogue."""

import argparse
import hashlib
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE / "code_read_inputs.json"
INPUT_SHA256 = "b913946a60edf6dd4a68006d5681eaad7f14ec9fab9e18f3d14c3e98c4b67fdb"
PINNED_EMPTY = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
MAX_WORD = 2**256 - 1


def load_source(name):
    """Load a local conformance helper directly, including under python -I."""
    path = HERE / (name + ".py")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    return module


reader = load_source("account_optional_differential")
AdmissionError = reader.AdmissionError
decode = reader.decode
strict_equal = reader.strict_equal


def recipes():
    data = INPUT.read_bytes()
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise AdmissionError("code-read input identity mismatch")
    rows = decode(data)
    if len(rows) != 85 or len({r["id"] for r in rows}) != 85:
        raise AdmissionError("wrong code-read catalogue size")
    coherent = [r for r in rows if r["sourceComparable"]]
    if len(coherent) != 68 or any(r["emptyCodeHash"] != PINNED_EMPTY for r in coherent):
        raise AdmissionError("wrong coherent source cases")
    return rows


def code_map(entries):
    return {int(h, 16): list(bytes.fromhex(data)) for h, data in entries}


def witness_error(recipe):
    tag, value = next(iter(recipe["providerError"].items()))
    if isinstance(value, dict):
        item, digest = next(iter(value.items()))
        return {tag: {item: int(digest, 16)}}
    return {tag: value if value == "leaf" else int(value, 16)}


def retained_frame(recipe):
    def fields(salt, entries):
        return {
            "account_reads": [salt, salt + 4],
            "account_writes": [[salt, None], [salt + 1, [2**80 + salt, MAX_WORD, salt + 2]]],
            "storage_reads": [[salt, 17], [salt + 1, 19]],
            "storage_writes": [[salt, []], [salt + 1, [[17, 0], [19, MAX_WORD]]]],
            "storage_clears": [salt, salt + 3],
            "code_writes": sorted([h, data] for h, data in code_map(entries).items()),
        }
    block = fields(31, recipe["block"])
    block.update(code_reads=[41, 43], oldest_ancestor_offset=2**420 + 3)
    tx = fields(61, recipe["tx"])
    tx.update(created_accounts=[71, 75],
              transient_storage=[[62, 17, 0], [63, 19, MAX_WORD]])
    return {"block": block, "tx": tx}


def lean_frame(recipe):
    def order(first, second, salt):
        return {"next": 2**410 + salt,
                "positions": [[first, 7 + salt], [second, 91 + salt]],
                "keysByPosition": [[9 + salt, second], [71 + salt, second]]}

    def orders(salt):
        empty = {"next": 0, "positions": [], "keysByPosition": []}
        return [order(salt, salt + 1, salt), order(salt + 1, salt + 2, salt + 1),
                [[salt, empty], [salt + 2, order(17, 19, salt)]]]

    provider = code_map(recipe["provider"])
    probe_hashes = sorted(provider) + [int(recipe["hash"], 16), 101]
    code_results = [[h, [{"ok": provider[h]} if h in provider else
                         {"error": witness_error(recipe)}, [[0, h]]]] for h in probe_hashes]
    root_size = len(recipe["block"])
    return {"consts": [int(recipe["emptyCodeHash"], 16), 11, 12, 13],
            "blockOrders": orders(31), "txOrders": orders(61),
            "provider": {"account": [{"ok": [2**80 + 19, 17, 62]}, [[1, 19]]],
                         "storage": [{"ok": 52}, [[2, 23, 29]]],
                         "code": code_results, "root": [{"ok": 73 + root_size}, [[3, root_size]]]}}


def expected(recipe, *, source=False):
    frame = retained_frame(recipe)
    h = int(recipe["hash"], 16)
    layers = [code_map(recipe[layer]) for layer in ("tx", "block", "provider")]
    reserved = h == int(recipe["emptyCodeHash"], 16)
    provider_call = not reserved and all(h not in layer for layer in layers[:2])
    calls = [[0, h]] if provider_call else []
    old = {int(value, 16) for value in recipe["old_reads"]}
    reads = sorted(old | ({h} if provider_call else set()))
    answer = [] if reserved else next((layer[h] for layer in layers if h in layer), None)
    row = {"id": recipe["id"], "frameBefore": frame}
    if not source:
        row["leanBefore"] = lean_frame(recipe)
    if answer is None:
        outcome = {"error": {"keyError": h}} if source else {"error": {"witness": witness_error(recipe)}}
    else:
        outcome = {"ok": answer}
    step = {"answer": outcome, "calls": calls, "reads": reads if answer is not None else None,
            "frame": frame if source or answer is not None else None}
    if source:
        step.update(failedSourceReads=reads if answer is None else None,
                    providerObservedReads=[True] if provider_call else [],
                    providerObservedAddCounts=[1] if provider_call else [],
                    readAdds=[h] if provider_call else [])
        row["providerCode"] = sorted([k, v] for k, v in layers[2].items())
    else:
        step["lean"] = row["leanBefore"] if answer is not None else None
    row["attempts"] = [step.copy() for _ in range(recipe["repeat"])]
    return row


def parse_stream(data, *, source=False):
    if type(data) is not bytes or len(data) > 2**22 or not data.endswith(b"\n"):
        raise AdmissionError("invalid, oversized or unterminated JSON Lines stream")
    lines = data[:-1].split(b"\n")
    cases = [r for r in recipes() if not source or r["sourceComparable"]]
    if len(lines) != len(cases):
        raise AdmissionError("wrong observation count")
    rows = [decode(line) for line in lines]
    for actual, recipe in zip(rows, cases, strict=True):
        strict_equal(actual, expected(recipe, source=source), recipe["id"])
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    rows = parse_stream(args.check_target.read_bytes())
    print(f"PASS code reads: {len(rows)} complete observations")


if __name__ == "__main__":
    main()
