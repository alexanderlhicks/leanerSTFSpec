#!/usr/bin/env python3
"""Strict complete Taylor frames with independent literal controls.

The committed reader has no source loader or expected recurrence. Source frames
and their authenticated binding digest are supplied by the caller.
"""

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

# One frozen input schedule, transcribed with full independent handwritten results.
# Columns: id, factor, numerator, denominator, complete expected result.
CASES = (
    ("T01", 0, 7, 3, 0),
    ("T02", 5, 0, 3, 5),
    ("T03", 1, 0, 1, 1),
    ("T04", 1, 1, 1, 2),
    ("T05", 1, 2, 1, 6),
    ("T06", 2, 1, 2, 3),
    ("T07", 1, 3, 2, 4),
    ("T08", 3, 2, 3, 5),
    ("T09", 0, 0, 1, 0),
    ("T10", 0, 1, 11684671, 0),
    ("T11", 1, 1, 2, 1),
    ("T12", 1, 2, 3, 1),
    ("T13", 7, 1, 3, 9),
    ("T14", 9, 4, 3, 33),
    ("T15", 1, 3, 1, 16),
    ("T16", 2, 5, 2, 23),
    ("T17", 1, 8, 3, 12),
    ("T18", 18446744073709551615, 0, 1, 18446744073709551615),
    ("T19", 18446744073709551616, 1, 18446744073709551617, 18446744073709551616),
    ("T20", 340282366920938463463374607431768211456, 1,
     340282366920938463463374607431768211457, 340282366920938463463374607431768211456),
    ("T21", 115792089237316195423570985008687907853269984665640564039457584007913129639935,
     1, 115792089237316195423570985008687907853269984665640564039457584007913129639936,
     115792089237316195423570985008687907853269984665640564039457584007913129639935),
    ("T22", 1, 0, 11684671, 1),
    ("T23", 1, 1, 11684671, 1),
    ("T24", 1, 11684670, 11684671, 2),
    ("T25", 1, 11684671, 11684671, 2),
    ("T26", 1, 11684672, 11684671, 2),
    ("T27", 1, 23369342, 11684671, 7),
    ("T28", 7, 23369343, 11684671, 51),
)


def binding_digest(value):
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("a lowercase 64-hex source binding digest is required")
    return value


def expected_frames(kind, digest=None):
    """Construct literal wire fixtures, never calculate a Taylor result."""
    if kind not in ("source", "target"):
        raise ValueError("unknown frame domain")
    if kind == "source":
        binding_digest(digest)
    typename = "Lean.Nat" if kind == "target" else "ethereum_types.numeric.Uint"
    fields = {name: typename for name in ("factor", "numerator", "denominator")}
    frames = []
    for case_id, factor, numerator, denominator, result in CASES:
        inputs = {"factor": factor, "numerator": numerator, "denominator": denominator}
        classes = {"input": fields.copy(), "output": typename, "after": fields.copy()}
        if kind == "source":
            classes["bindingDigest"] = digest
        frames.append({"schema": f"taylor-{kind}-v1", "id": case_id,
                       "domain": f"typed-{kind}", "operation": "taylor_exponential",
                       "input": inputs, "output": {"kind": "success", "result": result,
                                                    "after": inputs.copy()}, "classes": classes})
    return frames


def strict_equal(actual, expected, path):
    # Exact type checks precede equality: bool is an int subclass in Python.
    if type(actual) is not type(expected):
        raise ValueError(f"{path}: wrong type {type(actual).__name__}")
    if type(expected) is dict:
        if actual.keys() != expected.keys():
            raise ValueError(f"{path}: missing or extra keys")
        for key in expected:
            strict_equal(actual[key], expected[key], f"{path}.{key}")
    elif type(expected) is list:
        if len(actual) != len(expected):
            raise ValueError(f"{path}: wrong count")
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            strict_equal(left, right, f"{path}[{index}]")
    elif actual != expected:
        raise ValueError(f"{path}: complete value mismatch")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_noninteger(value):
    raise ValueError(f"noninteger JSON number: {value}")


def parse_stream(data, kind, digest=None):
    """Validate actual bytes, full fixed schedule and every literal result/type."""
    expected = expected_frames(kind, digest)
    if type(data) is not bytes or not data.endswith(b"\n"):
        raise ValueError("stream needs a final LF or CRLF terminator")
    lines = data.split(b"\n")[:-1]
    if any(b"\r" in line for line in lines):
        if not all(line.endswith(b"\r") and b"\r" not in line[:-1] for line in lines):
            raise ValueError("mixed or malformed CR terminators")
        lines = [line[:-1] for line in lines]
    if len(lines) != len(CASES):
        raise ValueError("stream must contain exactly28 frames")
    actual = []
    for index, line in enumerate(lines):
        text = line.decode("utf-8", errors="strict")
        frame = json.loads(text, object_pairs_hook=unique_object,
                           parse_float=reject_noninteger, parse_constant=reject_noninteger)
        strict_equal(frame, expected[index], f"frame[{index}]")
        actual.append(frame)
    return actual


def compare(target_path, native_path, source_path, digest):
    binding_digest(digest)
    target = parse_stream(target_path.read_bytes(), "target")
    native = parse_stream(native_path.read_bytes(), "target")
    source = parse_stream(source_path.read_bytes(), "source", digest)
    strict_equal(target, native, "interpreted/native")
    for index, (left, right) in enumerate(zip(target, source, strict=True)):
        for field in ("id", "operation", "input", "output"):
            strict_equal(left[field], right[field], f"coupling[{index}].{field}")


def encode(frames):
    return b"".join(json.dumps(frame, sort_keys=True, separators=(",", ":"),
                               allow_nan=False).encode("utf-8") + b"\n" for frame in frames)


def parser_cases():
    """Finite wire mutations of handwritten fixtures, with no numerical model."""
    digest = "a" * 64  # Synthetic parser fixture only; never source authentication.
    target = expected_frames("target")
    source = expected_frames("source", digest)
    good = encode(target)
    cases = [("target-lf", good, "target", None, True),
             ("target-crlf", good.replace(b"\n", b"\r\n"), "target", None, True),
             ("source-lf", encode(source), "source", digest, True),
             ("source-crlf", encode(source).replace(b"\n", b"\r\n"), "source", digest, True)]

    def bad(name, frames, kind="target", supplied=None):
        cases.append((name, encode(frames), kind, supplied, False))

    for index in range(len(CASES)):
        frames = copy.deepcopy(target)
        frames[index]["output"]["result"] += 1
        bad(f"result-{index + 1:02}", frames)
    positions = [("input", name) for name in ("factor", "numerator", "denominator")]
    positions += [("output", "result")]
    positions += [("output", "after", name) for name in ("factor", "numerator", "denominator")]
    for position in positions:
        for label, value in [("bool", True), ("float", 1.0), ("string", "1"),
                             ("negative", -1), ("null", None)]:
            frames = copy.deepcopy(target)
            owner = frames[0]
            for key in position[:-1]:
                owner = owner[key]
            owner[position[-1]] = value
            bad("-".join(position) + "-" + label, frames)
    for index in (18, 19, 20):
        frames = copy.deepcopy(target)
        frames[index]["input"]["factor"] = 0
        bad(f"huge-factor-truncated-{index}", frames)
    for key in target[0]:
        frames = copy.deepcopy(target)
        del frames[0][key]
        bad("root-missing-" + key, frames)
    for path in [(), ("input",), ("output",), ("output", "after"),
                 ("classes",), ("classes", "input"), ("classes", "after")]:
        frames = copy.deepcopy(target)
        owner = frames[0]
        for key in path:
            owner = owner[key]
        owner["extra"] = 0
        bad("extra-" + "-".join(path), frames)
    for key, value in [("schema", "taylor-source-v1"), ("domain", "typed-source"),
                       ("operation", "other"), ("id", "T99")]:
        frames = copy.deepcopy(target)
        frames[0][key] = value
        bad("wrong-" + key, frames)
    for key in ("input", "after"):
        for name in ("factor", "numerator", "denominator"):
            frames = copy.deepcopy(target)
            frames[0]["classes"][key][name] = "Lean.UInt64"
            bad(f"class-{key}-{name}", frames)
    frames = copy.deepcopy(target)
    frames[0]["classes"]["output"] = "Lean.Int"
    bad("result-class", frames)
    frames = copy.deepcopy(target)
    frames[0]["classes"]["bindingDigest"] = digest
    bad("target-binding-extra", frames)
    frames = copy.deepcopy(target)
    frames[0]["input"]["denominator"] = 0
    bad("denominator-zero", frames)
    frames = copy.deepcopy(target)
    frames[0]["output"] = {"kind": "error", "exception": {"class": "builtins.ValueError",
                          "args": [], "message": "raw"}, "after": frames[0]["input"]}
    bad("unexpected-error", frames)
    bad("reordered", [target[1], target[0], *target[2:]])
    bad("duplicate-id", [target[0], target[0], *target[2:]])
    bad("missing-frame", target[:-1])
    bad("extra-frame", [*target, target[0]])
    for label, value in [("missing", None), ("wrong", "b" * 64), ("malformed", "A" * 64)]:
        frames = copy.deepcopy(source)
        if value is None:
            del frames[0]["classes"]["bindingDigest"]
        else:
            frames[0]["classes"]["bindingDigest"] = value
        bad("source-binding-" + label, frames, "source", digest)
    cases.append(("external-binding-missing", encode(source), "source", None, False))
    cases.append(("external-binding-malformed", encode(source), "source", "z" * 64, False))
    for label, raw in [
        ("missing-final-lf", good[:-1]), ("blank-line", good + b"\n"),
        ("bare-cr", good.replace(b"\n", b"\r")),
        ("mixed-crlf", good.replace(b"\n", b"\r\n", 1)),
        ("doubled-cr", good.replace(b"\n", b"\r\r\n")),
        ("misplaced-cr", good.replace(b"{", b"{\r", 1)),
        ("invalid-utf8", b"\xff" + good), ("bom", b"\xef\xbb\xbf" + good),
        ("trailing-diagnostic", good + b"PASS\n"),
        ("concatenated", good.replace(b"\n", b"", 1)),
        ("truncated-json", good.replace(b"}\n", b"\n", 1)),
        ("duplicate-root", good.replace(b'"schema":', b'"id":"T01","schema":', 1)),
        ("duplicate-nested", good.replace(b'"factor":0', b'"factor":0,"factor":0', 1)),
        ("nan", good.replace(b'"result":0', b'"result":NaN', 1)),
        ("infinity", good.replace(b'"result":0', b'"result":Infinity', 1)),
    ]:
        cases.append((label, raw, "target", None, False))
    return cases


def self_test(output):
    output.mkdir(parents=True, exist_ok=False)
    executable = [sys.executable, "-B"]
    if sys.flags.optimize:
        executable.append("-O")
    executable.append(str(Path(__file__).resolve()))
    target = output / "literal-target.jsonl"
    target.write_bytes(encode(expected_frames("target")))
    count = 0
    for name, raw, kind, digest, valid in parser_cases():
        try:
            parse_stream(raw, kind, digest)
            accepted = True
        except (ValueError, UnicodeError):
            accepted = False
        if accepted != valid:
            raise ValueError(f"in-memory self-test failed: {name}")
        dest = output / name
        dest.mkdir()
        fixture = dest / "input.jsonl"
        fixture.write_bytes(raw)
        if kind == "target":
            argv = [*executable, "--check-target", str(fixture)]
        else:
            argv = [*executable, "--compare", "--target", str(target), "--native", str(target),
                    "--source", str(fixture)]
            if digest is not None:
                argv += ["--source-binding-digest", digest]
        start = datetime.now(timezone.utc).isoformat()
        result = subprocess.run(argv, input=b"", capture_output=True, check=False)
        end = datetime.now(timezone.utc).isoformat()
        streams = {}
        for filename, body in [("stdin.bin", b""), ("stdout.bin", result.stdout),
                               ("stderr.bin", result.stderr)]:
            (dest / filename).write_bytes(body)
            streams[filename] = {"size": len(body), "sha256": hashlib.sha256(body).hexdigest()}
        record = {"argv": argv, "cwd": str(Path.cwd()), "start_utc": start, "end_utc": end,
                  "exit": result.returncode, "expected_accept": valid, "streams": streams}
        (dest / "record.json").write_text(json.dumps(record, indent=2) + "\n")
        if (result.returncode == 0) != valid:
            raise ValueError(f"actual public CLI self-test failed: {name}")
        count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check-target", type=Path)
    modes.add_argument("--compare", action="store_true")
    modes.add_argument("--self-test", action="store_true")
    parser.add_argument("--target", type=Path)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--source-binding-digest")
    parser.add_argument("--self-test-output", type=Path)
    args = parser.parse_args()
    coupling_args = (args.target, args.native, args.source, args.source_binding_digest)
    try:
        if args.self_test:
            if any(value is not None for value in coupling_args) or args.self_test_output is None:
                raise ValueError("--self-test requires only --self-test-output fresh-directory")
            count = self_test(args.self_test_output.resolve())
            print(f"PASS {count} literal parser cases and actual public CLI invocations")
        elif args.check_target is not None:
            if (any(value is not None for value in coupling_args) or
                    args.self_test_output is not None):
                raise ValueError("--check-target takes no comparison/self-test arguments")
            parse_stream(args.check_target.read_bytes(), "target")
            print("PASS28 complete target frames and handwritten results")
        else:
            if any(value is None for value in coupling_args) or args.self_test_output is not None:
                raise ValueError(
                    "--compare requires target/native/source and external source binding digest")
            compare(args.target, args.native, args.source, args.source_binding_digest)
            print("PASS28 complete interpreted/native/source frames and handwritten results")
        return 0
    except (OSError, ValueError, UnicodeError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
