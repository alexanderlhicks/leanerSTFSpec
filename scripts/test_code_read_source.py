"""Check source comparison and actual-worker authentication admission without EELS."""

import copy
import json
from pathlib import Path
import runpy
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
MODULE = runpy.run_path(str(ROOT / "STFSpec/Conformance/State/code_read_source.py"))
READER = MODULE["READER"]


def stream(rows):
    return "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows)


class SourceReaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = READER.recipes()
        cls.source = [READER.expected(r, source=True) for r in cls.cases if r["sourceComparable"]]
        cls.target = [READER.expected(r) for r in cls.cases]

    def test_complete_projection(self):
        parsed = READER.parse_stream(stream(self.source).encode(), source=True)
        self.assertEqual(parsed, self.source)
        MODULE["compare_targets"](self.target, parsed)

    def test_exact_source_failures_and_mark_before_call(self):
        idx = next(i for i, row in enumerate(self.source)
                   if row["attempts"][0]["failedSourceReads"] is not None)
        for key, value in [("providerObservedReads", [False]), ("providerObservedReads", [1]),
                           ("providerObservedAddCounts", [0]), ("readAdds", []),
                           ("failedSourceReads", None), ("reads", []),
                           ("answer", {"error": {"keyError": "wrong"}}), ("frame", None)]:
            with self.subTest(key=key, value=value):
                changed = copy.deepcopy(self.source)
                changed[idx]["attempts"][0][key] = value
                with self.assertRaises(READER.AdmissionError):
                    READER.parse_stream(stream(changed).encode(), source=True)

    def test_projected_loss_is_rejected(self):
        changed = copy.deepcopy(self.target)
        changed[0]["attempts"][0]["frame"]["block"]["code_writes"].clear()
        with self.assertRaises(READER.AdmissionError):
            MODULE["compare_targets"](changed, self.source)

    def test_runtime_flags_and_pinned_compiled_identities(self):
        names = [*MODULE["SOURCE_MODULES"], "ethereum_types.numeric", "ethereum_types.bytes"]
        files = [{"path": f"/source/{n}.py", "size": i, "sha256": str(i) * 64}
                 for i, n in enumerate(names)]
        identity = {"files": files[:2]}
        executable = {"path": "/python"}
        auth = {"optimize": 1, "isolated": 1, "dont_write_bytecode": True,
                "executable": executable, "imported_files": files,
                "operation_source": "def get_code(): ...",
                "source_loading": {"policy": "compile-source-without-bytecode-cache",
                                   "compiled_sources": dict(zip(names, files, strict=True))}}
        envelope = {"authentication": auth, "observations": stream(self.source)}
        read = MODULE["read_worker"]
        encode = lambda value: json.dumps(value, separators=(",", ":")).encode()
        self.assertEqual(read(encode(envelope), 1, identity, executable)[2], self.source)
        for field, value in [("optimize", True), ("isolated", True), ("dont_write_bytecode", 1),
                             ("operation_source", "def get_account(): ..."), ("executable", {})]:
            with self.subTest(field=field):
                changed = copy.deepcopy(envelope)
                changed["authentication"][field] = value
                with self.assertRaises(READER.AdmissionError):
                    read(encode(changed), 1, identity, executable)
        for name in names:
            changed = copy.deepcopy(envelope)
            changed["authentication"]["source_loading"]["compiled_sources"][name] = {}
            with self.assertRaises(READER.AdmissionError):
                read(encode(changed), 1, identity, executable)
        different_pin = copy.deepcopy(identity)
        different_pin["files"][0]["sha256"] = "f" * 64
        with self.assertRaises(READER.AdmissionError):
            read(encode(envelope), 1, different_pin, executable)

    def test_worker_installs_policy_before_probe_and_authenticates_same_policy(self):
        worker = MODULE["worker"]
        calls = []
        policy = object()
        auth = worker.__globals__["AUTH"]

        def install():
            calls.append("install")
            return policy

        def probe():
            calls.append("probe")
            yield {"sentinel": 17}

        def report(eels, used_policy, *, operation_name):
            calls.append("authenticate")
            self.assertIs(used_policy, policy)
            self.assertEqual(operation_name, "get_code")
            self.assertEqual(eels, Path("eels"))
            return {"actual": True}

        with patch.object(auth, "install_source_only_imports", install), \
             patch.object(auth, "authenticate", report), \
             patch.dict(worker.__globals__, probe=probe):
            got = worker(Path("eels"))
        self.assertEqual(calls, ["install", "probe", "authenticate"])
        self.assertEqual(got, {"authentication": {"actual": True}, "observations": '{"sentinel":17}\n'})


if __name__ == "__main__":
    unittest.main()
