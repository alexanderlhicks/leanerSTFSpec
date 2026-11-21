"""Check strict admission of complete code-read JSON Lines."""

import copy
import json
from pathlib import Path
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULE = runpy.run_path(str(ROOT / "STFSpec/Conformance/State/code_read_differential.py"))


def lines(rows):
    return b"".join(json.dumps(row, separators=(",", ":")).encode() + b"\n" for row in rows)


class CodeReadReaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = MODULE["recipes"]()
        cls.target = staticmethod(MODULE["parse_stream"])
        cls.expected = [MODULE["expected"](r) for r in cls.cases]
        cls.encoded = lines(cls.expected)

    def reject(self, data):
        with self.assertRaises(MODULE["AdmissionError"]):
            self.target(data)

    def test_complete_stream(self):
        self.assertEqual(self.target(self.encoded), self.expected)

    def test_rows_and_framing(self):
        for invalid in [lines(self.expected[:-1]), lines(self.expected + self.expected[:1]),
                        lines(self.expected[::-1]), self.encoded[:-1], self.encoded + b"\n",
                        b"\xff" + self.encoded[1:], b"x" * (2**22 + 1)]:
            self.reject(invalid)
        self.reject(self.encoded.replace(b'"id":', b'"id":"duplicate","id":', 1))
        self.reject(self.encoded.replace(b"[31,35]", b"[31.0,35]", 1))
        self.reject(self.encoded.replace(b"[31,35]", b"[NaN,35]", 1))

    def test_full_success_answers_and_ordered_calls(self):
        idx = next(i for i, row in enumerate(self.expected)
                   if len(row["attempts"]) > 1 and row["attempts"][0]["calls"]
                   and row["attempts"][0]["reads"] is not None)
        for key, value in [("answer", {"ok": [True, 0]}), ("answer", {"ok": [255]}),
                           ("calls", []), ("calls", [[False, 0]]), ("reads", []),
                           ("frame", None), ("lean", None)]:
            with self.subTest(key=key, value=value):
                changed = copy.deepcopy(self.expected)
                changed[idx]["attempts"][1][key] = value
                self.reject(lines(changed))

    def test_retained_leaves(self):
        slots = (("frame", "block", "account_writes"), ("frame", "tx", "transient_storage"),
                 ("lean", "blockOrders"), ("lean", "txOrders"), ("lean", "consts"),
                 ("lean", "provider", "account"), ("lean", "provider", "storage"),
                 ("lean", "provider", "code"), ("lean", "provider", "root"))
        for path in slots:
            with self.subTest(path=path):
                changed = copy.deepcopy(self.expected)
                value = changed[0]["attempts"][0]
                for key in path[:-1]:
                    value = value[key]
                del value[path[-1]]
                self.reject(lines(changed))

    def test_every_typed_failure(self):
        for i, row in enumerate(self.expected):
            if not row["id"].startswith("typed-error-"):
                continue
            with self.subTest(id=row["id"]):
                for key, value in [("answer", {"error": {"witness": {"missing": {"code": 0}}}}),
                                   ("reads", []), ("frame", {}), ("lean", {})]:
                    changed = copy.deepcopy(self.expected)
                    changed[i]["attempts"][0][key] = value
                    self.reject(lines(changed))


if __name__ == "__main__":
    unittest.main()
