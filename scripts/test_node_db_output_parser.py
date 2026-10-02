# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Private NodeDB observation-schema regressions, independent of Lean/EELS builds.

The complete typed fixture is generated from ordered insertion/query events with
injected oracle answers. It is not pinned-source evidence or a Keccak oracle.
Run python3 -B scripts/test_node_db_output_parser.py and repeat with -B -O; no Lean
build, pinned environment or external artifacts are required.
"""

import importlib.util
from pathlib import Path
import unittest

MODULE_PATH = (Path(__file__).resolve().parents[1] /
               "STFSpec/Conformance/Commit/node_db_native.py")
spec = importlib.util.spec_from_file_location("node_db_native", MODULE_PATH)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
check_output = module.check_output


def complete_output():
    """Model observations from events, including present and absent query values."""
    maximum = (1 << 256) - 1
    cases = [{"case": 0, "items": []}, {"case": 1, "items": [
        {"key": f"{0:064x}", "value": ""},
        {"key": f"{999999:064x}", "value": "ff"},
        {"key": f"{maximum:064x}", "value": "0001"},
    ]}]
    lines = []

    def observe(label, events, parent=()):
        # Input order, overwrite, and retained parent contents are modeled here,
        # rather than borrowing the helper's expected-table construction.
        table = dict(parent)
        for answer, value in events:
            table[answer] = list(value)
        lines.append(f"S|{label}|{len(table)}")
        for answer, value in sorted(table.items()):
            key = [(answer >> shift) & 255 for shift in range(248, -1, -8)]
            lines.append(f"M|{label}|{answer}|{key}|{value}")
        for answer in (0, 999999, maximum):
            value = str(table[answer]) if answer in table else "none"
            lines.append(f"Q|{label}|{answer}|{value}")
        return table

    def traced(label, events, parent=()):
        table = observe(label, events, parent)
        lines.extend(f"T|{label}|{list(value)}" for _, value in events)
        return table

    observe("id0", [])
    observe("id1", [(0, []), (999999, [255]), (maximum, [0, 1])])
    small = [[], [255], [], [128, 0]]
    unique = [((1 << (64 * index)) + 7, value) for index, value in enumerate(small)]
    traced("control0", unique)
    traced("control1", [((1 << 255) + 7, value) for value in small])
    traced("empty", [])
    for label in ("forward", "reverse"):
        lines.append(f"L|{label}|91")
        traced(label, unique)
    events = [(1 << index, [index >> 8, index & 255, 170, 85]) for index in range(256)]
    traced("markers", events)
    events = [((1 << 240) + 257 * index, [index >> 8, index & 255, 170, 85])
              for index in range(1024)]
    parent = traced("large", events)
    for sibling in range(8):
        extension = [((1 << 240) + 257 * index, [0, index, sibling, 0])
                     for index in range(64)]
        traced(f"sibling{sibling}", extension, parent.items())
    observe("parentAfter", [], parent.items())
    for position in range(4):
        label = f"failure{position}"
        lines.append(f"F|{label}|{position}")
        lines.extend(f"T|{label}|{value}" for value in small[:position + 1])
    return lines, cases


class NodeDBOutputParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lines, cls.cases = complete_output()

    def mutated(self, prefix, field, value):
        lines = self.lines.copy()
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("|")
        fields[field] = value
        lines[index] = "|".join(fields)
        return "\n".join(lines)

    def reject(self, raw):
        # Parent rejects some controls with conversion/lookup errors rather than
        # assertions. Acceptance itself is the behavior under regression here.
        with self.assertRaises((AssertionError, ValueError, TypeError, KeyError,
                                SyntaxError, OverflowError, IndexError)):
            check_output(raw, self.cases)

    def test_complete_typed_frame(self):
        self.assertEqual(check_output("\n".join(self.lines) + "\n", self.cases),
                         {"maps": 18, "full_key_value_observations": 10512,
                          "missing_or_present_queries": 54, "ordered_queries": 1818,
                          "failure_positions": 4})

    def test_byte_member_types_and_bounds(self):
        for prefix, field, valid, index in (
            ("M|id1|0|", 3, [0] * 32, 0),
            (f"M|id1|{(1 << 256) - 1}|", 4, [0, 1], 0),
            (f"Q|id1|{(1 << 256) - 1}|", 3, [0, 1], 0),
            ("T|control0|[128, 0]", 2, [128, 0], 1),
        ):
            for byte in (False, 0.0, [], {}, -1, 256):
                with self.subTest(prefix=prefix, byte=byte):
                    value = valid.copy()
                    value[index] = byte
                    self.reject(self.mutated(prefix, field, repr(value)))
        for prefix, field, valid, index in (
            ("M|markers|1|", 3, [0] * 31 + [1], 31),
            (f"M|id1|{(1 << 256) - 1}|", 4, [0, 1], 1),
            (f"Q|id1|{(1 << 256) - 1}|", 3, [0, 1], 1),
            ("T|markers|[0, 1, 170, 85]", 2, [0, 1, 170, 85], 1),
        ):
            for byte in (True, 1.0):
                with self.subTest(prefix=prefix, byte=byte):
                    value = valid.copy()
                    value[index] = byte
                    self.reject(self.mutated(prefix, field, repr(value)))

    def test_containers_and_hash_width(self):
        for prefix, field, valid in (("M|id1|0|", 3, [0] * 32),
                                     ("M|id1|0|", 4, []), ("Q|id1|0|", 3, []),
                                     ("T|control0|[]", 2, [])):
            for value in (tuple(valid), bytes(valid), False, 0, None, {}, ""):
                with self.subTest(prefix=prefix, value=value):
                    self.reject(self.mutated(prefix, field, repr(value)))
            self.reject(self.mutated(prefix, field, "["))
        for value in ([0] * 31, [0] * 33):
            self.reject(self.mutated("M|id1|0|", 3, repr(value)))
        for prefix, field, value in (("M|id1|999999|", 4, (255,)),
                                     ("Q|id1|999999|", 3, (255,)),
                                     ("T|control0|[255]", 2, (255,))):
            self.reject(self.mutated(prefix, field, repr(value)))

    def test_absence_marker_and_present_empty_bytes(self):
        for value in ("None", "NONE", " none", "none ", "[]", "()", "False", "0"):
            with self.subTest(value=value):
                self.reject(self.mutated("Q|id0|0|", 3, value))
        self.reject(self.mutated("Q|id1|0|", 3, "none"))

    def test_natural_scalars_and_full_hash_bound(self):
        for prefix, field, original in (("S|id0|", 2, "0"), ("M|id1|0|", 2, "0"),
                                        ("Q|id0|0|", 2, "0"), ("F|failure0|", 2, "0"),
                                        ("L|forward|", 2, "91")):
            for value in ("-1", "True", "0.0", "+" + original, " " + original,
                          original + " ", "0_" + original, "0" + original,
                          "", "１２", "-0"):
                with self.subTest(prefix=prefix, value=value):
                    self.reject(self.mutated(prefix, field, value))
        for prefix in ("M|id1|0|", "Q|id0|0|"):
            self.reject(self.mutated(prefix, 2, str(1 << 256)))
        self.reject(self.mutated("M|id1|0|", 2, "1"))

    def test_schema_labels_and_completeness(self):
        for prefix in ("S|", "M|", "Q|", "T|", "F|", "L|"):
            index = next(i for i, line in enumerate(self.lines) if line.startswith(prefix))
            for replacement in (self.lines[index] + "|extra",
                                self.lines[index].rsplit("|", 1)[0], "X|unknown", ""):
                with self.subTest(prefix=prefix, replacement=replacement):
                    lines = self.lines.copy()
                    lines[index] = replacement
                    self.reject("\n".join(lines))
            self.reject(self.mutated(prefix, 1, "unknown"))
            lines = self.lines.copy()
            del lines[index]
            self.reject("\n".join(lines))
            lines = self.lines.copy()
            lines.insert(index, lines[index])
            self.reject("\n".join(lines))

    def test_query_and_trace_order_and_payload_contents(self):
        for prefix in ("Q|id0|", "T|control0|"):
            lines = self.lines.copy()
            indices = [i for i, line in enumerate(lines) if line.startswith(prefix)]
            lines[indices[0]], lines[indices[1]] = lines[indices[1]], lines[indices[0]]
            self.reject("\n".join(lines))
        self.reject(self.mutated("M|id1|999999|", 4, "[254]"))
        self.reject(self.mutated("Q|id1|999999|", 3, "[254]"))
        self.reject(self.mutated("F|failure3|", 2, "2"))
        self.reject(self.mutated("L|forward|", 2, "92"))


if __name__ == "__main__":
    unittest.main()
