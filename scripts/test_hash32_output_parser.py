# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regressions of the complete native Hash32 observation parser; no Lean build needed."""

import importlib.util
from pathlib import Path
import unittest


DRIVER = Path(__file__).resolve().parents[1] / \
    "STFSpec/Conformance/Base/hash32_table_support.py"
spec = importlib.util.spec_from_file_location("hash32_table_support", DRIVER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Cannot load Hash32 support driver: {DRIVER}")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
check_output = driver.check_output


def complete_output():
    """Construct independent expected observations, including every map/query."""
    vectors = [0, 1, 3, 8, (1 << 256) - 1, 3 + (1 << 256)]

    def key_bytes(n):
        return list((n % (1 << 256)).to_bytes(32, "big"))

    def table_hash(n):
        result = 14695981039346656037
        for byte in key_bytes(n):
            result = ((result ^ byte) * 1099511628211) & ((1 << 64) - 1)
        return result

    def payload(n):
        return [n & 255, (n >> 8) & 255, 170, 85]

    keys = [(1 << 240) + 257 * i for i in range(1025)]
    parent = dict(zip(keys[:1024], map(payload, range(1024))))
    maps = {"tiny": {3: payload(3), 8: payload(2)}, "parent": parent}
    maps["latest"] = {key: payload(i + 32768 if i % 3 == 0 else i)
                      for i, key in enumerate(keys[:1024])}
    maps["parentAfter"] = parent
    for sibling in range(16):
        child = dict(parent)
        for i in range(64):
            child[keys[i * 13]] = payload(sibling * 64 + i + 8192)
        child[keys[1024]] = payload(sibling + 61440)
        maps[f"sibling{sibling}"] = child
    maps["parentReleased"] = parent
    lines = [f"V|{n}|{table_hash(n)}|{table_hash(n)}|{key_bytes(n)}" for n in vectors]
    for label, entries in maps.items():
        lines.append(f"S|{label}|{len(entries)}")
        queries = [3, 8, 3 + (1 << 256), 999] if label == "tiny" else keys
        for n in queries:
            value = entries.get(n % (1 << 256))
            actual = "none" if value is None else str(value)
            lines.append(f"M|{label}|{n}|{key_bytes(n)}|{actual}")
    return lines, vectors


class Hash32OutputParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lines, cls.vectors = complete_output()

    def mutated(self, prefix, field, replacement):
        lines = self.lines.copy()
        index = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[index].split("|")
        fields[field] = replacement
        lines[index] = "|".join(fields)
        return "\n".join(lines)

    def reject(self, raw):
        with self.assertRaises(AssertionError):
            check_output(raw, self.vectors)

    def test_complete_valid_output(self):
        summary = check_output("\n".join(self.lines) + "\n", self.vectors)
        self.assertEqual(summary, {"vectors": 6, "maps": 21,
                                  "whole_key_payload_lookups": 20504,
                                  "observations": 20531})

    def test_byte_classes_and_bounds(self):
        for prefix, field, valid in (("V|1|", 4, [0] * 31 + [1]),
                                     ("M|tiny|3|", 3, [0] * 31 + [3]),
                                     ("M|tiny|3|", 4, [3, 0, 170, 85])):
            for byte in (False, 0.0, [], {}, -1, 256):
                with self.subTest(prefix=prefix, field=field, byte=byte):
                    changed = valid.copy()
                    changed[0 if field != 4 or prefix.startswith("V") else 1] = byte
                    self.reject(self.mutated(prefix, field, repr(changed)))
        for prefix, field, valid, index in (("V|1|", 4, [0] * 31 + [1], 31),
                                            ("M|parent|", 3, [0, 1] + [0] * 30, 1)):
            for byte in (True, 1.0):
                with self.subTest(prefix=prefix, byte=byte):
                    changed = valid.copy()
                    changed[index] = byte
                    self.reject(self.mutated(prefix, field, repr(changed)))
        for byte in (True, 1.0):
            with self.subTest(payload_byte=byte):
                prefix = f"M|parent|{(1 << 240) + 257 * 256}|"
                self.reject(self.mutated(prefix, 4, repr([0, byte, 170, 85])))

    def test_containers_and_byte_shape(self):
        for prefix, field, valid in (("V|0|", 4, [0] * 32),
                                     ("M|tiny|3|", 3, [0] * 31 + [3]),
                                     ("M|tiny|3|", 4, [3, 0, 170, 85])):
            for value in (tuple(valid), dict(enumerate(valid)), valid[:-1], valid + [0],
                          "bytes", None, 0, []):
                with self.subTest(prefix=prefix, field=field, value=value):
                    self.reject(self.mutated(prefix, field, repr(value)))
            self.reject(self.mutated(prefix, field, "["))

    def test_absence_marker_and_empty_payload(self):
        for value in ("None", "[]", "()", "{}", "NONE", " none", "none "):
            with self.subTest(value=value):
                self.reject(self.mutated("M|tiny|999|", 4, value))
        self.reject(self.mutated("M|tiny|3|", 4, "none"))

    def test_natural_scalar_fields(self):
        for prefix, field, original in (("V|0|", 1, "0"), ("V|0|", 2, "0"),
                                        ("V|0|", 3, "0"), ("S|tiny|", 2, "2"),
                                        ("M|tiny|3|", 2, "3")):
            if prefix == "V|0|" and field in (2, 3):
                original = self.lines[0].split("|")[field]
            for value in ("-1", "True", "1.0", "+" + original, " " + original,
                          original + " ", "0_" + original, "", "１２"):
                with self.subTest(prefix=prefix, field=field, value=value):
                    self.reject(self.mutated(prefix, field, value))

    def test_schema_labels_and_completeness(self):
        for prefix in ("V|", "S|", "M|"):
            index = next(i for i, line in enumerate(self.lines) if line.startswith(prefix))
            for replacement in (self.lines[index] + "|extra",
                                self.lines[index].rsplit("|", 1)[0], "X|unknown", ""):
                with self.subTest(prefix=prefix, replacement=replacement):
                    lines = self.lines.copy()
                    lines[index] = replacement
                    self.reject("\n".join(lines))
        for prefix in ("V|0|", "S|tiny|", "M|tiny|3|"):
            index = next(i for i, line in enumerate(self.lines) if line.startswith(prefix))
            self.reject("\n".join(self.lines[:index] + [self.lines[index]] + self.lines[index:]))
        for prefix in ("V|0|", "S|tiny|", "M|tiny|999|"):
            index = next(i for i, line in enumerate(self.lines) if line.startswith(prefix))
            self.reject("\n".join(self.lines[:index] + self.lines[index + 1:]))
        index = next(i for i, line in enumerate(self.lines) if line.startswith("M|tiny|3|"))
        self.reject("\n".join(self.lines + [self.lines[index]]))
        for prefix in ("S|tiny|", "M|tiny|3|"):
            self.reject(self.mutated(prefix, 1, "unknown"))
        self.reject(self.mutated("M|tiny|3|", 2, "4"))

    def test_values_and_observation_order(self):
        for prefix, field, replacement in (
                ("V|0|", 2, "0"), ("V|0|", 3, "0"),
                ("V|0|", 4, repr([0] * 31 + [1])),
                ("M|tiny|3|", 3, repr([0] * 31 + [4])),
                ("M|tiny|3|", 4, repr([4, 0, 170, 85])), ("S|tiny|", 2, "1")):
            with self.subTest(prefix=prefix, field=field):
                self.reject(self.mutated(prefix, field, replacement))
        for prefix in ("V|", "M|tiny|"):
            lines = self.lines.copy()
            indices = [i for i, line in enumerate(lines) if line.startswith(prefix)]
            first, second = indices[:2]
            lines[first], lines[second] = lines[second], lines[first]
            self.reject("\n".join(lines))
        self.reject("")
        self.reject("\n".join(self.lines) + "\n\n")


if __name__ == "__main__":
    unittest.main()
