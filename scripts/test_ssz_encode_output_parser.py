#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict finite SSZ literal/native observation controls, including Python -O."""
import importlib.util
import json
from pathlib import Path
import unittest

REPO = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    'ssz_encode_differential', REPO / 'STFSpec/Conformance/Codec/ssz_encode_differential.py')
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)


class ParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = DRIVER.load_inventory()
        cls.lines = [row['id'] + ':' + json.dumps(list(bytes.fromhex(row['expected_hex'])))
                     for row in cls.rows]

    def rejects(self, lines):
        with self.assertRaises((ValueError, TypeError)):
            DRIVER.check_target('\n'.join(lines), self.rows)

    def test_complete(self):
        self.assertEqual(len(DRIVER.check_target('\n'.join(self.lines) + '\n', self.rows)), 61)

    def test_missing(self):
        self.rejects(self.lines[:-1])

    def test_duplicate(self):
        self.rejects(self.lines + self.lines[:1])

    def test_unknown(self):
        self.rejects(self.lines + ['unknown:[]'])

    def test_blank(self):
        self.rejects(self.lines + ['', ''])

    def test_exact_byte_class_and_shape(self):
        for wire in ('[true]', '[false]', '[-1]', '[256]', '[0.0]', '[[0]]',
                     'null', '{}', '"00"', '[0] trailing', '[0] #comment'):
            with self.subTest(wire=wire):
                self.rejects(['u1_zero:' + wire] + self.lines[1:])

    def test_full_bytes(self):
        for wire in ('[]', '[1]', '[0, 0]'):
            with self.subTest(wire=wire):
                self.rejects(['u1_zero:' + wire] + self.lines[1:])

    def test_strict_schema_parameters(self):
        for schema in (['uint', True], ['byteVector', False], ['byteList', -1],
                       ['list', ['uint', True], 0], ['list', ['bool'], True],
                       ['progressiveContainer', [1], []], ['container', {}]):
            with self.subTest(schema=schema), self.assertRaises((ValueError, TypeError)):
                DRIVER.validate_schema(schema)

    def test_strict_value_classes(self):
        for schema, value in ((['uint', 1], True), (['bool'], 1),
                              (['byteVector', 1], 0), (['byteList', 1], 'AA'),
                              (['list', ['uint', 1], 1], [True]),
                              (['container', [['bool']]], [0])):
            with self.subTest(value=value), self.assertRaises((ValueError, TypeError)):
                DRIVER.validate_value(schema, value)


if __name__ == '__main__':
    unittest.main()
