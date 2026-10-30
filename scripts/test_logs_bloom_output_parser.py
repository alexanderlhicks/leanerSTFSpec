#!/usr/bin/env python3
"""Strict literal/output controls; identical checks under normal and optimized Python."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / 'STFSpec/Conformance/Block/logs_bloom_differential.py'
spec = importlib.util.spec_from_file_location('logs_bloom_differential', DRIVER)
bloom = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bloom)


def encode(frames):
    return ''.join(json.dumps(row, separators=(',', ':')) + '\n' for row in frames)


def paths(value, prefix=()):
    yield prefix, value
    if type(value) is dict:
        for key, child in value.items():
            yield from paths(child, prefix + (key,))
    elif type(value) is list:
        for index, child in enumerate(value):
            yield from paths(child, prefix + (index,))


def replace(value, path, new):
    if not path:
        return new
    out = copy.deepcopy(value)
    node = out
    for key in path[:-1]:
        node = node[key]
    node[path[-1]] = new
    return out


class StrictBloomOutput(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.frames = bloom.expected_frames()
        cls.good = encode(cls.frames)

    def reject(self, raw):
        with self.assertRaises((ValueError, RecursionError, UnicodeError)):
            bloom.check_text(raw)

    def test_accept_all_literals(self):
        self.assertEqual(bloom.check_text(self.good), 112)
        catalogue = bloom.load_catalogue()
        self.assertEqual(len(catalogue['source_catalogue']), 20)
        self.assertEqual(sum(len(r['queries']) for r in catalogue['source_catalogue']), 85)
        for row in catalogue['source_catalogue']:
            self.assertEqual(len(row['expected']), 512)
        self.assertEqual(len([r for r in catalogue['source_catalogue']
                              if r['name'] == 'zero_address_zero_topic']), 1)

    def test_every_recursive_value_type_and_shape(self):
        controls = 0
        for frame in self.frames:
            for path, value in paths(frame):
                if type(value) is dict:
                    mutations = [{**value, '__unexpected__': 0}]
                    mutations += [{k: v for k, v in value.items() if k != key} for key in value]
                    mutations += [None, [], True]
                elif type(value) is list:
                    mutations = [value + [None], None, {}, True]
                    if value:
                        mutations += [value[:-1]]
                    if len(value) > 1 and value != list(reversed(value)):
                        mutations += [list(reversed(value))]
                elif type(value) is int:
                    mutations = [True, False, float(value), str(value), value + 1, None]
                elif type(value) is bool:
                    mutations = [1, 0, not value, None]
                elif type(value) is str:
                    mutations = [None, 0, True, value + '0']
                    if value:
                        mutations += [value[:-1], value.upper() if value.upper() != value else value + 'x']
                else:
                    mutations = [False, 0, '', [], {}]
                for mutation in mutations:
                    changed = replace(frame, path, mutation)
                    with self.assertRaises(ValueError, msg=f'{path} / {mutation!r}'):
                        bloom.exact(changed, frame)
                    controls += 1
        self.assertGreater(controls, 10000)

    def test_full_framing_and_json(self):
        for index in (0, 1, 8, len(self.frames) - 1):
            self.reject(encode(self.frames[:index] + self.frames[index + 1:]))
            self.reject(encode(self.frames[:index] + [self.frames[index]] + self.frames[index:]))
        self.reject(encode([self.frames[0], *reversed(self.frames[1:-1]), self.frames[-1]]))
        self.reject(self.good + '{}\n')
        self.reject('\n' + self.good)
        self.reject(self.good.replace('\n', '\n\n', 1))
        self.reject('not json\n' + '\n'.join(self.good.splitlines()[1:]))
        self.reject(self.good.replace('"count":112', '"count":true', 1))
        self.reject(self.good.replace('"count":112', '"count":112.0', 1))
        self.reject(self.good.replace('"count":112', '"count":null', 1))
        self.reject(self.good.replace('"count":112', '"count":NaN', 1))
        self.reject(self.good.replace('"count":112', '"count":Infinity', 1))
        self.reject(self.good.replace('"count":112', '"count":112,"count":112', 1))
        self.reject(self.good.replace('"address":', '"address":"00","address":', 1))
        self.reject(self.good.replace('"preimage":', '"preimage":"00","preimage":', 1))
        self.reject(self.good.replace('"digest":', '"digest":"00","digest":', 1))
        self.reject(self.good.replace('"end":true', '"end":1', 1))

    def test_cli_invalid_json_is_nonzero(self):
        with tempfile.TemporaryDirectory(prefix='logs-bloom-parser-') as directory:
            path = Path(directory) / 'capture.jsonl'
            path.write_text(self.good)
            good = subprocess.run([sys.executable, '-B', str(DRIVER), '--check-target', str(path)],
                                  capture_output=True, text=True)
            self.assertEqual(good.returncode, 0, good.stderr)
            for text in ('{broken\n', self.good.replace('"count":112', '"count":true', 1)):
                path.write_text(text)
                bad = subprocess.run([sys.executable, '-B', str(DRIVER), '--check-target', str(path)],
                                     capture_output=True, text=True)
                self.assertNotEqual(bad.returncode, 0)
                self.assertIn('FAIL:', bad.stderr)


if __name__ == '__main__':
    unittest.main()
