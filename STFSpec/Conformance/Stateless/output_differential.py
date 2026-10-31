"""Strict whole-stdout target check against independent complete byte literals."""
import argparse
import hashlib
import json
from pathlib import Path
import re

OUT = Path(__file__).resolve().parent

def expected_rows():
    data = (OUT / 'output_literals.json').read_bytes()
    if hashlib.sha256(data).hexdigest() != 'd5cb4c09f46ee695e762126eb6cdd102ec52967b69144450f02ef0fab5aa9ec5':
        raise ValueError('matrix changed')
    return [dict(name=r['name'], actual_hex=r['expected_hex']) for r in json.loads(data)['rows']] + [dict(name='zero_sentinel', actual_hex='00' * 43)]

def object_without_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key')
        result[key] = value
    return result

def check(text):
    lines = text.splitlines()
    expected = expected_rows()
    if len(lines) != len(expected):
        raise ValueError('wrong output line count')
    for line, wanted in zip(lines, expected):
        actual = json.loads(line, object_pairs_hook=object_without_duplicates)
        if type(actual) is not dict or set(actual) != {'name', 'actual_hex'}:
            raise ValueError('wrong output object shape')
        if type(actual['name']) is not str or type(actual['actual_hex']) is not str:
            raise ValueError('wrong output value type')
        if re.fullmatch('[0-9a-f]{86}', actual['actual_hex']) is None:
            raise ValueError('output is not 43 lowercase-hex bytes')
        if actual != wanted:
            raise ValueError('complete output mismatch: ' + wanted['name'])
    return len(expected)

if __name__ == '__main__':
    args = argparse.ArgumentParser()
    args.add_argument('--check-target', type=Path, required=True)
    parsed = args.parse_args()
    count = check(parsed.check_target.read_text())
    print(f'Complete target stdout matches {count} independent literal rows including sentinel.')
