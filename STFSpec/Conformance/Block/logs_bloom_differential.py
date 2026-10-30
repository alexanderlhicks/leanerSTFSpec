#!/usr/bin/env python3
"""Compare complete public logsBloom observations with immutable independent literals.

The twenty original complete cases were frozen before source execution, then checked
against pinned EELS. Synthetic answers and effects were frozen before target observation.
This reader imports neither EELS nor a runtime protocol/cryptographic expected model.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

CATALOG = '6fe020501102507a348d249da59332a822f691a867279e1153f092249a91160a'
SCHEMA = 'logs-bloom-v1'
CASE_COUNT = 112
SOURCE_COUNT = 20
SOURCE_QUERY_COUNT = 85
SYNTHETIC_COUNT = 72
MAX_BYTES = 4_000_000
MAX_LINE = 500_000


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON key: {key}')
        result[key] = value
    return result


def invalid_constant(value):
    raise ValueError(f'invalid JSON constant: {value}')


def decode(text):
    return json.loads(text, object_pairs_hook=unique_object, parse_constant=invalid_constant)


def exact(actual, expected, path='$'):
    """Compare recursively with exact Python types: bool is never an integer."""
    if type(actual) is not type(expected):
        raise ValueError(f'{path}: type {type(actual).__name__}, expected {type(expected).__name__}')
    if type(expected) is dict:
        if actual.keys() != expected.keys():
            raise ValueError(f'{path}: object fields differ')
        for key in expected:
            exact(actual[key], expected[key], f'{path}.{key}')
    elif type(expected) is list:
        if len(actual) != len(expected):
            raise ValueError(f'{path}: array length differs')
        for index, (a, e) in enumerate(zip(actual, expected)):
            exact(a, e, f'{path}[{index}]')
    elif actual != expected:
        raise ValueError(f'{path}: value differs')


def load_catalogue():
    raw = Path(__file__).with_name('logs_bloom_cases.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != CATALOG:
        raise ValueError('frozen catalogue identity differs')
    value = decode(raw)
    if type(value) is not dict or set(value) != {
        'schema', 'source_catalogue_sha256', 'provenance', 'source_catalogue', 'frames'
    }:
        raise ValueError('frozen catalogue schema differs')
    exact(value['schema'], 1)
    exact(len(value['source_catalogue']), SOURCE_COUNT)
    exact(sum(len(row['queries']) for row in value['source_catalogue']), SOURCE_QUERY_COUNT)
    exact(len(value['frames']), CASE_COUNT)
    return value


def expected_frames():
    header = {'schema': SCHEMA, 'catalog': CATALOG, 'count': CASE_COUNT,
              'source_count': SOURCE_COUNT, 'source_query_count': SOURCE_QUERY_COUNT,
              'synthetic_count': SYNTHETIC_COUNT}
    end = {'end': True, 'count': CASE_COUNT, 'catalog': CATALOG}
    return [header, *load_catalogue()['frames'], end]


def check_text(raw):
    if type(raw) is not str or len(raw.encode('utf-8')) > MAX_BYTES:
        raise ValueError('target stream exceeds finite evidence size')
    lines = raw.splitlines()
    if len(lines) != CASE_COUNT + 2 or any(not line or len(line) > MAX_LINE for line in lines):
        raise ValueError('target framing/line count differs')
    actual = [decode(line) for line in lines]
    exact(actual, expected_frames())
    return CASE_COUNT


def check_target(path):
    raw = Path(path).read_bytes()
    if len(raw) > MAX_BYTES:
        raise ValueError('target stream exceeds finite evidence size')
    return check_text(raw.decode('utf-8'))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-target', required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        count = check_target(args.check_target)
    except (ValueError, OSError, UnicodeError, RecursionError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        return 1
    print(f'PASS: {count} complete logsBloom frames; 20 real cases and 72 synthetic/effect cases')
    return 0


if __name__ == '__main__':
    sys.exit(main())
