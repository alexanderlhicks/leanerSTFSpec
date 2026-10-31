#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Check complete compiled SSZ bytes against independent literals and pinned EELS.

Use --check-target FILE for local native stdout validation. Add --eels CHECKOUT
under that checkout's frozen Python -I -B for 52 EELS and 3 dependency source cases.
Six mathematical cases are checked only against literals. No decoder, source
failure-order, huge-view, universal refinement or guest claim follows. Interpreter,
startup, installed distribution RECORD files and host execution remain trusted.
"""
import argparse
import base64
from dataclasses import make_dataclass
import hashlib
import importlib.abc
import importlib.machinery
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys
import tomllib
from typing import Annotated, Tuple

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def nat(value):
    return type(value) is int and value >= 0


def hex_bytes(value):
    require(type(value) is str and len(value) % 2 == 0, 'hex string required')
    result = bytes.fromhex(value)
    require(result.hex() == value, 'canonical lowercase hex required')
    return result


def validate_schema(t):
    require(type(t) is list and t and type(t[0]) is str, 'descriptor tag')
    tag = t[0]
    if tag in ('uint', 'byteVector', 'byteList'):
        require(len(t) == 2 and nat(t[1]), 'descriptor natural parameter')
    elif tag in ('bool', 'progressiveByteList'):
        require(len(t) == 1, 'descriptor arity')
    elif tag in ('list', 'progressiveList'):
        require(len(t) == (3 if tag == 'list' else 2), 'list descriptor arity')
        if tag == 'list':
            require(nat(t[2]), 'list limit')
        validate_schema(t[1])
    elif tag in ('container', 'progressiveContainer'):
        require(len(t) == (3 if tag == 'progressiveContainer' else 2), 'container arity')
        if tag == 'progressiveContainer':
            require(type(t[1]) is list and all(type(x) is bool for x in t[1]), 'mask')
        require(type(t[-1]) is list, 'field list')
        for field in t[-1]:
            validate_schema(field)
    else:
        raise ValueError('unknown descriptor')


def validate_value(t, value):
    tag = t[0]
    if tag == 'uint':
        require(nat(value), 'exact nonnegative integer payload')
    elif tag == 'bool':
        require(type(value) is bool, 'exact boolean payload')
    elif tag in ('byteVector', 'byteList', 'progressiveByteList'):
        hex_bytes(value)
    elif tag in ('list', 'progressiveList'):
        require(type(value) is list, 'actual list payload')
        for child in value:
            validate_value(t[1], child)
    else:
        require(type(value) is list and len(value) == len(t[-1]), 'exact field arity')
        for field, child in zip(t[-1], value):
            validate_value(field, child)


def load_inventory(path=HERE / 'ssz_encode_literals.json'):
    rows = json.loads(path.read_text())
    require(type(rows) is list, 'literal inventory list')
    seen = set()
    for row in rows:
        require(type(row) is dict and set(row) == {
            'id', 'path', 'type', 'value', 'expected_hex', 'derivation'}, 'literal keys')
        require(type(row['id']) is str and row['id'] and ':' not in row['id'] and
                row['id'] not in seen, 'unique literal identifier')
        require(row['path'] in ('eels_dataclass', 'dependency_sparse', 'mathematical'),
                'source classification')
        require(type(row['derivation']) is str, 'literal derivation')
        seen.add(row['id'])
        validate_schema(row['type'])
        validate_value(row['type'], row['value'])
        hex_bytes(row['expected_hex'])
    require(len(rows) == 61, 'complete 61-case inventory required')
    return rows


def check_target(text, rows):
    expected = {row['id']: hex_bytes(row['expected_hex']) for row in rows}
    actual = {}
    for line in text.splitlines():
        require(':' in line, 'native line identifier separator')
        name, encoded = line.split(':', 1)
        require(name in expected and name not in actual, 'unknown/duplicate native identifier')
        wire = json.loads(encoded)
        require(type(wire) is list and all(type(x) is int and 0 <= x < 256 for x in wire),
                'native exact byte list')
        actual[name] = bytes(wire)
        require(actual[name] == expected[name], name + ': complete native byte mismatch')
    require(set(actual) == set(expected), 'missing native observations')
    return actual


class SourceAuth:
    """Fresh executed .py bytes: pinned tracked EELS or installed dependency RECORD."""
    def __init__(self, root, reference):
        self.root = root
        self.commit = reference['release']['commit']
        self.expected = {}
        self.records = {}
        self.used = {}
        require(self.git('rev-parse', 'HEAD').strip() == self.commit, 'EELS commit pin')
        require(self.git('status', '--porcelain', '--untracked-files=no') == '',
                'tracked EELS source must be clean')
        lock = (root / 'uv.lock').read_bytes()
        require(lock == self.git_bytes('show', self.commit + ':uv.lock'), 'pinned EELS lock')
        self.used[root / 'uv.lock'] = lock
        for name in ('ethereum-types', 'eth-remerkleable'):
            dist = importlib.metadata.distribution(name)
            require(dist.version == reference['release']['python_dependencies'][name],
                    name + ': locked version')
            records = []
            for file in dist.files or []:
                path = Path(dist.locate_file(file)).resolve()
                if file.name == 'RECORD' and file.parent.name.endswith('.dist-info'):
                    records.append(path)
                if file.suffix != '.py':
                    continue
                require(file.hash is not None and file.hash.mode == 'sha256' and
                        type(file.size) is int, name + ': source RECORD hash/size')
                data = path.read_bytes()
                digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip('=')
                require(digest == file.hash.value and len(data) == file.size,
                        name + ': source differs from installed RECORD')
                self.expected[path] = data
            require(len(records) == 1, name + ': unique installed RECORD')
            self.records[records[0]] = records[0].read_bytes()

    def git_bytes(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args])

    def git(self, *args):
        return self.git_bytes(*args).decode()

    def verify(self, source, data):
        path = Path(source).resolve()
        if path.is_relative_to(self.root / 'src' / 'ethereum'):
            rel = str(path.relative_to(self.root))
            expected = self.git_bytes('show', self.commit + ':' + rel)
        else:
            require(path in self.expected, 'source outside authenticated packages')
            expected = self.expected[path]
        require(data == expected, 'executed source changed: ' + str(path))
        self.used[path] = data

    def check(self):
        require(self.git('rev-parse', 'HEAD').strip() == self.commit, 'EELS pin changed')
        require(self.git('status', '--porcelain', '--untracked-files=no') == '', 'EELS changed')
        for path, data in {**self.records, **self.expected, **self.used}.items():
            require(path.read_bytes() == data, 'source/RECORD changed during replay')


class FreshLoader(importlib.machinery.SourceFileLoader):
    def __init__(self, name, source, auth):
        super().__init__(name, source)
        self.auth = auth

    def get_code(self, fullname):
        data = Path(self.path).read_bytes()
        self.auth.verify(self.path, data)
        return self.source_to_code(data, self.path)


class FreshFinder(importlib.abc.MetaPathFinder):
    def __init__(self, auth):
        self.auth = auth

    def find_spec(self, fullname, path=None, target=None):
        if fullname.split('.')[0] not in ('ethereum', 'ethereum_types', 'remerkleable'):
            return None
        spec = importlib.machinery.PathFinder.find_spec(fullname, path)
        require(spec is not None and isinstance(spec.loader, importlib.machinery.SourceFileLoader),
                'expected source module: ' + fullname)
        self.auth.verify(spec.origin, Path(spec.origin).read_bytes())
        spec.loader = FreshLoader(fullname, spec.origin, self.auth)
        return spec


def source_replay(root, rows):
    require(sys.flags.isolated and sys.flags.dont_write_bytecode, 'source replay requires -I -B')
    prefixes = ('ethereum', 'ethereum_types', 'remerkleable')
    require(not any(name.split('.')[0] in prefixes for name in sys.modules),
            'source packages imported before authentication')
    reference = tomllib.loads((REPO / 'reference.toml').read_text())
    auth = SourceAuth(root, reference)
    sys.path.insert(0, str(root / 'src'))
    sys.meta_path.insert(0, FreshFinder(auth))
    from ethereum.utils import ssz
    from ethereum_types.numeric import Uint
    from remerkleable.progressive import ProgressiveContainer
    from remerkleable.byte_arrays import RawBytesView
    serial = 0

    def annotation(t):
        nonlocal serial
        tag = t[0]
        if tag == 'uint':
            return Annotated[Uint, ssz._Uint(t[1] * 8)]
        if tag == 'bool':
            return bool
        if tag in ('byteVector', 'byteList', 'progressiveByteList'):
            marker = {'byteVector': lambda: ssz.byte_vector(t[1]),
                      'byteList': lambda: ssz.byte_list(t[1]),
                      'progressiveByteList': ssz.progressive_byte_list}[tag]()
            return Annotated[bytes, marker]
        if tag in ('list', 'progressiveList'):
            marker = ssz.ssz_list(t[2]) if tag == 'list' else ssz.progressive_list()
            return Annotated[Tuple[annotation(t[1]), ...], marker]
        serial += 1
        base = ssz.ProgressiveSszContainer if tag == 'progressiveContainer' else ssz.SszContainer
        return make_dataclass('Case' + str(serial),
                              [('f' + str(i), annotation(f)) for i, f in enumerate(t[-1])],
                              bases=(base,))

    def value(t, raw, ann):
        tag = t[0]
        if tag in ('uint', 'bool'):
            return raw
        if tag in ('byteVector', 'byteList', 'progressiveByteList'):
            return hex_bytes(raw)
        if tag in ('list', 'progressiveList'):
            elem = ssz._collection_element(ann)
            return tuple(value(t[1], child, elem) for child in raw)
        return ann(**{'f' + str(i): value(f, child, a)
                      for i, ((_, a), f, child) in
                      enumerate(zip(ssz._field_types(ann), t[-1], raw))})

    counts = {'eels_dataclass': 0, 'dependency_sparse': 0, 'mathematical': 0}
    for row in rows:
        counts[row['path']] += 1
        if row['path'] == 'mathematical':
            continue
        t, raw = row['type'], row['value']
        raw_view = None
        if row['path'] == 'dependency_sparse':
            require(t[0] == 'progressiveContainer', 'sparse progressive descriptor')
            fields = {'f' + str(i): ssz._rmk_type(ssz._infer(annotation(f)))
                      for i, f in enumerate(t[-1])}
            cls = type('Sparse' + row['id'],
                       (ProgressiveContainer(active_fields=[int(x) for x in t[1]]),),
                       {'__annotations__': fields})
            args = {'f' + str(i): (hex_bytes(x) if f[0] in ('byteVector', 'byteList') else x)
                    for i, (f, x) in enumerate(zip(t[-1], raw))}
            actual = cls(**args).encode_bytes()
        else:
            ann = annotation(t)
            obj = value(t, raw, ann)
            if t[0] in ('container', 'progressiveContainer'):
                actual = ssz._to_view(obj).encode_bytes()
            else:
                wrapper = make_dataclass('Wrapper' + str(serial), [('f0', ann)],
                                         bases=(ssz.SszContainer,))
                view = ssz._to_view(wrapper(obj))
                raw_view = view.f0
                actual = raw_view.encode_bytes()
                whole = view.encode_bytes()
                fixed = ssz._rmk_type(ssz._infer(ann)).is_fixed_byte_length()
                require(type(whole) is bytes and whole == (b'' if fixed else b'\x04\0\0\0') + actual,
                        row['id'] + ': enclosing wrapper mismatch')
        require(type(actual) is bytes or
                (actual is raw_view and isinstance(raw_view, RawBytesView)),
                row['id'] + ': expected bytes or the exact original RawBytesView')
        require(bytes(actual) == hex_bytes(row['expected_hex']),
                row['id'] + ': complete source byte mismatch')
    auth.check()
    require(counts == {'eels_dataclass': 52, 'dependency_sparse': 3, 'mathematical': 6},
            'complete source/mathematical classification')
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-target', type=Path, required=True)
    parser.add_argument('--eels', type=Path)
    args = parser.parse_args()
    rows = load_inventory()
    check_target(args.check_target.read_text(), rows)
    counts = source_replay(args.eels.resolve(), rows) if args.eels else None
    print(json.dumps({'native_literal_matches': len(rows), 'source_counts': counts}, sort_keys=True))


if __name__ == '__main__':
    main()
