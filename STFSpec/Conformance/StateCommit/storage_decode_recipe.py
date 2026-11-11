"""Finite mathematical construction. No decoder, target import, or source observation."""
import argparse
import json
from pathlib import Path

ERROR = {'error': 'WitnessError.malformed.leaf'}


def canon(payload, is_list=False):
    n = len(payload)
    if not is_list and n == 1 and payload[0] < 128:
        return payload
    if n < 56:
        return bytes([(192 if is_list else 128) + n]) + payload
    digits = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    return bytes([(247 if is_list else 183) + len(digits)]) + digits + payload


def build():
    rows = []

    def add(name, raw, result, derivation):
        rows.append({'id': name, 'raw_hex': raw.hex(), 'result': result,
                     'derivation': derivation})

    def payload(name, b):
        ok = len(b) <= 32 and (not b or b[0] != 0)
        # This finite base-256 sum is a mathematical expectation, not target output.
        n = sum(byte * 256 ** (len(b) - 1 - j) for j, byte in enumerate(b))
        add(name, canon(b), {'ok': n} if ok else ERROR.copy(),
            'Canonical byte item; '
            + ('minimal width <=32; full base-256 sum' if ok else 'leading zero or width >32'))

    def bad(name, b, why):
        add(name, b, ERROR.copy(), why)

    bad('raw-empty', b'', 'No complete RLP item exists')
    for name, b in [
        ('zero', b''), ('one', b'\x01'), ('127', b'\x7f'), ('128', b'\x80'),
        ('255', b'\xff'), ('raw-zero', b'\x00'),
    ]:
        payload(name, b)
    for k in range(256):
        n = 2 ** k
        payload('single-bit-%03d' % k, n.to_bytes((k + 8) // 8, 'big'))
    payload('u256-max', b'\xff' * 32)
    for n in (31, 32, 33):
        for name, b in [
            ('ones', b'\x01' * n),
            ('high-then-zero', b'\x80' + b'\x00' * (n - 1)),
            ('zero-then-one', b'\x00' * (n - 1) + b'\x01'),
            ('all-zero', b'\x00' * n),
        ]:
            payload('width-%d-%s' % (n, name), b)
    for pos in range(32):
        b = bytearray(range(1, 33))
        b[pos] = 128
        payload('asymmetric-high-%02d' % pos, bytes(b))
        b = bytearray(range(1, 33))
        b[pos] = 0
        payload('asymmetric-zero-%02d' % pos, bytes(b))
        b = bytearray(32)
        b[pos] = 1
        payload('single-byte-position-%02d' % pos, bytes(b))
    for n in (55, 56, 57, 255, 256, 257):
        for leading in (0, 1):
            payload('boundary-bytes-%d-leading-%d' % (n, leading),
                    bytes([leading]) + b'\xa5' * (n - 1))
        bad('boundary-list-%d' % n, canon(b'\x80' * n, True),
            'Complete canonical list; typed byte shape fails')
        raw = canon(b'\x01' * n)
        bad('boundary-bytes-%d-truncated' % n, raw[:-1],
            'Declared payload exceeds complete input; raw parse fails before width check')
        bad('boundary-bytes-%d-trailing' % n, raw + b'\x00',
            'Trailing byte; raw parse fails before width check')
    for name, b in [
        ('empty', b''), ('one-empty-byte', b'\x80'), ('one-list', b'\xc0'),
        ('two-values', b'\x01\x02'), ('nested', canon(canon(b'', True), True)),
    ]:
        bad('list-' + name, canon(b, True), 'Complete canonical list; typed byte shape fails')
    for name, h in [
        ('child-short', 'c181'),
        ('child-overrun', 'c28280'),
        ('child-long-under56', 'c3b80101'),
        ('child-leading-length-zero', 'c4b9003801'),
        ('child-nonminimal-singleton', 'c28101'),
        ('nested-child-truncated', 'c2c181'),
        ('list-long-under56', 'f80180'),
        ('list-leading-length-zero', 'f90038'),
    ]:
        bad('malformed-list-' + name, bytes.fromhex(h),
            'Raw RLP grammar failure inside list or its framing; no typed result')
    for tag in range(0x81, 0xc0):
        bad('prefix-only-%02x' % tag, bytes([tag]),
            'Missing declared string payload or length digits')
    for tag in range(0xc1, 0x100):
        bad('prefix-only-%02x' % tag, bytes([tag]),
            'Missing declared list payload or length digits')
    for k in range(1, 9):
        for is_list in (False, True):
            tag = (247 if is_list else 183) + k
            for available in range(k):
                # Eight triangular small header families, no payload Cartesian product.
                bad('length-digit-trunc-%s-%d-%d'
                    % ('list' if is_list else 'bytes', k, available),
                    bytes([tag]) + b'\x01' * available, 'Incomplete long length digits')
    for name, h in [
        ('singleton-zero', '8100'),
        ('singleton-one', '8101'),
        ('singleton-127', '817f'),
        ('long-empty', 'b800'),
        ('long-one', 'b80101'),
        ('long-55', 'b837' + '01' * 55),
        ('length-zero-prefix', 'b90038' + '01' * 56),
        ('overlong-width', 'b90021' + '01' * 33),
        ('huge-declared', 'bfffffffffffffffff'),
        ('two-zero-items', '8080'),
        ('single-trailing', '0100'),
        ('list-trailing', 'c080'),
    ]:
        bad('noncanonical-' + name, bytes.fromhex(h),
            'Nonminimal header/singleton, truncation, or trailing bytes; raw parse fails')
    for name, b in [
        ('valid32', b'\x01' + b'\x00' * 31),
        ('leading32', b'\x00' + b'\x01' * 31),
        ('wide33', b'\x01' * 33),
    ]:
        raw = canon(b)
        bad('paired-' + name + '-trailing', raw + b'\x80',
            'Raw complete-item failure precedes potential typed check')
        bad('paired-' + name + '-truncated', raw[:-1],
            'Raw truncation precedes potential typed check')
    # Deliberate exact duplicate rows retain identity, order, cardinality and wire bytes.
    rows += [dict(rows[0]), dict(rows[1]), dict(rows[2]), dict(rows[-1])]
    return rows


def emit(path):
    path.mkdir(exist_ok=True)
    rows = build()

    def write(name, xs):
        (path / name).write_bytes(b''.join(
            (json.dumps(x, separators=(',', ':'), ensure_ascii=True) + '\n').encode('ascii')
            for x in xs))

    write('catalogue.jsonl', rows)
    write('input.jsonl', [{'id': r['id'], 'raw_hex': r['raw_hex']} for r in rows])
    write('expected.jsonl',
          [{'id': r['id'], 'raw_hex': r['raw_hex'], 'result': r['result']} for r in rows])
    print(json.dumps({
        'rows': len(rows),
        'successes': sum('ok' in r['result'] for r in rows),
        'errors': sum('error' in r['result'] for r in rows),
        'duplicate_tail': 4,
    }, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output_dir', metavar='OUTPUT_DIR', type=Path,
                        help='directory that receives catalogue.jsonl, input.jsonl '
                             'and expected.jsonl')
    args = parser.parse_args()
    emit(args.output_dir)


if __name__ == '__main__':
    main()
