"""Compare complete storage-leaf observations with independently frozen mathematics.

Expectations were frozen on 2026-11-06 before the strict Lean migration, from
CONTRACT O4(e) and EthCodec E1/E2. storage_decode_recipe.py reconstructs the finite
grammar and full radix-256 sums without a parser or source/target imports. The
635 rows retain four exact duplicate tail rows. Original pinned decode_to(U256)
observations separately matched all rows; this checker runs neither that source
nor a guest, backend, account decoder or resource test.
Spec guidance: STFSpec/informal/modules/EthStateCommit.md §§3–7.
"""
import json
import re
import sys
from pathlib import Path

class Rejected(ValueError):
    pass

def require(p,why):
    if not p:
        raise Rejected(why)

def pairs(items):
    d={}
    for k,v in items:
        require(k not in d,'duplicate key')
        d[k]=v
    return d

def no_float(x):
    raise Rejected('floating point or nonfinite constant')

def parse(data):
    require(type(data) is bytes,'bytes required')
    require(bool(data) and data.endswith(b'\n') and b'\r' not in data,'LF framing')
    out=[]
    for line in data[:-1].split(b'\n'):
        require(bool(line),'blank row')
        try:
            x=json.loads(line.decode('ascii'),object_pairs_hook=pairs,parse_float=no_float,parse_constant=no_float)
        except (UnicodeError,json.JSONDecodeError) as e:
            raise Rejected('JSON syntax') from e
        require(type(x) is dict and list(x)==['id','raw_hex','result'],'row fields/order')
        require(type(x['id']) is str and bool(x['id']),'id')
        h=x['raw_hex']
        require(type(h) is str and re.fullmatch(r'(?:[0-9a-f]{2})*',h) is not None,'exact lowercase byte hex')
        r=x['result']; require(type(r) is dict and len(r)==1,'result fields')
        if list(r)==['ok']:
            require(type(r['ok']) is int and 0<=r['ok']<2**256,'full U256 integer')
        elif list(r)==['error']:
            require(type(r['error']) is str and r['error']=='WitnessError.malformed.leaf','coarse error')
        else:
            raise Rejected('result tag')
        canonical=json.dumps(x,separators=(',',':'),ensure_ascii=True).encode('ascii')
        require(line==canonical,'canonical complete row serialization')
        out.append(x)
    return out

def check(expected,actual):
    e=parse(expected); a=parse(actual)
    require(len(e)==len(a),'cardinality')
    require(e==a,'ordered exact rows, bytes, values and duplicates')
    return len(e)

DIRECTORY = Path(__file__).resolve().parent
INPUT_SHA = "a64c7f29efce2839884ed97bb10eeafbfd6eb08b68b43458dc6cce65310c55ee"
EXPECTED_SHA = "e4c992505c607dbe6216cc2d281c0d55796a6b0fca717bcefc717e6c9c1c790f"


def expected_bytes():
    import hashlib
    raw = (DIRECTORY / "storage_decode_inputs.jsonl").read_bytes()
    expected = (DIRECTORY / "storage_decode_expected.jsonl").read_bytes()
    require(hashlib.sha256(raw).hexdigest() == INPUT_SHA, "frozen input provenance")
    require(hashlib.sha256(expected).hexdigest() == EXPECTED_SHA, "frozen expectation provenance")
    rows = parse(expected)
    require(len(rows) == 635, "frozen row count")
    inputs = b"".join((json.dumps({k: r[k] for k in ("id", "raw_hex")},
        separators=(",", ":")) + "\n").encode("ascii") for r in rows)
    require(inputs == raw, "complete frozen input bridge")
    return expected


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path, required=True)
    args = parser.parse_args()
    n = check(expected_bytes(), args.check_target.read_bytes())
    print(f"PASS strict storage decoding: {n} complete ordered rows")


if __name__ == "__main__":
    main()
