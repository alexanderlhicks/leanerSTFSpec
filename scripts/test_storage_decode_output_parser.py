"""Bounded positive/negative tests of the strict reader, using frozen math rows."""
import json
from pathlib import Path
import importlib.util
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("storage_decode_reader",
    ROOT / "STFSpec/Conformance/StateCommit/storage_decode_differential.py")
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
check, Rejected = reader.check, reader.Rejected

p=Path(__file__).resolve().parent
expected=reader.expected_bytes()
recipe_spec = importlib.util.spec_from_file_location("storage_decode_recipe",
    ROOT / "STFSpec/Conformance/StateCommit/storage_decode_recipe.py")
recipe = importlib.util.module_from_spec(recipe_spec)
recipe_spec.loader.exec_module(recipe)
constructed = recipe.build()
constructed_expected = b"".join((json.dumps({k: row[k] for k in
    ("id", "raw_hex", "result")}, separators=(",", ":"), ensure_ascii=True)
    + "\n").encode("ascii") for row in constructed)
if constructed_expected != expected:
    raise RuntimeError("frozen mathematical recipe/expectation disagreement")
constructed_input = b"".join((json.dumps({k: row[k] for k in ("id", "raw_hex")},
    separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii") for row in constructed)
if constructed_input != (
        ROOT / "STFSpec/Conformance/StateCommit/storage_decode_inputs.jsonl").read_bytes():
    raise RuntimeError("frozen mathematical recipe/input disagreement")
lines=expected.splitlines(keepends=True)
rows=[json.loads(x) for x in lines]
def pack(xs):
    return b''.join((json.dumps(x,separators=(',',':'))+'\n').encode() for x in xs)
def change(i,key,value):
    xs=json.loads(json.dumps(rows)); xs[i][key]=value
    return pack(xs)
def result(value):
    return change(2,'result',value)
variants={
 'missing-final-lf':expected[:-1], 'crlf':expected.replace(b'\n',b'\r\n'),
 'blank-row':expected+b'\n', 'extra-row':expected+lines[0],
 'missing-row':b''.join(lines[:-1]), 'swapped-rows':b''.join([lines[1],lines[0]]+lines[2:]),
 'duplicate-collapse':b''.join(lines[:-4]),
 'duplicate-reorder':b''.join(lines[:-4]+[lines[-3],lines[-4],lines[-2],lines[-1]]),
 'bool-success':result({'ok':True}), 'float-success':result({'ok':1.0}),
 'string-success':result({'ok':'1'}), 'null-success':result({'ok':None}),
 'negative-success':result({'ok':-1}), 'overflow-success':result({'ok':2**256}),
 'wrong-integer':result({'ok':2}), 'partial-byte-value':change(5,'result',{'ok':0}),
 'fine-error':change(0,'result',{'error':'leadingZero'}),
 'extra-result-field':change(0,'result',{'error':'WitnessError.malformed.leaf','ok':0}),
 'id-change':change(0,'id','different'), 'bytes-change':change(2,'raw_hex','02'),
 'hex-upper':change(4,'raw_hex','7F'), 'hex-odd':change(2,'raw_hex','1'),
 'hex-space':change(2,'raw_hex','01 '), 'hex-prefix':change(2,'raw_hex','0x01'),
 'wire-array':change(2,'raw_hex',[1]),
 'extra-field':expected.replace(b'{"id":',b'{"extra":0,"id":',1),
 'duplicate-key':expected.replace(b'{"id":',b'{"id":"shadow","id":',1),
 'result-duplicate-key':expected.replace(b'{"ok":1}',b'{"ok":0,"ok":1}',1),
 'field-reorder':expected.replace(b'{"id":"raw-empty","raw_hex":""',
                                 b'{"raw_hex":"","id":"raw-empty"',1),
 'json-whitespace':b' '+expected, 'garbage-tail':expected+b'x',
 'nonfinite':expected.replace(b'{"ok":1}',b'{"ok":NaN}',1),
 'float-exponent':expected.replace(b'{"ok":1}',b'{"ok":1e0}',1),
}
# A byte late in a multi-byte wire must be preserved, including all leading/trailing zeros.
i=next(i for i,r in enumerate(rows) if r['id']=='width-32-high-then-zero')
variants['late-wire-byte']=change(i,'raw_hex',rows[i]['raw_hex'][:-2]+'01')
variants['truncated-wire']=change(i,'raw_hex',rows[i]['raw_hex'][:-2])
variants['endianness-value']=change(i,'result',{'ok':128})
report=[]
for name,actual in variants.items():
    try:
        check(expected,actual)
    except Rejected as e:
        report.append({'control':name,'rejected':True,'reason':str(e)})
    else:
        raise RuntimeError('control unexpectedly accepted: '+name)
n=check(expected,expected)
print(json.dumps({'positive_rows':n,'negative_controls':report},sort_keys=True,
                 separators=(',',':')))
