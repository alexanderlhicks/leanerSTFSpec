#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact builtin Bytes wire observations against authenticated ethereum-rlp 0.1.6.

Run frozen EELS/.venv/bin/python -I -B, --eels EELS --output EXTERNAL/file.lean.
Interpreter/startup, frozen installation/RECORD, compiler/kernel, native runtime
and ambient host remain trusted. This single bounded profile establishes no
Python refinement, host/resource, EEST or guest theorem. --helpers-only executes
local admission controls without source encode/decode entry calls.
"""
import copy
import hashlib
import inspect
import json
import marshal
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder, require_type


RAW = {
    149: (("Cannot decode empty bytestring",), '.empty'),
    397: (("negative length",), '.nonCanonical "negative length"'),
    **{n: (("truncated",), '.truncated') for n in [399,411,421,435,442,454,477,520,536]},
    **{n: (("trailing bytes",), '.trailing') for n in [401,423,437,456]},
    404: ((), '.nonCanonical "prefixed single byte"'),
    **{n: ((), '.nonCanonical "leading zero length"') for n in [413,444,522,538]},
    **{n: ((), '.nonCanonical "long form for short payload"') for n in [418,449]},
}
RAW_FUNCTIONS = {149:'decode',397:'decode_to_bytes',399:'decode_to_bytes',401:'decode_to_bytes',
    404:'decode_to_bytes',411:'decode_to_bytes',413:'decode_to_bytes',418:'decode_to_bytes',
    421:'decode_to_bytes',423:'decode_to_bytes',435:'decode_to_sequence',437:'decode_to_sequence',
    442:'decode_to_sequence',444:'decode_to_sequence',449:'decode_to_sequence',454:'decode_to_sequence',
    456:'decode_to_sequence',477:'decode_joined_encodings',520:'decode_item_length',
    522:'decode_item_length',536:'decode_item_length',538:'decode_item_length'}
RAW_NAMES = {'decode_to','decode','decode_to_bytes','decode_to_sequence',
             'decode_joined_encodings','decode_item_length'}


def byte_result(value, expected):
    # Admit the exact result type before any equality operation.
    require_type(value, bytes)
    require_type(expected, bytes)
    if value != expected:
        raise ValueError('complete byte result differs')
    return value


def admit(record):
    """Finite exception observation relation; no wire parser or source substitute."""
    if not record['exact'] or not record['authenticated']:
        raise ValueError('wrong exception class/code')
    frames, cause = record['frames'], record['cause']
    if cause is None:
        if record['context'] or record['suppressed'] or not frames or frames[0] != ['decode_to',167]:
            raise ValueError('invalid raw provenance')
        if any(n not in RAW_NAMES or (n == 'decode_to' and line != 167) for n,line in frames):
            raise ValueError('invalid raw chain')
        name, site = frames[-1]
        if site not in RAW or name != RAW_FUNCTIONS[site] or tuple(record['args']) != RAW[site][0]:
            raise ValueError('unadmitted raw raise')
        return RAW[site][1], 'raw', site
    if (frames != [['decode_to',171]] or tuple(record['args']) != ('cannot decode into `bytes`',)
            or not record['suppressed'] or not record['context_same_cause']
            or not record['context'] or not cause['exact'] or not cause['authenticated']
            or cause['cause'] is not None or cause['context'] or cause['suppressed']):
        raise ValueError('invalid typed wrapper/cause')
    if (cause['frames'] != [['decode_to',169],['deserialize_to',207],['_deserialize_to_bytes',258]]
            or tuple(cause['args']) != ('invalid bytes',)):
        raise ValueError('unexpected typed constructor/reflection/host failure')
    return '.shape "bytes"', 'typed', 258


def helper_controls(error):
    class BytesSubclass(bytes):
        pass
    class Convertible:
        def __bytes__(self):
            raise RuntimeError('conversion must not run')
        def __eq__(self, other):
            raise RuntimeError('equality must not run before type admission')
    def rejects(fn, value):
        try:
            fn(value)
        except (TypeError, ValueError):
            return
        raise RuntimeError('negative admission fixture accepted')
    values = [None,False,0,[],(),'',bytearray(),memoryview(b''),BytesSubclass(b''),
              [0],(0,),Convertible()]
    for value in values:
        rejects(lambda x: byte_result(x,b''), value)
    byte_result(b'',b'')
    raw = dict(exact=True,authenticated=True,frames=[['decode_to',167],['decode',149]],
        args=['Cannot decode empty bytestring'],cause=None,context=False,suppressed=False,
        context_same_cause=False)
    fixtures = []
    for exc in [RecursionError(),MemoryError(),ValueError(),AssertionError(),TypeError(),
                NotImplementedError()]:
        event = copy.deepcopy(raw)
        event.update(exact=type(exc) is error,fixture_class=type(exc).__qualname__)
        fixtures.append(event)
    event = copy.deepcopy(raw)
    event.update(authenticated=False,frames=[['unknown',1]],fixture_class='synthetic DecodingError')
    fixtures.append(event)
    event = copy.deepcopy(raw)
    event['frames'] = [['decode_to',171],['decode',149]]
    fixtures.append(event)
    for event in fixtures:
        rejects(admit,event)
    rejects(lambda x: byte_result(x,b'\x01'), b'\x00')
    if admit(raw) != ('.empty','raw',149):
        raise RuntimeError('positive raw admission failed')
    return dict(type_negatives=12,exception_negatives=8,value_negatives=1,
        positive_controls=2,synthetic_events='controller negatives only',
        negative_results=[dict(id=f'T{i:02}',admission='rejected') for i in range(12)]+
            [dict(id=f'E{i:02}',admission='rejected',event=event)
             for i,event in enumerate(fixtures)]+
            [dict(id='V00',admission='rejected',actual_hex='00',expected_hex='01')])


def catalog():
    payloads = [b'',b'\x00',b'\x01',b'\x7f',b'\x80',b'\xff',b'\x00\x01',b'\x00\x00\x01',
        b'\x01\x00',bytes.fromhex('01008000ff7f'),bytes(55),bytes([128])*56,bytes(255),
        bytes((73*i+19)%256 for i in range(256))]
    wires = [bytes.fromhex(h) for h in ['80','00','01','7f','8180','81ff','820001','83000001',
        '820100','8601008000ff7f']]+[b'\xb7'+payloads[10],b'\xb8\x38'+payloads[11],
        b'\xb8\xff'+payloads[12],b'\xb9\x01\x00'+payloads[13]]
    lists = ['c0','c180','c100','c2c1c0','c480c08180','f7'+'80'*55,'f838'+'80'*56]
    raw = ['','0506','81','8205','8000','8105','810500','b900','b90040','b805','b838',
        'b838'+'80'*56+'00','bf'+'ff'*8,'c1','c000','f900','f90040','f805','f838',
        'f838'+'80'*56+'00','ff'+'ff'*8,'c28200','c181','c28100','c38100','c2810000',
        'c481008100','c3b90038','c2b805','c7b805'+'00'*5,'c1b8','c1f8','c3f90038']
    sites = [149,397,399,399,401,404,401,411,413,418,421,423,421,435,437,442,444,449,
             454,456,454,477,477,404,435,437,404,522,477,418,520,536,538]
    return payloads,wires,lists,raw,sites


def main():
    helpers_only = '--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context = setup_driver(__doc__,__file__,29201)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed != 29201:
        context.parser.error('use frozen -I -B and the released seed29201')
    if sys.version_info[:2] != (3,13):
        context.parser.error('the released oracle interpreter is Python3.13')
    if any(n.split('.',1)[0] == 'ethereum_rlp' for n in sys.modules):
        raise ImportError('ethereum_rlp imported before authentication')
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0,RlpFreshFinder(auth))
    from ethereum_rlp import rlp, exceptions
    from ethereum_types import bytes as bytes_module
    from ethereum_types.bytes import Bytes
    context.check_source(rlp,'ethereum_rlp/rlp.py',dependency=True)
    context.check_source(bytes_module,'ethereum_types/bytes.py',dependency=True)
    source_bytes, source_error = Bytes, rlp.DecodingError
    if Bytes is not bytes or Bytes.__module__ != 'builtins' or Bytes.__name__ != 'bytes':
        raise ImportError('original Bytes is not builtin bytes')
    rlp_path = Path(rlp.__file__).absolute()
    compiled = compile(rlp_path.read_bytes(),str(rlp_path),'exec')
    originals = {c.co_name:c for c in compiled.co_consts if inspect.iscode(c)}
    functions = {n:getattr(rlp,n) for n in originals if inspect.isfunction(getattr(rlp,n,None))}
    saved_codes = {n:f.__code__ for n,f in functions.items()}
    for n,c in saved_codes.items():
        if c != originals[n] or c.co_filename != str(rlp_path):
            raise ImportError('original source code differs: '+n)
    exception_init, exception_str = source_error.__init__, source_error.__str__
    def fresh_codes(path):
        source = Path(path).absolute()
        codes = {}
        def visit(c):
            codes[c.co_qualname] = c
            for child in c.co_consts:
                if inspect.iscode(child):
                    visit(child)
        visit(compile(source.read_bytes(),str(source),'exec',dont_inherit=True))
        return codes
    exception_codes = fresh_codes(exceptions.__file__)
    if exception_str.__code__ != exception_codes.get(exception_str.__code__.co_qualname):
        raise ImportError('DecodingError renderer differs from original code')
    # Verify each released first-raise citation against the actual authenticated text.
    lines = rlp_path.read_text().splitlines()
    for site in [*RAW,171,258]:
        if not lines[site-1].lstrip().startswith('raise '):
            raise ImportError('catalog site is not an original raise: '+str(site))
    def identities():
        if (source_bytes is not bytes or rlp.Bytes is not source_bytes
                or bytes_module.Bytes is not source_bytes or rlp.DecodingError is not source_error
                or exceptions.DecodingError is not source_error
                or source_error.__init__ is not exception_init or source_error.__str__ is not exception_str):
            raise ImportError('source alias/class binding drift')
        for n,f in functions.items():
            if getattr(rlp,n) is not f or f.__code__ is not saved_codes[n] or f.__globals__ is not rlp.__dict__:
                raise ImportError('source function/code binding drift: '+n)
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
    closure()
    helpers = helper_controls(source_error)
    if helpers_only:
        closure();print(json.dumps(dict(profile='helpers-only',**helpers),sort_keys=True));return 0
    def trace(exc):
        frames, all_frames, authenticated = [],[],True
        tb = exc.__traceback__
        while tb:
            c = tb.tb_frame.f_code
            all_frames.append(dict(file=c.co_filename,function=c.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()))
            if c.co_filename == str(rlp_path):
                frames.append([c.co_name,tb.tb_lineno])
                if saved_codes.get(c.co_name) is not c:
                    authenticated = False
            elif c is not observe.__code__:
                authenticated = False
            tb = tb.tb_next
        return dict(exact=type(exc) is source_error,authenticated=authenticated,frames=frames,
            traceback=all_frames,args=list(exc.args),message=str(exc),
            cause=trace(exc.__cause__) if exc.__cause__ is not None else None,
            context=exc.__context__ is not None,suppressed=exc.__suppress_context__,
            context_same_cause=exc.__cause__ is not None and exc.__cause__ is exc.__context__)
    guards = ['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base']
    records = []
    call_path = context.output.with_suffix('.calls.jsonl')
    if call_path.exists():
        raise FileExistsError('fresh call evidence destination required')
    def retain(event):
        with call_path.open('a') as out:
            out.write(json.dumps(event,sort_keys=True)+'\n')
    counts = dict(encode=0,decode=0,decode_ok=0,raw_error=0,typed_error=0)
    def lean_bytes(data):
        chunks = [list(data[i:i+64]) for i in range(0,len(data),64)]
        return f'(ByteArray.mk (({chunks} : List (List UInt8)).flatten.toArray))'
    def enc(case,payload,expected=None):
        require_type(payload,bytes);identities()
        wire = functions['encode'](source_bytes(payload))
        retain(dict(id=case,operation='encode',payload=list(payload),
                    exact_bytes=type(wire) is bytes,
                    wire=list(wire) if type(wire) is bytes else None))
        require_type(wire,bytes);identities()
        if expected is not None:
            byte_result(wire,expected)
        counts['encode'] += 1
        guard = f'#guard encodeOf {lean_bytes(payload)} = {lean_bytes(wire)}'
        guards.append(guard+' -- '+case)
        records.append(dict(id=case,operation='encode',payload=list(payload),payload_hex=payload.hex(),
            wire=list(wire),wire_hex=wire.hex(),result='ok',type='builtins.bytes',guard=guard,
            source_observation=dict(constructor='bytes',bytes=list(wire))))
        return wire
    def observe(case,wire,payload=None,expected=None):
        require_type(wire,bytes);identities();counts['decode'] += 1
        record = dict(id=case,operation='decode_to',wire=list(wire),wire_hex=wire.hex())
        try:
            value = functions['decode_to'](source_bytes,wire)
        except Exception as exc:
            identities();event = trace(exc)
            retain(dict(id=case,operation='decode_to',wire=list(wire),exception=event))
            error,phase,site = admit(event)
            if expected is None or (error,phase,site) != expected:
                raise RuntimeError('case-specific source rejection differs: '+case)
            result = f'(Except.error ({error}) : Except RlpError ByteArray)'
            counts[phase+'_error'] += 1
            record.update(result='error',diagnostic=error,phase=phase,site=site,exception=event,
                source_observation=dict(constructor='DecodingError',event=event),
                common_channel=dict(type='Except Unit ByteArray',constructor='error',unit=True))
        else:
            retain(dict(id=case,operation='decode_to',wire=list(wire),
                        exact_bytes=type(value) is bytes,
                        value=list(value) if type(value) is bytes else None))
            identities();require_type(value,bytes)
            if expected is not None or payload is None:
                raise RuntimeError('unexpected source success: '+case)
            value = byte_result(value,payload);counts['decode_ok'] += 1
            result = f'(Except.ok {lean_bytes(value)} : Except RlpError ByteArray)'
            record.update(result='ok',value=list(value),value_hex=value.hex(),type='builtins.bytes',
                source_observation=dict(constructor='bytes',bytes=list(value)),
                common_channel=dict(type='Except Unit ByteArray',constructor='ok',bytes=list(value)))
        expr = f'decodeTo (α := ByteArray) {lean_bytes(wire)}'
        guard = (f'#guard (match ({expr}), {result} with | .ok a, .ok b => decide (a = b) '
                 '| .error a, .error b => decide (a = b) | _, _ => false)')
        record.update(lean_result=result,lean_expression=expr,guard=guard,
            lean_common_expression=f'({expr}).mapError (fun (_ : RlpError) => ())')
        records.append(record);guards.append(guard+' -- '+case)
    payloads,wires,lists,raw,sites = catalog()
    for i,(payload,wire) in enumerate(zip(payloads,wires)):
        enc(f'P{i:02}-encode',payload,wire)
        observe(f'P{i:02}-decode',wire,payload=payload)
    for i,h in enumerate(lists):
        observe(f'L{i:02}',bytes.fromhex(h),expected=('.shape "bytes"','typed',258))
    for i,(h,site) in enumerate(zip(raw,sites)):
        observe(f'R{i:02}',bytes.fromhex(h),expected=(RAW[site][1],'raw',site))
    rng = random.Random(29201)
    for width in [0,1,2,7,8,31,32,55,56,127,255,256]:
        for trial in range(4):
            payload = bytes(rng.randrange(256) for _ in range(width))
            case = f'G{width:03}-{trial}'
            wire = enc(case+'-encode',payload)
            observe(case+'-decode',wire,payload=payload)
            low = len(wire)==1 and wire[0]<128
            drop_site = 149 if len(wire)==1 else (399 if width<56 else 421)
            append_site = 397 if low else (401 if width<56 else 423)
            observe(case+'-drop-last',wire[:-1],expected=(RAW[drop_site][1],'raw',drop_site))
            observe(case+'-append00',wire+b'\x00',expected=(RAW[append_site][1],'raw',append_site))
    if counts != dict(encode=62,decode=198,decode_ok=62,raw_error=129,typed_error=7):
        raise RuntimeError('released profile count differs: '+str(counts))
    if len(records)!=260 or len(guards)!=262 or max(len(r['wire']) for r in records)!=260:
        raise RuntimeError('released profile cardinality/extent differs')
    closure()
    identity = dict(functions={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in saved_codes.items()},
        Bytes=dict(module=source_bytes.__module__,name=source_bytes.__name__,builtin_identity=True,
                   alias_source='ethereum_types/bytes.py:165',constructor_trust='native interpreter builtin'),
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected},
        rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
        types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest())
    observation_path = context.output.with_suffix('.observations.json')
    observation_path.write_text(json.dumps(dict(seed=29201,cases=records,identities=identity,
        helpers=helpers,counts=counts,total_success=124,max_supplied_wire=260,max_payload=256,
        max_list_depth=3,max_list_width=56,max_declared_payload=2**64-1,
        success_reencoding='private public-law clients prove encodeOf result = original wire'),indent=2)+'\n')
    closure()
    result = context.run(guards,counts=dict(**counts,total_success=124,**helpers),identity=identity,
        observations=str(observation_path),domain='exact builtin Bytes; single finite released profile')
    closure()
    return result


if __name__ == '__main__':
    raise SystemExit(main())
