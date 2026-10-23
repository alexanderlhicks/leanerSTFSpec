#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact Uint wire observations against authenticated ethereum-rlp 0.1.6.

Run frozen EELS/.venv/bin/python -I -B, --eels EELS --output EXTERNAL/file.lean.
The interpreter, startup, frozen installation, RECORD, Lean compiler/kernel and
core runtime remain trusted. This finite profile proves no generic Python,
schema/host-depth, EEST/guest or resource correspondence. --helpers-only checks
admission fixtures without executing any source encode/decode entry call.
"""
import hashlib
import importlib.util
import inspect
import json
import marshal
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
_here = Path(__file__).resolve()
sys.path.insert(0, str(_here.parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder, require_type


def nat_input(n):
    require_type(n, int)
    if n < 0:
        raise TypeError("negative Nat input")
    return n


def uint_result(value, uint):
    # Type admission MUST precede conversion (bool/int equality is insufficient).
    require_type(value, uint)
    n = int(value)
    return nat_input(n)


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
RAW_NAMES = {'decode_to','decode','decode_to_bytes','decode_to_sequence','decode_joined_encodings','decode_item_length'}


def admit(record):
    """Finite source-site observation relation; never a source parser/model."""
    if not record['exact'] or not record['authenticated']:
        raise ValueError("wrong exception class/code")
    frames, cause = record['frames'], record['cause']
    if cause is None:
        if record['context'] or record['suppressed'] or not frames or frames[0] != ['decode_to',167]:
            raise ValueError("invalid raw provenance")
        if any(name not in RAW_NAMES or (name == 'decode_to' and line != 167) for name,line in frames):
            raise ValueError("invalid raw chain")
        name, site = frames[-1]
        if site not in RAW or name != RAW_FUNCTIONS[site] or tuple(record['args']) != RAW[site][0]:
            raise ValueError("unadmitted raw raise")
        return RAW[site][1], 'raw', site
    if (frames != [['decode_to',171]] or tuple(record['args']) != ("cannot decode into `Uint`",)
            or not record['suppressed'] or not record['context_same_cause']
            or not cause['exact'] or not cause['authenticated'] or cause['cause'] is not None
            or cause['context'] or cause['suppressed']):
        raise ValueError("invalid typed wrapper/cause")
    chain = cause['frames']
    if chain[:2] != [['decode_to',169],['deserialize_to',205]] or len(chain) != 3:
        raise ValueError("invalid typed dispatch")
    if chain[-1] == ['_deserialize_to_uint',269] and tuple(cause['args']) == ('invalid uint',):
        return '.shape "integer"', 'typed', 269
    if chain[-1] == ['_deserialize_to_uint',271] and tuple(cause['args']) == ('non-canonical integer',):
        return '.nonCanonical "integer leading zero"', 'typed', 271
    raise ValueError("unexpected typed constructor/host failure")


def helper_controls(uint, u64, u256, error):
    class IntSubclass(int):
        pass
    class UintSubclass(uint):
        pass
    class BytesSubclass(bytes):
        pass
    def rejects(fn, value):
        try:
            fn(value)
        except (TypeError, ValueError):
            return
        raise RuntimeError("negative helper fixture accepted")
    for v in [True,0,1,u64(1),u256(1),IntSubclass(1),UintSubclass(1),b'',BytesSubclass(b'')]:
        rejects(lambda x: uint_result(x,uint),v)
    for v in [True,0,bytearray(),memoryview(b''),'',[],(),BytesSubclass(b'')]:
        rejects(lambda x: require_type(x,bytes),v)
    for v in [True,-1,1.0,'1',b'1',uint(1),u64(1),IntSubclass(1)]:
        rejects(nat_input,v)
    if uint_result(uint(1),uint) != 1 or nat_input(0) != 0:
        raise RuntimeError("positive numeric admission failed")
    require_type(b'',bytes)
    # Primitive fixture records test the same admission function as real records;
    # no source binding is replaced and no source operation manufactures a case.
    raw = dict(exact=True,authenticated=True,frames=[['decode_to',167],['decode',149]],
               args=['Cannot decode empty bytestring'],cause=None,context=False,suppressed=False,
               context_same_cause=False)
    inner = dict(exact=True,authenticated=True,frames=[['decode_to',169],['deserialize_to',205],
                 ['_deserialize_to_uint',269]],args=['invalid uint'],cause=None,context=False,suppressed=False)
    outer = dict(exact=True,authenticated=True,frames=[['decode_to',171]],args=['cannot decode into `Uint`'],
                 cause=inner,context=True,suppressed=True,context_same_cause=True)
    import copy
    fixtures=[]
    x=copy.deepcopy(raw);x['exact']=False;x['fixture_class']='DecodingError subclass';fixtures.append(x)
    for name in ['ValueError','NotImplementedError','RecursionError']:
        x=copy.deepcopy(outer);x['cause']['exact']=False;x['cause']['fixture_class']=name;fixtures.append(x)
    x=copy.deepcopy(outer);x['cause']=None;fixtures.append(x)
    x=copy.deepcopy(outer);x['args']=['wrong'];fixtures.append(x)
    x=copy.deepcopy(outer);x['authenticated']=False;fixtures.append(x)
    x=copy.deepcopy(raw);x['cause']=inner;fixtures.append(x)
    for fixture in fixtures:
        rejects(admit,fixture)
    if admit(raw) != ('.empty','raw',149) or admit(outer) != ('.shape "integer"','typed',269):
        raise RuntimeError("positive exception admission failed")
    return dict(type_negatives=25,exception_negatives=8,positive_controls=5)


def main():
    helpers_only = '--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context = setup_driver(__doc__,__file__,5029)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed != 5029:
        context.parser.error("use frozen -I -B and the released seed5029")
    if any(n.split('.',1)[0] == 'ethereum_rlp' for n in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth=RlpSourceAuth(context)
    sys.meta_path.insert(0,RlpFreshFinder(auth))
    from ethereum_rlp import rlp
    from ethereum_rlp import exceptions
    from ethereum_types import numeric
    from ethereum_types.numeric import Uint, U64, U256
    context.check_source(rlp,'ethereum_rlp/rlp.py',dependency=True)
    source_uint, source_error = Uint, rlp.DecodingError
    names=['decode_to','decode','deserialize_to','encode','_deserialize_to_uint',
           'decode_to_bytes','decode_to_sequence','decode_joined_encodings','decode_item_length']
    functions={n:getattr(rlp,n) for n in names}
    saved_codes={n:f.__code__ for n,f in functions.items()}
    rlp_path=Path(rlp.__file__).absolute()
    # Recompile authenticated current bytes and structurally bind each saved code
    # to its original named function in that code, not merely to a matching path.
    compiled=compile(rlp_path.read_bytes(),str(rlp_path),'exec')
    originals={c.co_name:c for c in compiled.co_consts if inspect.iscode(c)}
    for n,c in saved_codes.items():
        if c != originals[n]:
            raise ImportError('source function code differs: '+n)
    class_bindings={n:getattr(Uint,n) for n in ['__init__','__int__','from_be_bytes','_in_range']}
    class_codes={n:(f.__func__ if inspect.ismethod(f) else f).__code__ for n,f in class_bindings.items()}
    exception_init=source_error.__init__
    exception_str=source_error.__str__
    # Bind inherited numeric constructors/conversions and the exception renderer
    # to original code freshly compiled from authenticated package source too.
    def fresh_codes(path):
        source = Path(path).absolute()
        code = compile(source.read_bytes(), str(source), 'exec', dont_inherit=True)
        result = {}
        def visit(c):
            result[c.co_qualname] = c
            for child in c.co_consts:
                if inspect.iscode(child):
                    visit(child)
        visit(code)
        return result
    numeric_codes = fresh_codes(numeric.__file__)
    exception_codes = fresh_codes(exceptions.__file__)
    for name, code in class_codes.items():
        if code != numeric_codes.get(code.co_qualname):
            raise ImportError('Uint path differs from original code: ' + name)
    if exception_str.__code__ != exception_codes.get(exception_str.__code__.co_qualname):
        raise ImportError('DecodingError renderer differs from original code')
    source_inventory={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected}
    def identities():
        if (rlp.Uint is not source_uint or numeric.Uint is not source_uint or
                rlp.DecodingError is not source_error or exceptions.DecodingError is not source_error or
                source_error.__init__ is not exception_init or
                source_error.__str__ is not exception_str):
            raise ImportError('source class binding drift')
        for n,f in functions.items():
            if getattr(rlp,n) is not f or f.__code__ is not saved_codes[n] or f.__globals__ is not rlp.__dict__:
                raise ImportError('source function binding drift: '+n)
        for n,c in class_codes.items():
            f=getattr(source_uint,n);f=f.__func__ if inspect.ismethod(f) else f
            if f.__code__ is not c:
                raise ImportError('Uint conversion/constructor drift: '+n)
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
    closure()
    helpers=helper_controls(Uint,U64,U256,source_error)
    if helpers_only:
        closure();print(json.dumps(dict(profile='helpers-only',**helpers),sort_keys=True));return 0
    def trace(exc):
        frames=[];authenticated=True;all_frames=[]
        tb=exc.__traceback__
        while tb:
            c=tb.tb_frame.f_code
            all_frames.append(dict(file=c.co_filename,function=c.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()))
            if c.co_filename == str(rlp_path):
                frames.append([c.co_name,tb.tb_lineno])
                if c.co_name not in saved_codes or saved_codes[c.co_name] is not c:
                    authenticated=False
            elif c is not observe.__code__:
                authenticated=False
            tb=tb.tb_next
        return dict(exact=type(exc) is source_error,authenticated=authenticated,frames=frames,
            traceback=all_frames,args=list(exc.args),message=str(exc),
            cause=trace(exc.__cause__) if exc.__cause__ is not None else None,
            context=exc.__context__ is not None,suppressed=exc.__suppress_context__,
            context_same_cause=exc.__cause__ is not None and exc.__cause__ is exc.__context__)
    guards=['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base']
    records=[];encode_calls=0;accepted=0
    def enc(model):
        nonlocal encode_calls
        identities();wire=functions['encode'](model);identities();require_type(wire,bytes)
        encode_calls+=1
        return wire
    def construct(n):
        nat_input(n);identities();value=source_uint(n);require_type(value,source_uint);identities();return value
    def observe(case,wire,family,expected=None):
        nonlocal accepted
        require_type(wire,bytes);identities()
        record=dict(id=case,family=family,wire=list(wire),wire_hex=wire.hex())
        try:
            value=functions['decode_to'](source_uint,wire)
        except Exception as exc:
            identities();observation=trace(exc)
            error,phase,site=admit(observation)
            if expected is not None and (error,phase,site) != expected:
                raise RuntimeError('case-specific source provenance differs: '+case)
            result=f'(Except.error ({error}) : Except RlpError Nat)'
            record.update(result='error',diagnostic=error,phase=phase,site=site,exception=observation)
        else:
            if expected is not None:
                raise RuntimeError("expected case-specific rejection: " + case)
            identities();n=uint_result(value,source_uint);accepted+=1
            result=f'(Except.ok {n} : Except RlpError Nat)'
            record.update(result='ok',value=n,type=type(value).__module__+'.'+type(value).__qualname__)
        chunks = [list(wire[i:i+64]) for i in range(0,len(wire),64)]
        expr=(f'decodeTo (α := Nat) (ByteArray.mk '
              f'(({chunks} : List (List UInt8)).flatten.toArray))')
        guard=(f'#guard (match ({expr}), {result} with | .ok a, .ok b => decide (a = b) '
               '| .error a, .error b => decide (a = b) | _, _ => false)')
        record['guard']=guard;guards.append(guard+' -- '+case);records.append(record)
    rawhex=['','81','8201','b8','b900','f8','f900','b838','f838','bf'+'ff'*8,'ff'+'ff'*8,
            '8000','c000','818000','c18000','0001','0100','8100','817f','b800','f800','b90038',
            'f90038','b801','f801','b83700','f83700','c181','c28100','c2b801']
    rawsites=[149,399,399,411,411,442,442,421,454,421,454,401,437,401,437,397,397,404,404,
              413,444,413,444,418,449,418,449,477,404,477]
    for i,(h,site) in enumerate(zip(rawhex,rawsites),1):
        observe(f'W-R{i:02}',bytes.fromhex(h),'literal-raw',(RAW[site][1],'raw',site))
    ns=[0,1,2,127,128,129,255,256,257,1024,0x01000203,2**64-1,2**64,2**64+1,
        2**256-1,2**256,2**256+1,*[2**(8*k)+0x010003 for k in [54,55,254,255,256]]]
    saved=[]
    for i,n in enumerate(ns,1):
        wire=enc(construct(n));saved.append(wire);observe(f'W-N{i:02}',wire,'Uint-encoding')
    models=[[],[b''],[[b'']],[b'\x01',b'\x02',b'\x03'],[b'']*56,[b'']*256,
            b'\x00',b'\x00\x01',b'\x00\x00\x01',bytes(56)]
    for i,model in enumerate(models,1):
        site=269 if i<=6 else 271
        error='.shape "integer"' if i<=6 else '.nonCanonical "integer leading zero"'
        observe(f'W-T{i:02}',enc(model),'typed-negative',(error,'typed',site))
    for i,width in enumerate([0,1,2,3,54,55,56,57,255,256,257,1024],1):
        observe(f'W-B{i:02}',enc(bytes((73*j+19)%256 for j in range(width))),'byte-width')
    for i,depth in enumerate([1,2,4,8,16,24,32],1):
        model=b'\x01\x00\x80'
        for _ in range(depth):model=[model]
        observe(f'W-D{i:02}',enc(model),'list-depth',('.shape "integer"','typed',269))
    for i,width in enumerate([0,1,2,3,55,56,255,256],1):
        observe(f'W-L{i:02}',enc([b'']*width),'list-width',('.shape "integer"','typed',269))
    rng=random.Random(5029)
    for i in range(1,129):
        width=rng.randrange(0,65)
        observe(f'W-Q{i:03}',bytes(rng.randrange(256) for _ in range(width)),'random-raw')
    for i,wire in enumerate(saved):
        for j,mutant in enumerate([wire[:-1],wire+b'\x00',wire+b'\xff']):
            observe(f'W-M{3*i+j+1:02}',mutant,'Nat-wire-mutation')
    if len(records)!=283 or encode_calls!=59 or max(len(r['wire']) for r in records)!=1027:
        raise RuntimeError('released profile count/extent differs')
    closure()
    identity=dict(functions={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in saved_codes.items()},
        uint_codes={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in class_codes.items()},
        sources=source_inventory,rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
        types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest())
    observation_path=context.output.with_suffix('.observations.json')
    observation_path.write_text(json.dumps(dict(seed=5029,cases=records,identities=identity,
        helpers=helpers,encode_calls=encode_calls,decode_to_calls=len(records),accepted=accepted,
        rejected=len(records)-accepted,max_wire=1027,max_depth=32,max_width=256),indent=2)+'\n')
    closure()
    exit_code=context.run(guards,counts=dict(encode=encode_calls,decode_to=len(records),
        accepted=accepted,rejected=len(records)-accepted,**helpers),
        identity=identity,observations=str(observation_path),domain='exact Uint wire; finite released profile')
    closure()
    return exit_code


if __name__=='__main__':
    raise SystemExit(main())
