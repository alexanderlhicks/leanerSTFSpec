#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact original U256 wire observations against authenticated ethereum-rlp 0.1.6.

Run frozen EELS/.venv/bin/python -I -B with --eels EELS --output EXTERNAL/file.lean
and --wheel-dir WHEELS. Supply these exact original locked files in WHEELS:
ethereum_rlp-0.1.6-py3-none-any.whl and ethereum_types-0.4.1-py3-none-any.whl.
The explicit directory has no private fallback or network download.
Interpreter/startup, frozen installation/RECORD, compiler/kernel, native runtime
and ambient host remain trusted. This single bounded profile establishes no
Python refinement, host/resource, EEST or guest theorem. --helpers-only executes
local admission controls without source encode/decode entry calls.
"""
import argparse
import copy
import zipfile
import tomllib
import hashlib
import inspect
import json
import marshal
from pathlib import Path
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


def numeric_input(value):
    require_type(value, int)
    if not 0 <= value < 2**256:
        raise ValueError('U256 input outside exact range')
    return value


def word_result(value, original):
    # Exact nominal class admission precedes every conversion or equality.
    require_type(value, original)
    return int(value)


def provenance(actual, expected):
    """The same primitive identity/body admission serves live and isolated fixtures."""
    if set(actual) != set(expected):
        raise ValueError('provenance inventory differs')
    for name, wanted in expected.items():
        got = actual[name]
        if name.endswith('_body'):
            if type(got) is not bytes or got != wanted:
                raise ValueError('source body drift: '+name)
        elif got is not wanted:
            raise ValueError('original identity drift: '+name)


def model_observation(value):
    if type(value) is bytes:
        return dict(constructor='bytes',type='builtins.bytes',bytes=list(value))
    require_type(value,list)
    return dict(constructor='list',children=[model_observation(x) for x in value])


def admit(record):
    if not record['exact'] or not record['authenticated']:
        raise ValueError('wrong exception class/code')
    frames,cause=record['frames'],record['cause']
    if cause is None:
        if record['context'] or record['suppressed'] or not frames or frames[0]!=['decode_to',167]:
            raise ValueError('invalid raw provenance')
        if any(n not in RAW_NAMES or (n=='decode_to' and line!=167) for n,line in frames):
            raise ValueError('invalid raw chain')
        name,site=frames[-1]
        if site not in RAW or name!=RAW_FUNCTIONS[site] or tuple(record['args'])!=RAW[site][0]:
            raise ValueError('unadmitted raw raise')
        return RAW[site][1],'raw',site
    if (frames!=[['decode_to',171]] or tuple(record['args'])!=('cannot decode into `U256`',)
            or not record['suppressed'] or not record['context_same_cause']
            or not record['context'] or not cause['exact'] or not cause['authenticated']):
        raise ValueError('invalid typed wrapper')
    prefix=[['decode_to',169],['deserialize_to',205]]
    for site,args,error in [(269,('invalid uint',),'.shape "integer"'),
            (271,('non-canonical integer',),'.nonCanonical "integer leading zero"')]:
        if cause['frames']==prefix+[['_deserialize_to_uint',site]]:
            if (tuple(cause['args'])!=args or cause['cause'] is not None or cause['context']
                    or cause['suppressed']):
                raise ValueError('wrong typed cause')
            value=cause['frame_value']
            observed=model_observation(value)
            if (site==269 and type(value) is not list) or (site==271 and
                    (type(value) is not bytes or not value or value[0]!=0)):
                raise ValueError('typed original value differs')
            if observed!=cause['value_observation']:
                raise ValueError('typed model observation differs')
            return error,'typed',site
    terminal=cause['cause']
    if (cause['frames']!=prefix+[['_deserialize_to_uint',275]] or cause['args']!=[]
            or not cause['suppressed'] or not cause['context_same_cause'] or not cause['context']
            or terminal is None or not terminal['exact_value_error'] or not terminal['authenticated']
            or terminal['frames']!=[['_deserialize_to_uint',273],['from_be_bytes',575]]
            or terminal['cause'] is not None or terminal['context'] or terminal['suppressed']):
        raise ValueError('unexpected typed native/class/reflection/width origin')
    value=terminal['frame_value']
    require_type(value,bytes)
    if len(value)<=32 or value[0]==0 or terminal['args']!=[f'expected at most 32 but got {len(value)}']:
        raise ValueError('invalid width terminal')
    if terminal['value_observation']!=model_observation(value):
        raise ValueError('width original value differs')
    return '.shape "integer width"','typed',575


def helper_controls(original, Uint, U64, expected):
    class WordSubclass(original):
        pass
    results=[]
    def reject(label,fn,value,fixture):
        try:
            fn(value)
        except (TypeError,ValueError):
            results.append(dict(id=label,result='rejected',fixture=fixture));return
        raise RuntimeError('negative fixture accepted: '+label)
    for i,value in enumerate([True,False,-1,2**256,1.0,'1',b'\x01',Uint(1),U64(1),WordSubclass(1)]):
        reject(f'NI{i:02}',numeric_input,value,dict(type=type(value).__qualname__,repr=repr(value)))
    for i,value in enumerate([bytearray(),memoryview(b''),'',[],None]):
        reject(f'WI{i:02}',lambda x: require_type(x,bytes),value,dict(type=type(value).__qualname__))
    for i,value in enumerate([True,1,Uint(1),U64(1),WordSubclass(1)]):
        reject(f'SR{i:02}',lambda x: word_result(x,original),value,dict(type=type(value).__qualname__))
    for i,name in enumerate(['rlp_body','numeric_body','encode','decode_to','deserialize_to','U256','from_be_bytes']):
        fixture=dict(expected);fixture[name]=b'isolated changed body' if name.endswith('_body') else object()
        reject(f'PV{i:02}',lambda x: provenance(x,expected),fixture,
            dict(label=name,isolated_primitive_fixture=True,shared_runtime_mutation=False))
    terminal=dict(exact=False,exact_value_error=True,authenticated=True,
        frames=[['_deserialize_to_uint',273],['from_be_bytes',575]],args=['expected at most 32 but got 33'],
        cause=None,context=False,suppressed=False,frame_value=b'\x01'+b'\x00'*32,
        value_observation=model_observation(b'\x01'+b'\x00'*32))
    inner=dict(exact=True,authenticated=True,frames=[['decode_to',169],['deserialize_to',205],
        ['_deserialize_to_uint',275]],args=[],cause=terminal,context=True,suppressed=True,
        context_same_cause=True)
    outer=dict(exact=True,authenticated=True,frames=[['decode_to',171]],
        args=['cannot decode into `U256`'],cause=inner,context=True,suppressed=True,context_same_cause=True)
    if admit(outer)!=('.shape "integer width"','typed',575):
        raise RuntimeError('positive width fixture failed')
    bad=copy.deepcopy(outer);bad['cause']['cause']['frames'][-1][-1]=577
    reject('PV07',admit,bad,dict(label='wrong-width-terminal',isolated_primitive_fixture=True))
    provenance(dict(expected),expected)
    for value in [0,1,2**256-1]:
        numeric_input(value)
        if word_result(original(value),original)!=value:
            raise RuntimeError('positive exact word control failed')
    require_type(b'',bytes)
    if len(results)!=28:
        raise RuntimeError('helper budget differs')
    return dict(total_negatives=28,numeric=10,wire=5,success=5,provenance=8,
        negative_results=results,source_entries=0,positive_controls=6)


def catalog():
    # Released bounded fixture header catalog, never a general encoder/parser.
    widths=[0,1,2,3,4,7,8,9,15,16,17,23,24,30,31,32,
        33,34,35,40,55,56,63,64,127,128,255,256]
    headers={k: bytes([128+k]) if k<56 else
        bytes([184,k]) if k<256 else bytes.fromhex('b90100') for k in widths}
    def fixture(payload):
        require_type(payload,bytes)
        if len(payload) not in headers:
            raise ValueError('fixture width outside catalog')
        return payload if len(payload)==1 and payload[0]<128 else headers[len(payload)]+payload
    numbers=[0,1,2,127,128,129,255,256,257,1024,0x010002,0x01008000ff7f,
        2**16-1,2**16,2**32-1,2**32,2**64-1,2**64,2**128-1,2**128,
        2**248-1,2**248,2**255,2**256-1]
    success=[]
    for width in widths[:16]:
        payload=bytes([1]+[0 if j%2==0 else (17*j)%256 for j in range(1,width)]) if width else b''
        success.append((fixture(payload),int.from_bytes(payload,'big')))
    nested=b'\x80'
    for i in range(1,33):
        nested=bytes([192+i])+nested
    shape=[bytes.fromhex(x) for x in ['c0','c100','c180','c20102','c1c0','c2c100']]
    shape += [nested,bytes.fromhex('f840')+b'\x80'*64]
    zeros=[fixture(b'\x00' if k==1 else b'\x00'*(k-1)+b'\x01') for k in [1,2,3,4,7,8,9,16,31,32,33,64]]
    wide=[fixture(b'\x01'+b'\x00'*(k-1)) for k in [33,34,35,40,55,56,63,64,127,128,255,256]]
    raw=['','0506','81','8205','8000','8105','810500','b900','b90040','b805','b838',
        'b838'+'80'*56+'00','bf'+'ff'*8,'c1','c000','f900','f90040','f805','f838',
        'f838'+'80'*56+'00','ff'+'ff'*8,'c28200','c181','c28100']
    sites=[149,397,399,399,401,404,401,411,413,418,421,423,421,435,437,442,444,449,454,456,454,477,477,404]
    return numbers,success,shape,zeros,wide,[(bytes.fromhex(h),site) for h,site in zip(raw,sites)]


def main():
    # Compose only this driver's extra input with the unchanged shared CLI.
    wheel_parser=argparse.ArgumentParser(add_help=False)
    wheel_parser.add_argument('--wheel-dir',type=Path,metavar='WHEELS')
    wheel_args,remaining=wheel_parser.parse_known_args()
    if '--help' in remaining or '-h' in remaining:
        # Help exits before shared reference setup, imports or acquisition.
        help_parser = argparse.ArgumentParser(description=__doc__)
        help_parser.add_argument('--eels', type=Path, required=True)
        help_parser.add_argument('--output', type=Path, required=True)
        help_parser.add_argument('--seed', type=int, default=29401)
        help_parser.add_argument('--wheel-dir', type=Path, metavar='WHEELS', required=True)
        help_parser.add_argument(
            '--helpers-only', action='store_true',
            help='run local admission controls without source encode/decode entries')
        help_parser.parse_args()
        return 0

    if '--help' not in remaining and '-h' not in remaining:
        if wheel_args.wheel_dir is None:
            wheel_parser.error('--wheel-dir WHEELS is required; see --help for exact filenames')
        if not wheel_args.wheel_dir.is_dir():
            wheel_parser.error('--wheel-dir must name an existing wheel directory')
        for name in ['ethereum_rlp-0.1.6-py3-none-any.whl','ethereum_types-0.4.1-py3-none-any.whl']:
            if not (wheel_args.wheel_dir/name).is_file():
                wheel_parser.error('missing original locked wheel: '+name)
    sys.argv=[sys.argv[0],*remaining]
    helpers_only = '--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context = setup_driver(__doc__,__file__,29401)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed != 29401:
        context.parser.error('use frozen -I -B and the released seed29401')
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
    from ethereum_types import numeric
    source_bytes, source_bool, source_error = Bytes, bool, rlp.DecodingError
    original = numeric.U256
    numeric_path = Path(numeric.__file__).absolute()
    def resolved_global(function, name):
        if name in function.__globals__:
            return function.__globals__[name]
        return function.__builtins__[name]
    if (resolved_global(rlp.encode,'bool') is not source_bool
            or resolved_global(rlp.deserialize_to,'bool') is not source_bool):
        raise ImportError('source Bool is not original builtin bool')
    aliases = {n:getattr(rlp,n) for n in ['Bytes','FixedBytes','Uint','FixedUnsigned','Sequence']}
    builtins_used = {n:resolved_global(rlp.encode,n)
                     for n in ['bool','bytes','bytearray','str','isinstance']}
    if source_bool.__module__ != 'builtins' or source_bool.__name__ != 'bool':
        raise ImportError('original Bool class differs')
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
    for site in [*RAW,171,269,271,275]:
        if not lines[site-1].lstrip().startswith('raise '):
            raise ImportError('catalog site is not an original raise: '+str(site))
    def rlp_identities():
        if (source_bytes is not bytes or rlp.Bytes is not source_bytes
                or bytes_module.Bytes is not source_bytes or rlp.DecodingError is not source_error
                or exceptions.DecodingError is not source_error
                or source_error.__init__ is not exception_init or source_error.__str__ is not exception_str):
            raise ImportError('source alias/class binding drift')
        for n,v in aliases.items():
            if getattr(rlp,n) is not v:
                raise ImportError('source dispatch class alias drift: '+n)
        for n,v in builtins_used.items():
            if resolved_global(functions['encode'],n) is not v:
                raise ImportError('original builtin binding drift: '+n)
        if resolved_global(functions['deserialize_to'],'bool') is not source_bool:
            raise ImportError('Bool typed dispatch binding drift')
        for n,f in functions.items():
            if getattr(rlp,n) is not f or f.__code__ is not saved_codes[n] or f.__globals__ is not rlp.__dict__:
                raise ImportError('source function/code binding drift: '+n)
    numeric_codes=fresh_codes(numeric_path)
    classes={name:getattr(numeric,name) for name in ['Unsigned','FixedUnsigned','Uint','U64','U256']}
    methods={}
    for name in ['__init__','__int__','__index__','__eq__','to_be_bytes','_in_range','from_be_bytes']:
        method=inspect.getattr_static(original,name)
        function=method.__func__ if isinstance(method,classmethod) else method
        if function.__code__!=numeric_codes.get(function.__code__.co_qualname):
            raise ImportError('numeric inherited method code differs: '+name)
        methods[name]=(method,function,function.__code__)
    if original.__bases__!=(numeric.FixedUnsigned,) or numeric.FixedUnsigned.__bases__!=(numeric.Unsigned,):
        raise ImportError('original numeric class hierarchy differs')
    maximum=original.MAX_VALUE
    require_type(maximum,original)
    if int(maximum)!=2**256-1:
        raise ImportError('original MAX_VALUE differs')
    expected=dict(rlp_body=rlp_path.read_bytes(),numeric_body=numeric_path.read_bytes(),
        encode=rlp.encode,decode_to=rlp.decode_to,deserialize_to=rlp.deserialize_to,
        U256=original,from_be_bytes=inspect.getattr_static(original,'from_be_bytes'))
    def identities():
        rlp_identities()
        provenance(dict(rlp_body=rlp_path.read_bytes(),numeric_body=numeric_path.read_bytes(),
            encode=rlp.encode,decode_to=rlp.decode_to,deserialize_to=rlp.deserialize_to,
            U256=numeric.U256,from_be_bytes=inspect.getattr_static(original,'from_be_bytes')),expected)
        for name,cls in classes.items():
            if getattr(numeric,name) is not cls:
                raise ImportError('numeric class binding drift')
        for name,(method,function,code) in methods.items():
            if (inspect.getattr_static(original,name) is not method or function.__code__ is not code
                    or function.__globals__ is not numeric.__dict__):
                raise ImportError('inherited numeric binding drift: '+name)
        if original.MAX_VALUE is not maximum or type(maximum) is not original or int(maximum)!=2**256-1:
            raise ImportError('numeric MAX_VALUE drift')
    # Current source/RECORD admission is supplemented by lock-hashed wheel members.
    lock=tomllib.loads((context.eels/'uv.lock').read_text())
    wheel_receipts=[]
    wheel_dir=wheel_args.wheel_dir.resolve()
    for package,version,folder in [('ethereum-rlp','0.1.6','ethereum_rlp'),('ethereum-types','0.4.1','ethereum_types')]:
        wheel=wheel_dir/(package.replace('-','_')+'-'+version+'-py3-none-any.whl')
        body=wheel.read_bytes();digest=hashlib.sha256(body).hexdigest()
        entries=[p for p in lock['package'] if p['name']==package and p['version']==version]
        if len(entries)!=1 or not any(w['hash']=='sha256:'+digest for w in entries[0]['wheels']):
            raise ImportError('wheel differs from original lock')
        with zipfile.ZipFile(wheel) as archive:
            members=[n for n in archive.namelist() if n.startswith(folder+'/') and n.endswith('.py')]
            for name in members:
                installed=context.eels/'.venv/lib/python3.13/site-packages'/name
                if installed.read_bytes()!=archive.read(name):
                    raise ImportError('installed source differs from lock wheel: '+name)
        wheel_receipts.append(dict(path=str(wheel),sha256=digest,source_members=len(members)))
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
        for row in wheel_receipts:
            if hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()!=row['sha256']:
                raise ImportError('wheel input drift')
    closure()
    if helpers_only:
        helpers=helper_controls(original,numeric.Uint,numeric.U64,expected)
        closure();print(json.dumps(dict(profile='helpers-only',**helpers),sort_keys=True));return 0
    helpers=dict(total_negatives=28,execution='separate normal/-O helper-only runs; no repetition here')
    def trace(exc):
        frames,all_frames,authenticated=[],[],True
        frame_value=None;has_value=False
        tb=exc.__traceback__
        while tb:
            c=tb.tb_frame.f_code
            all_frames.append(dict(file=c.co_filename,function=c.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()))
            if c.co_filename==str(rlp_path):
                frames.append([c.co_name,tb.tb_lineno])
                if saved_codes.get(c.co_name) is not c:
                    authenticated=False
                if c.co_name=='_deserialize_to_uint' and tb.tb_lineno in (269,271):
                    frame_value=tb.tb_frame.f_locals['decoded'];has_value=True
            elif c.co_filename==str(numeric_path):
                frames.append([c.co_name,tb.tb_lineno])
                if methods['from_be_bytes'][2] is not c:
                    authenticated=False
                if tb.tb_lineno==575:
                    frame_value=tb.tb_frame.f_locals['buffer'];has_value=True
            elif c is not observe.__code__:
                authenticated=False
            tb=tb.tb_next
        result=dict(exact=type(exc) is source_error,exact_value_error=type(exc) is ValueError,
            exception_class=type(exc).__module__+'.'+type(exc).__qualname__,
            authenticated=authenticated,frames=frames,traceback=all_frames,args=list(exc.args),
            message=str(exc),cause=trace(exc.__cause__) if exc.__cause__ is not None else None,
            context=exc.__context__ is not None,suppressed=exc.__suppress_context__,
            context_same_cause=exc.__cause__ is not None and exc.__cause__ is exc.__context__,
            context_detail=trace(exc.__context__) if exc.__context__ is not None and exc.__context__ is not exc.__cause__ else None)
        if has_value:
            result.update(frame_value=frame_value,value_observation=model_observation(frame_value))
        return result
    def serializable(value):
        if type(value) is bytes:
            return dict(native_type='builtins.bytes',bytes=list(value),hex=value.hex())
        if type(value) is list:
            return [serializable(x) for x in value]
        if type(value) is dict:
            return {k:serializable(v) for k,v in value.items()}
        return value
    guards=['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base']
    records=[]
    call_path=context.output.with_suffix('.calls.jsonl')
    if call_path.exists():
        raise FileExistsError('fresh call evidence destination required')
    def retain(event):
        with call_path.open('a') as out:
            out.write(json.dumps(serializable(event),sort_keys=True)+'\n')
    counts=dict(encode=0,decode=0,decode_ok=0,raw_error=0,typed_error=0)
    def lean_bytes(data):
        chunks=[list(data[i:i+64]) for i in range(0,len(data),64)]
        return f'(ByteArray.mk (({chunks} : List (List UInt8)).flatten.toArray))'
    def enc(case,number):
        numeric_input(number) # No wrapping/coercion before original construction.
        value=original(number)
        if word_result(value,original)!=number:
            raise ValueError('original construction differs')
        identities();counts['encode']+=1
        wire=functions['encode'](value)
        require_type(wire,bytes);identities()
        event=dict(id=case,operation='encode',input_integer=number,input_class='ethereum_types.numeric.U256',
            wire=list(wire),wire_hex=wire.hex(),result='ok',result_class='builtins.bytes')
        retain(event)
        guard=f'#guard encodeOf (U256.ofNat {number}) = {lean_bytes(wire)}'
        records.append(dict(**event,guard=guard));guards.append(guard+' -- '+case)
        return wire
    def observe(case,wire,number=None,expected_error=None):
        require_type(wire,bytes);identities();counts['decode']+=1
        record=dict(id=case,operation='decode_to',wire=list(wire),wire_hex=wire.hex())
        try:
            value=functions['decode_to'](original,wire)
        except Exception as exc:
            identities();event=trace(exc)
            retain(dict(**record,exception=event))
            error,phase,site=admit(event)
            if expected_error!=(error,phase,site):
                raise RuntimeError('case-specific rejection differs: '+case)
            result=f'(Except.error ({error}) : Except RlpError U256)'
            counts[phase+'_error']+=1
            record.update(result='error',diagnostic=error,phase=phase,site=site,
                exception=serializable(event),common_channel=dict(type='Except Unit U256',constructor='error'))
        else:
            identities()
            actual=word_result(value,original)
            if expected_error is not None or number is None or actual!=numeric_input(number):
                raise RuntimeError('unexpected exact source success: '+case)
            retain(dict(**record,exact_class='ethereum_types.numeric.U256',integer=actual))
            counts['decode_ok']+=1
            result=f'(Except.ok (U256.ofNat {actual}) : Except RlpError U256)'
            record.update(result='ok',value=actual,result_class=type(value).__module__+'.'+type(value).__qualname__,
                common_channel=dict(type='Except Unit U256',constructor='ok',value=actual))
        expr=f'decodeTo (α := U256) {lean_bytes(wire)}'
        guard=(f'#guard (match ({expr}), {result} with | .ok a, .ok b => decide (a = b) '
            '| .error a, .error b => decide (a = b) | _, _ => false)')
        record.update(lean_result=result,lean_expression=expr,guard=guard,
            lean_common_expression=f'({expr}).mapError (fun (_ : RlpError) => ())')
        records.append(record);guards.append(guard+' -- '+case)
    numbers,success,shape,zeros,wide,raw=catalog()
    for i,n in enumerate(numbers):
        wire=enc(f'A{i:02}-encode',n);observe(f'A{i:02}-decode',wire,number=n)
    for i,(wire,n) in enumerate(success):
        observe(f'B{i:02}',wire,number=n)
    errors=[('.shape "integer"',269)]*8+[('.nonCanonical "integer leading zero"',271)]*12+[('.shape "integer width"',575)]*12
    for i,(wire,(error,site)) in enumerate(zip(shape+zeros+wide,errors)):
        observe(f'C{i:02}',wire,expected_error=(error,'typed',site))
    for i,(wire,site) in enumerate(raw):
        observe(f'R{i:02}',wire,expected_error=(RAW[site][1],'raw',site))
    if counts!=dict(encode=24,decode=96,decode_ok=40,raw_error=24,typed_error=32):
        raise RuntimeError('released count differs: '+str(counts))
    if len(records)!=120 or len(guards)!=122 or max(len(r['wire']) for r in records)!=259:
        raise RuntimeError('released cardinality/extent differs')
    closure()
    identity=dict(functions={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in saved_codes.items()},
        U256=dict(module=original.__module__,name=original.__qualname__,exact_original=True,
            bases=[x.__module__+'.'+x.__qualname__ for x in original.__mro__],MAX_VALUE=int(maximum),
            MAX_VALUE_class=type(maximum).__qualname__),
        numeric_methods={n:dict(qualname=c.co_qualname,file=c.co_filename,line=c.co_firstlineno,
            code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,(_,f,c) in methods.items()},
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected},
        rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
        types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest(),wheels=wheel_receipts,
        wheel_directory=dict(supplied=str(wheel_args.wheel_dir),resolved=str(wheel_dir)))
    observation_path=context.output.with_suffix('.observations.json')
    observation_path.write_text(json.dumps(dict(seed=29401,cases=records,identities=identity,helpers=helpers,
        counts=counts,total_success=64,max_payload=256,max_wire=259,max_success_payload=32,
        max_success_wire=33,max_depth=32,max_list_width=64,max_declared_payload=2**64-1),indent=2)+'\n')
    closure()
    result=context.run(guards,counts=dict(**counts,total_success=64),observations=str(observation_path),
        domain='exact original U256; finite seed29401 profile; no RNG draws')
    closure()
    return result


if __name__=='__main__':
    raise SystemExit(main())
