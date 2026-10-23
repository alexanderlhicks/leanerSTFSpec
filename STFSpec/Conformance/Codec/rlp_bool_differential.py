#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact builtin Bool wire observations against authenticated ethereum-rlp 0.1.6.

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


def bool_input(value):
    require_type(value, bool)
    return value


def bool_result(value, expected):
    # Both exact types are admitted before equality or observation.
    bool_input(value)
    bool_input(expected)
    if value != expected:
        raise ValueError('complete Bool result differs')
    return value


def byte_result(value, expected):
    require_type(value, bytes)
    require_type(expected, bytes)
    if value != expected:
        raise ValueError('complete byte result differs')
    return value


def model_observation(value):
    # This observes the actual original source value, never a substitute parser.
    if type(value) is bytes:
        return dict(constructor='bytes', type='builtins.bytes', bytes=list(value))
    require_type(value, list)
    return dict(constructor='list', type='builtins.list',
                children=[model_observation(child) for child in value])


def admit(record):
    """Finite exception observation relation; no source parser/model replacement."""
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
    if (frames != [['decode_to',171]] or tuple(record['args']) != ('cannot decode into `bool`',)
            or not record['suppressed'] or not record['context_same_cause']
            or not record['context'] or not cause['exact'] or not cause['authenticated']
            or cause['cause'] is not None or cause['context'] or cause['suppressed']):
        raise ValueError('invalid typed wrapper/cause')
    if (cause['frames'] != [['decode_to',169],['deserialize_to',209],['_deserialize_to_bool',251]]
            or tuple(cause['args']) != ('invalid boolean',)):
        raise ValueError('unexpected typed constructor/reflection/host failure')
    value = cause['frame_value']
    observed = model_observation(value)
    if type(value) is bytes and value in (b'', b'\x01'):
        raise ValueError('typed failure claims accepted Bool model')
    if observed != cause['value_observation']:
        raise ValueError('original frame value observation differs')
    return '.shape "boolean"', 'typed', 251


def helper_controls(error):
    class IntSubclass(int):
        pass
    class BytesSubclass(bytes):
        pass
    class ErrorSubclass(error):
        pass
    results = []
    def rejects(label, fn, value, fixture):
        try:
            fn(value)
        except (TypeError, ValueError):
            results.append(dict(id=label, admission='rejected', fixture=fixture))
            return
        raise RuntimeError('negative admission fixture accepted: '+label)
    values = [0,1,-1,0.0,1.0,None,b'',bytearray(),'',[],IntSubclass(1)]
    for i,value in enumerate(values):
        fixture=dict(type=type(value).__module__+'.'+type(value).__qualname__, repr=repr(value))
        rejects(f'BI{i:02}', bool_input, value, fixture)
        rejects(f'BR{i:02}', lambda x: bool_result(x,False), value, fixture)
    for i,value in enumerate([False,0,bytearray(),memoryview(b''),'',[],(),BytesSubclass(b'')]):
        rejects(f'BY{i:02}', lambda x: require_type(x,bytes), value,
                dict(type=type(value).__qualname__))
    raw = dict(exact=True,authenticated=True,frames=[['decode_to',167],['decode',149]],
        args=['Cannot decode empty bytestring'],cause=None,context=False,suppressed=False,
        context_same_cause=False)
    inner = dict(exact=True,authenticated=True,frames=[['decode_to',169],['deserialize_to',209],
        ['_deserialize_to_bool',251]],args=['invalid boolean'],cause=None,context=False,
        suppressed=False,frame_value=b'\x02',value_observation=model_observation(b'\x02'))
    outer = dict(exact=True,authenticated=True,frames=[['decode_to',171]],
        args=['cannot decode into `bool`'],cause=inner,context=True,suppressed=True,
        context_same_cause=True)
    fixtures = []
    event=copy.deepcopy(raw);event['exact']=type(ErrorSubclass()) is error
    fixtures.append(('exception-subclass',event))
    event=copy.deepcopy(outer);event['cause']=None;fixtures.append(('missing-cause',event))
    event=copy.deepcopy(outer);event['cause']['exact']=False
    fixtures.append(('wrong-cause-class',event))
    event=copy.deepcopy(outer);event['args']=['wrong'];fixtures.append(('wrong-outer-args',event))
    event=copy.deepcopy(outer);event['cause']['authenticated']=False
    event['cause']['frames'][1]=['deserialize_to',207];fixtures.append(('wrong-dispatch-code',event))
    event=copy.deepcopy(outer);event['cause']['frame_value']=bytearray(b'\x02')
    fixtures.append(('invalid-frame-class',event))
    for label,value in [('accepted-empty',b''),('accepted-01',b'\x01')]:
        event=copy.deepcopy(outer);event['cause']['frame_value']=value
        event['cause']['value_observation']=model_observation(value);fixtures.append((label,event))
    for i,(label,event) in enumerate(fixtures):
        fixture=copy.deepcopy(event)
        if fixture['cause'] is not None:
            value=fixture['cause'].pop('frame_value')
            fixture['cause']['frame_value_fixture']=dict(type=type(value).__qualname__,repr=repr(value))
        rejects(f'EX{i:02}',admit,event,dict(label=label,primitive_fixture=True,record=fixture))
    rejects('VALUE00', lambda x: bool_result(x,True), False, dict(actual=False,expected=True))
    for value in [False,True]:
        bool_input(value);bool_result(value,value)
    require_type(b'',bytes);byte_result(b'\x01',b'\x01')
    if admit(raw) != ('.empty','raw',149) or admit(outer) != ('.shape "boolean"','typed',251):
        raise RuntimeError('positive exception controls failed')
    list_event=copy.deepcopy(outer);list_event['cause']['frame_value']=[b'\x01',[b'']]
    list_event['cause']['value_observation']=model_observation(list_event['cause']['frame_value'])
    if admit(list_event) != ('.shape "boolean"','typed',251):
        raise RuntimeError('positive original-list fixture failed')
    if len(results) != 39:
        raise RuntimeError('released helper budget differs')
    return dict(bool_negatives=22,byte_negatives=8,exception_negatives=8,value_negatives=1,
        total_negatives=39,positive_controls=9,negative_results=results,
        synthetic_events='labeled primitive helper fixtures only; no source entry calls')


def catalog():
    models = [False,True,b'\x00',b'\x02',b'\x7f',b'\x80',b'\xff',b'\x00\x01',
        b'\x01\x00',b'\x01\x01',b'\x73'*55,b'\x73'*56,b'\x73'*256,
        [],[b''],[b'\x01'],[[b'\x01']],[b'']*56]
    raw = ['','81','8201','b8','b900','f8','f900','b838','f838','bf'+'ff'*8,'ff'+'ff'*8,
        '8000','c000','818000','c18000','0001','0100','8100','817f','b800','f800','b90038',
        'f90038','b801','f801','b83700','f83700','c181','c28100','c2b801']
    sites = [149,399,399,411,411,442,442,421,454,421,454,401,437,401,437,397,397,404,404,
        413,444,413,444,418,449,418,449,477,404,477]
    return models,raw,sites


def main():
    helpers_only = '--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context = setup_driver(__doc__,__file__,29301)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed != 29301:
        context.parser.error('use frozen -I -B and the released seed29301')
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
    source_bytes, source_bool, source_error = Bytes, bool, rlp.DecodingError
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
    for site in [*RAW,171,251]:
        if not lines[site-1].lstrip().startswith('raise '):
            raise ImportError('catalog site is not an original raise: '+str(site))
    def identities():
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
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
    closure()
    helpers = helper_controls(source_error)
    if helpers_only:
        closure();print(json.dumps(dict(profile='helpers-only',**helpers),sort_keys=True));return 0
    def trace(exc):
        frames, all_frames, authenticated = [],[],True
        frame_value = None
        has_value = False
        tb = exc.__traceback__
        while tb:
            c = tb.tb_frame.f_code
            all_frames.append(dict(file=c.co_filename,function=c.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()))
            if c.co_filename == str(rlp_path):
                frames.append([c.co_name,tb.tb_lineno])
                if c.co_name == '_deserialize_to_bool' and tb.tb_lineno == 251:
                    frame_value = tb.tb_frame.f_locals['value']
                    has_value = True
                if saved_codes.get(c.co_name) is not c:
                    authenticated = False
            elif c is not observe.__code__:
                authenticated = False
            tb = tb.tb_next
        result = dict(exact=type(exc) is source_error,authenticated=authenticated,frames=frames,
            traceback=all_frames,args=list(exc.args),message=str(exc),
            cause=trace(exc.__cause__) if exc.__cause__ is not None else None,
            context=exc.__context__ is not None,suppressed=exc.__suppress_context__,
            context_same_cause=exc.__cause__ is not None and exc.__cause__ is exc.__context__)
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
    guards = ['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base']
    records = []
    call_path = context.output.with_suffix('.calls.jsonl')
    if call_path.exists():
        raise FileExistsError('fresh call evidence destination required')
    def retain(event):
        with call_path.open('a') as out:
            out.write(json.dumps(serializable(event),sort_keys=True)+'\n')
    counts = dict(encode=0,decode=0,decode_ok=0,raw_error=0,typed_error=0)
    def lean_bytes(data):
        chunks = [list(data[i:i+64]) for i in range(0,len(data),64)]
        return f'(ByteArray.mk (({chunks} : List (List UInt8)).flatten.toArray))'
    def lean_model(value):
        if type(value) is bytes:
            return '(.bytes '+lean_bytes(value)+')'
        require_type(value,list)
        return '(.list ['+', '.join(lean_model(x) for x in value)+'])'
    def lean_bool(value):
        bool_input(value)
        return 'true' if value else 'false'
    def enc(case,model,typed):
        if typed:
            bool_input(model)
            observation=dict(constructor='bool',type='builtins.bool',value=model)
            expr='encodeOf '+lean_bool(model)
        else:
            observation=model_observation(model)
            expr='encode '+lean_model(model)
        identities()
        wire=functions['encode'](model)
        require_type(wire,bytes);identities()
        retain(dict(id=case,operation='encode',input=observation,exact_bytes=True,wire=list(wire)))
        if typed:
            byte_result(wire,b'\x01' if model else b'\x80')
        counts['encode'] += 1
        guard=f'#guard {expr} = {lean_bytes(wire)}'
        guards.append(guard+' -- '+case)
        records.append(dict(id=case,operation='encode',input=observation,wire=list(wire),
            wire_hex=wire.hex(),result='ok',type='builtins.bytes',guard=guard,
            lean_expression=expr,source_observation=dict(constructor='bytes',bytes=list(wire))))
        return wire
    def observe(case,wire,payload=None,expected=None):
        require_type(wire,bytes);identities();counts['decode'] += 1
        record=dict(id=case,operation='decode_to',wire=list(wire),wire_hex=wire.hex())
        try:
            value=functions['decode_to'](source_bool,wire)
        except Exception as exc:
            identities();event=trace(exc)
            error,phase,site=admit(event)
            retain(dict(id=case,operation='decode_to',wire=list(wire),exception=event))
            if expected is None or (error,phase,site) != expected:
                raise RuntimeError('case-specific source rejection differs: '+case)
            result=f'(Except.error ({error}) : Except RlpError Bool)'
            counts[phase+'_error'] += 1
            record.update(result='error',diagnostic=error,phase=phase,site=site,
                exception=serializable(event),
                source_observation=dict(constructor='DecodingError',event=serializable(event)),
                common_channel=dict(type='Except Unit Bool',constructor='error',unit=True))
        else:
            identities();bool_input(value)
            if expected is not None or payload is None:
                raise RuntimeError('unexpected source success: '+case)
            value=bool_result(value,payload)
            retain(dict(id=case,operation='decode_to',wire=list(wire),exact_bool=True,value=value))
            counts['decode_ok'] += 1
            result=f'(Except.ok {lean_bool(value)} : Except RlpError Bool)'
            record.update(result='ok',value=value,type='builtins.bool',
                source_observation=dict(constructor='bool',value=value),
                common_channel=dict(type='Except Unit Bool',constructor='ok',value=value))
        expr=f'decodeTo (α := Bool) {lean_bytes(wire)}'
        guard=(f'#guard (match ({expr}), {result} with | .ok a, .ok b => decide (a = b) '
               '| .error a, .error b => decide (a = b) | _, _ => false)')
        record.update(lean_result=result,lean_expression=expr,guard=guard,
            lean_common_expression=f'({expr}).mapError (fun (_ : RlpError) => ())')
        records.append(record);guards.append(guard+' -- '+case)
    models,raw,sites=catalog()
    for i,model in enumerate(models,1):
        typed=i<=2
        wire=enc(f'B-W{i:02}-encode',model,typed)
        observe(f'B-W{i:02}',wire,payload=model if typed else None,
                expected=None if typed else ('.shape "boolean"','typed',251))
    for i,(h,site) in enumerate(zip(raw,sites),19):
        observe(f'B-W{i:02}',bytes.fromhex(h),expected=(RAW[site][1],'raw',site))
    if counts != dict(encode=18,decode=48,decode_ok=2,raw_error=30,typed_error=16):
        raise RuntimeError('released profile count differs: '+str(counts))
    if len(records)!=66 or len(guards)!=68 or max(len(r['wire']) for r in records)!=259:
        raise RuntimeError('released profile cardinality/extent differs')
    closure()
    identity = dict(functions={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in saved_codes.items()},
        Bool=dict(module=source_bool.__module__,name=source_bool.__name__,builtin_identity=True,
                  resolution='original encode/deserialize_to function builtins',
                  constructor_trust='native interpreter builtin'),
        Bytes=dict(module=source_bytes.__module__,name=source_bytes.__name__,builtin_identity=True,
                   alias_source='ethereum_types/bytes.py:165',constructor_trust='native interpreter builtin'),
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected},
        rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
        types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest())
    observation_path = context.output.with_suffix('.observations.json')
    observation_path.write_text(json.dumps(dict(seed=29301,cases=records,identities=identity,
        helpers=helpers,counts=counts,total_success=20,max_supplied_wire=259,max_payload=256,
        max_list_depth=2,max_list_width=56,max_declared_payload=2**64-1,
        success_reencoding='private public-law clients prove encodeOf result = original wire'),indent=2)+'\n')
    closure()
    result = context.run(guards,counts=dict(**counts,total_success=20,**helpers),identity=identity,
        observations=str(observation_path),domain='exact builtin Bool; single finite released profile')
    closure()
    return result


if __name__ == '__main__':
    raise SystemExit(main())
