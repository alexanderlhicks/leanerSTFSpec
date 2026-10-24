#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact original Bytes20 RLP observations for nominal Lean Address.

Run frozen EELS/.venv/bin/python -I -B with --eels EELS --wheel-dir WHEELS
--output EXTERNAL.lean. Supply original locked ethereum_rlp-0.1.6-py3-none-any.whl
and ethereum_types-0.4.1-py3-none-any.whl explicitly; no fallback/download.
--helpers-only executes 50 negative and nine positive admission fixture groups,
one successful original constructor setup and zero RLP entries. Run normally,
then with -O before the sole seed29801 source profile: 47 entries, no RNG.
Address is statically Bytes20 in EELS state.py:33; no state or crypto module is
imported and no hash is executed. Native/interpreter/startup/install/RECORD,
ambient host, outer orchestration and Lean compiler/kernel remain trusted.
Finite observations are not universal Python, host-resource, EEST or guest proofs.
Full Lean diagnostics and external Except Unit observations remain separate.
"""
import argparse
import builtins
import dataclasses
import hashlib
import inspect
import json
import marshal
from pathlib import Path
import sys
import tomllib
import typing
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder, require_type


RAW = {
    149: (("Cannot decode empty bytestring",), '.empty'),
    397: (("negative length",), '.nonCanonical "negative length"'),
    **{n: (("truncated",), '.truncated') for n in [399,421,435,477]},
    **{n: (("trailing bytes",), '.trailing') for n in [401,437]},
    404: ((), '.nonCanonical "prefixed single byte"'),
    413: ((), '.nonCanonical "leading zero length"'),
    418: ((), '.nonCanonical "long form for short payload"'),
}
RAW_FUNCTIONS = {149:'decode',397:'decode_to_bytes',399:'decode_to_bytes',
    401:'decode_to_bytes',404:'decode_to_bytes',413:'decode_to_bytes',
    418:'decode_to_bytes',421:'decode_to_bytes',435:'decode_to_sequence',
    437:'decode_to_sequence',477:'decode_joined_encodings'}
RAW_NAMES = {'decode_to','decode','decode_to_bytes','decode_to_sequence',
             'decode_joined_encodings','decode_item_length'}
RAW_CASES = [('',149),('0506',397),('81',399),('8205',399),('8000',401),
             ('8105',404),('b90040',413),('b805',418),('b838',421),
             ('c1',435),('c000',437),('c181',477)]
WIDTHS = [20]
LENGTHS = [0,1,2,8,19,21,31,32,55,56,255,256]
HEADERS = {0:b'\x80',1:b'\x81',2:b'\x82',8:b'\x88',19:b'\x93',20:b'\x94',
           21:b'\x95',31:b'\x9f',32:b'\xa0',55:b'\xb7',56:b'\xb8\x38',
           255:b'\xb8\xff',256:b'\xb9\x01\x00'}
SHAPES = [(b'\xc0',[]),(b'\xc1\x00',[b'\x00']),
          (b'\xc1\x80',[b'']),(b'\xc1\xc0',[[]])]


def payload_input(value, width):
    require_type(value, bytes)
    if len(value) != width:
        raise ValueError('input differs from exact fixed width')
    return value


def literal_wire(value):
    require_type(value, bytes)
    return value


def fixed_result(value, original, width):
    # Exact nominal admission always precedes bytes conversion, equality or length.
    require_type(value, original)
    projected = bytes(value)
    payload_input(projected, width)
    return projected


def native_output(value, original, width, source_input, payload, expected_wire):
    # Every width20 encode returns exact builtin bytes; no singleton subclass path.
    literal_wire(value)
    payload_input(payload, width)
    literal_wire(expected_wire)
    if value != expected_wire:
        raise ValueError('complete native output bytes differ')
    return value


def provenance(actual, expected):
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
        return dict(constructor='bytes',bytes=list(value))
    require_type(value, list)
    return dict(constructor='list',children=[model_observation(x) for x in value])


def primitive_event(kind, original, width, payload=b'', shape=None, site=149):
    """Synthetic primitive descriptors test admission, never manufacture source errors."""
    base = dict(exact=True, exact_value_error=False, authenticated=True, frames=[],
        args=[], cause=None, context=False, suppressed=False, context_same_cause=False)
    if kind == 'raw':
        return dict(base, frames=[['decode_to',167],['decode',149]], args=list(RAW[149][0]))
    inner = dict(base, frames=[['decode_to',169],['deserialize_to',207],
        ['_deserialize_to_bytes',258 if kind == 'shape' else 262]],
        target_exact=True, target_token=original, class_tokens=[original,original])
    if kind == 'shape':
        inner.update(args=['invalid bytes'], frame_value=model_observation(shape))
    else:
        terminal = dict(base, exact=False, exact_value_error=True,
            frames=[['_deserialize_to_bytes',260],['__new__',36]],
            args=[f'expected {width} bytes but got {len(payload)}'],
            target_exact=True,target_token=original,class_tokens=[original,original],
            raw_value=payload, native_args=(payload,), native_kwargs={},
            result_token=original,result_bytes=payload,length_token=width,
            native_message=f'expected {width} bytes but got {len(payload)}')
        inner.update(args=[],cause=terminal,context=True,suppressed=True,
                     context_same_cause=True,raw_value=payload)
    return dict(base,frames=[['decode_to',171]],args=[f'cannot decode into `Bytes{width}`'],
        cause=inner,context=True,suppressed=True,context_same_cause=True,
        target_exact=True,target_token=original,class_tokens=[original])


def admit(record, original, width, payload=None, shape=None, wire=None):
    """Live capture and isolated fixtures use the same primitive descriptor admission."""
    if record['exact'] is not True or record['authenticated'] is not True:
        raise ValueError('wrong original exception class/code')
    frames, cause = record['frames'], record['cause']
    if cause is None:
        if (record['context'] or record['suppressed'] or not frames
                or frames[0] != ['decode_to',167]
                or any(n not in RAW_NAMES or (n=='decode_to' and line!=167) for n,line in frames)):
            raise ValueError('invalid raw provenance')
        name, site = frames[-1]
        if site not in RAW or name != RAW_FUNCTIONS[site] or tuple(record['args']) != RAW[site][0]:
            raise ValueError('unadmitted raw raise')
        return RAW[site][1], 'raw', site
    if (frames != [['decode_to',171]] or tuple(record['args']) != (f'cannot decode into `Bytes{width}`',)
            or record['suppressed'] is not True or record['context_same_cause'] is not True
            or record['context'] is not True or cause['exact'] is not True
            or cause['authenticated'] is not True or record.get('target_exact') is not True
            or record.get('target_token') is not original
            or any(x is not original for x in record.get('class_tokens',[]))
            or cause.get('target_token') is not original
            or any(x is not original for x in cause.get('class_tokens',[]))):
        raise ValueError('invalid typed wrapper/target')
    prefix = [['decode_to',169],['deserialize_to',207]]
    if 'outer_decoded' in record:
        wanted = model_observation(shape) if shape is not None else model_observation(payload)
        if record['outer_decoded'] != wanted or cause.get('dispatch_value') != wanted:
            raise ValueError('complete outer/dispatch native value differs')
    if cause['frames'] == prefix+[['_deserialize_to_bytes',258]]:
        if (cause['args'] != ['invalid bytes'] or cause['cause'] is not None
                or cause['context'] or cause['suppressed']
                or cause.get('frame_value') != model_observation(shape)):
            raise ValueError('wrong complete typed shape cause')
        return '.shape "bytes"', 'typed', 258
    terminal = cause['cause']
    if (cause['frames'] != prefix+[['_deserialize_to_bytes',262]] or cause['args'] != []
            or cause['suppressed'] is not True or cause['context_same_cause'] is not True
            or cause['context'] is not True or terminal is None
            or terminal['exact_value_error'] is not True or terminal['authenticated'] is not True
            or terminal['frames'] != [['_deserialize_to_bytes',260],['__new__',36]]
            or terminal['cause'] is not None or terminal['context'] or terminal['suppressed']):
        raise ValueError('unexpected native/class/reflection/host origin')
    literal_wire(payload)
    if (len(payload) == width or terminal['args'] != [f'expected {width} bytes but got {len(payload)}']
            or terminal.get('native_message') != terminal['args'][0]
            or terminal.get('target_token') is not original
            or terminal.get('target_exact') is not True
            or any(x is not original for x in terminal.get('class_tokens',[]))
            or type(terminal.get('raw_value')) is not bytes
            or terminal['raw_value'] != payload or type(cause.get('raw_value')) is not bytes
            or cause['raw_value'] != payload
            or type(terminal.get('native_args')) is not tuple
            or len(terminal['native_args']) != 1
            or type(terminal['native_args'][0]) is not bytes
            or terminal['native_args'][0] != payload
            or type(terminal.get('native_kwargs')) is not dict or terminal['native_kwargs'] != {}
            or terminal.get('result_token') is not original
            or type(terminal.get('result_bytes')) is not bytes or terminal['result_bytes'] != payload
            or type(terminal.get('length_token')) is not int
            or terminal['length_token'] != width or terminal['length_token'] is not original.LENGTH):
        raise ValueError('wrong original constructor length frame')
    if wire is not None:
        literal_wire(wire)
        if wire in (b'\x00', b'\x01', b'\x7f'):
            if cause['raw_value'] is not wire or terminal['raw_value'] is not wire:
                raise ValueError('raw singleton did not retain original builtin wire identity')
    return '.shape "fixed bytes length"', 'typed', 36


def helper_controls(carriers, expected):
    records = []
    def test(case, thunk, negative, details):
        try:
            result = thunk()
        except (TypeError, ValueError) as exc:
            if not negative:
                raise
            records.append(dict(id=case,result='rejected',fixture=details,
                exception=type(exc).__name__,message=str(exc)))
        else:
            if negative:
                raise RuntimeError('helper admitted negative '+case)
            records.append(dict(id=case,result='accepted',fixture=details,observation=result))
    original = carriers[0][2]
    p = bytes(20)
    # Exactly one direct original constructor setup. No failing constructor probes.
    value = original(payload_input(p,20))
    fixed_result(value,original,20)
    def fixture(v):
        # Explicit local fixture observations, never conversion of a live source value.
        row=dict(native_type=type(v).__module__+'.'+type(v).__qualname__)
        if type(v) is bytearray:
            row['bytes']=list(v)
        elif type(v) is memoryview:
            row['bytes']=list(v);row['format']=v.format;row['readonly']=v.readonly
        elif type(v) in (bytes,str,list,bool,int) or v is None:
            row['value']=v
        elif type(v) is original:
            row['original_class']=original;row['bytes']=list(fixed_result(v,original,20))
        else:
            row['sentinel_touches']=dict(touches)
        return row
    bad = [bytearray(),memoryview(b''),'',[],None,True,1]
    for i,v in enumerate(bad):
        test(f'HP{i:02}',lambda v=v:payload_input(v,20),True,
             fixture(v))
    for i,k in enumerate([0,1,19,21,55,256],7):
        q=bytes(k)
        test(f'HP{i:02}',lambda q=q:payload_input(q,20),True,dict(bytes=q,target_width=20))
    test('HP13',lambda:payload_input(p,20),False,dict(bytes=p,target_width=20))
    for i,v in enumerate(bad):
        test(f'HW{i:02}',lambda v=v:literal_wire(v),True,
             fixture(v))
    test('HW07',lambda:literal_wire(b''),False,dict(bytes=b''))
    touches = dict(conversion=0,equality=0)
    class Sentinel:
        def __bytes__(self):
            touches['conversion']+=1
            raise RuntimeError('conversion before exact native admission')
        def __eq__(self,other):
            touches['equality']+=1
            raise RuntimeError('equality before exact native admission')
    sentinel=Sentinel()
    for i,v in enumerate([p,bytearray(20),memoryview(p),'',False,0,None,sentinel]):
        test(f'HS{i:02}',lambda v=v:fixed_result(v,original,20),True,
             fixture(v))
    records[-1]['sentinel_touches']=dict(touches)
    if touches != dict(conversion=0,equality=0):
        raise RuntimeError('success sentinel observed before admission')
    test('HS08',lambda:fixed_result(value,original,20),False,dict(original_class=original,bytes=p))
    for i,key in enumerate(['rlp_body','bytes_body','encode','decode_to','deserialize_to',
                             'FixedBytes','Bytes20','__new__']):
        altered=dict(expected);altered[key]=b'foreign' if key.endswith('_body') else object()
        test(f'HV{i:02}',lambda a=altered:provenance(a,expected),True,dict(changed_field=key,descriptor=altered))
    test('HV08',lambda:provenance(expected,expected),False,
         dict(fields=list(expected),source_bodies={k:v for k,v in expected.items() if k.endswith('_body')}))
    good=primitive_event('length',original,20,bytes(19))
    def clone(d):
        return {k:clone(v) if type(v) is dict else list(v) if type(v) is list else v
                for k,v in d.items()}
    for i in range(10):
        event=clone(good);inner=event['cause'];terminal=inner['cause'];q=bytes(19)
        if i==0:terminal['frames']=[['_deserialize_to_bytes',260],['__new__',33]]
        elif i==1:terminal['exact_value_error']=False
        elif i==2:
            q=bytes(20);terminal.update(raw_value=q,native_args=(q,),result_bytes=q,
                args=['expected 20 bytes but got 20'],native_message='expected 20 bytes but got 20')
            inner['raw_value']=q
        elif i==3:terminal['target_token']=object()
        elif i==4:terminal['cause']=dict(marker=True)
        elif i==5:inner['suppressed']=False
        elif i==6:inner['context_same_cause']=False
        elif i==7:event['args']=['cannot decode into `Address`']
        elif i==8:terminal['raw_value']=bytearray(19)
        elif i==9:inner['frames']=[['decode_to',169],['deserialize_to',207],['_deserialize_to_bytes',260]]
        test(f'HE{i:02}',lambda e=event,q=q:admit(e,original,20,payload=q),True,
             dict(descriptor=event,payload=q))
    raw=primitive_event('raw',original,20)
    shape=primitive_event('shape',original,20,shape=[])
    singleton=b'\x00';one=primitive_event('length',original,20,singleton)
    for case,event,kwargs in [('HE10',raw,{}),('HE11',shape,dict(shape=[])),
            ('HE12',good,dict(payload=bytes(19))),
            ('HE13',one,dict(payload=singleton,wire=singleton))]:
        test(case,lambda e=event,k=kwargs:admit(e,original,20,**k),False,
             dict(descriptor=event,arguments=kwargs))
    for i,v in enumerate([value,bytearray(21),memoryview(b'\x94'+p),sentinel]):
        test(f'HO{i:02}',lambda v=v:native_output(v,original,20,value,p,b'\x94'+p),True,
             fixture(v))
    records[-1]['sentinel_touches']=dict(touches)
    if touches != dict(conversion=0,equality=0):
        raise RuntimeError('output sentinel observed before admission')
    test('HO04',lambda:native_output(b'\x94'+p,original,20,value,p,b'\x94'+p),False,
         dict(bytes=b'\x94'+p,expected_wire=b'\x94'+p))
    negatives=sum(r['result']=='rejected' for r in records)
    positives=sum(r['result']=='accepted' for r in records)
    if (negatives,positives,len(records))!=(50,9,59):
        raise RuntimeError('released helper group counts differ')
    return dict(records=records,total_negatives=negatives,total_positives=positives,
                constructor_setups=1,rlp_entries=0)


def fixture_wire(payload):
    """Released finite literal header table; not a replacement RLP oracle."""
    literal_wire(payload)
    if len(payload)==1 and payload[0]<128:
        return payload
    return HEADERS[len(payload)]+payload


def success_catalog():
    return [(20,p) for p in [bytes(20),bytes([255])*20,bytes(19)+b'\x01',
        b'\x01'+bytes(18)+b'\xff',bytes(range(20)),bytes([0,255])*10]]


def main():
    wheel_parser = argparse.ArgumentParser(add_help=False)
    wheel_parser.add_argument('--wheel-dir',type=Path,metavar='WHEELS')
    wheel_args, remaining = wheel_parser.parse_known_args()
    if '--help' not in remaining and '-h' not in remaining:
        if wheel_args.wheel_dir is None:
            wheel_parser.error('--wheel-dir WHEELS is required; see --help for exact filenames')
        if not wheel_args.wheel_dir.is_dir():
            wheel_parser.error('--wheel-dir must name an existing wheel directory')
        for name in ['ethereum_rlp-0.1.6-py3-none-any.whl','ethereum_types-0.4.1-py3-none-any.whl']:
            if not (wheel_args.wheel_dir/name).is_file():
                wheel_parser.error('missing original locked wheel: '+name)
    sys.argv = [sys.argv[0],*remaining]
    helpers_only = '--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context = setup_driver(__doc__,__file__,29801)
    runtime = dict(executable=sys.executable,version=sys.version,prefix=sys.prefix,
        base_prefix=sys.base_prefix,flags=repr(sys.flags),original_argv=sys.orig_argv,
        effective_argv=sys.argv,cwd=str(Path.cwd()))
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed != 29801:
        context.parser.error('use frozen -I -B and released seed29801')
    if sys.version_info[:2] != (3,13):
        context.parser.error('the released oracle interpreter is Python3.13')
    if any(n.split('.',1)[0]=='ethereum_rlp' for n in sys.modules):
        raise ImportError('ethereum_rlp imported before authentication')
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0,RlpFreshFinder(auth))
    from ethereum_rlp import rlp, exceptions
    from ethereum_types import bytes as bytes_module
    context.check_source(rlp,'ethereum_rlp/rlp.py',dependency=True)
    context.check_source(bytes_module,'ethereum_types/bytes.py',dependency=True)
    source_error = rlp.DecodingError
    rlp_path = Path(rlp.__file__).absolute()
    bytes_path = Path(bytes_module.__file__).absolute()
    carriers = [(f'Bytes{n}',n,getattr(bytes_module,f'Bytes{n}')) for n in WIDTHS]
    fixed = bytes_module.FixedBytes
    def resolved_global(function,name):
        return function.__globals__[name] if name in function.__globals__ else function.__builtins__[name]
    def fresh_codes(path):
        path = Path(path).absolute(); codes = {}
        def visit(code):
            codes[code.co_qualname] = code
            for child in code.co_consts:
                if inspect.iscode(child):
                    visit(child)
        visit(compile(path.read_bytes(),str(path),'exec',dont_inherit=True))
        return codes
    originals = fresh_codes(rlp_path)
    functions = {n:getattr(rlp,n) for n in originals if '.' not in n and inspect.isfunction(getattr(rlp,n,None))}
    saved_codes = {n:f.__code__ for n,f in functions.items()}
    for n,code in saved_codes.items():
        if code != originals[n] or code.co_filename != str(rlp_path):
            raise ImportError('original RLP code differs: '+n)
    exception_init,exception_str = source_error.__init__,source_error.__str__
    if exception_str.__code__ != fresh_codes(exceptions.__file__).get(exception_str.__code__.co_qualname):
        raise ImportError('original DecodingError renderer differs')
    constructor = inspect.getattr_static(fixed,'__new__')
    constructor_fn = constructor.__func__ if type(constructor) is staticmethod else constructor
    constructor_code = constructor_fn.__code__
    if constructor_code != fresh_codes(bytes_path).get(constructor_code.co_qualname):
        raise ImportError('original FixedBytes constructor differs')
    lengths = {n:c.LENGTH for _,n,c in carriers}
    observers = {name:inspect.getattr_static(bytes,name) for name in
                 ['__new__','__bytes__','__len__','__getitem__','__eq__','__iter__']}
    for _,n,cls in carriers:
        require_type(lengths[n],int)
        if lengths[n] != n or cls.__bases__ != (fixed,) or fixed.__bases__ != (bytes,):
            raise ImportError('original fixed class hierarchy/width differs')
        if inspect.getattr_static(cls,'__new__') is not constructor:
            raise ImportError('original inherited constructor differs')
        for name,observer in observers.items():
            if name!='__new__' and inspect.getattr_static(cls,name) is not observer:
                raise ImportError('original inherited bytes observer differs')
    aliases = {n:getattr(rlp,n) for n in ['Bytes','FixedBytes','Uint','FixedUnsigned','Sequence']}
    if bytes_module.Bytes is not bytes or rlp.Bytes is not bytes or rlp.FixedBytes is not fixed:
        raise ImportError('original bytes aliases differ')
    bindings = []
    for fn,names in [(rlp.deserialize_to,['get_origin','is_dataclass','isinstance','issubclass','type','bool']),
            (rlp._deserialize_to_bytes,['isinstance','bytes','ValueError']),
            (rlp.decode_to,['Exception']),
            (rlp.encode,['isinstance','bool','bytes','bytearray','str']),
            (constructor_fn,['bytes','len','ValueError'])]:
        for name in names:
            value = resolved_global(fn,name);bindings.append((fn,name,value))
            if hasattr(builtins,name) and value is not getattr(builtins,name):
                raise ImportError('original builtin differs: '+name)
    callbacks = {n:(getattr(rlp,n),getattr(rlp,n).__code__) for n in ['get_origin','get_args','is_dataclass']}
    for name,(fn,code) in callbacks.items():
        owner = dataclasses if name=='is_dataclass' else typing
        if getattr(owner,name) is not fn or code != fresh_codes(inspect.getsourcefile(fn)).get(code.co_qualname):
            raise ImportError('original reflection callback differs')
    for path,sites in [(rlp_path,[*RAW,171,258,262]),(bytes_path,[36])]:
        lines = path.read_text().splitlines()
        if any(not lines[n-1].lstrip().startswith('raise ') for n in sites):
            raise ImportError('released origin is not an original raise')
    def live_provenance():
        return dict(rlp_body=rlp_path.read_bytes(),bytes_body=bytes_path.read_bytes(),
            encode=rlp.encode,decode_to=rlp.decode_to,deserialize_to=rlp.deserialize_to,
            FixedBytes=bytes_module.FixedBytes,Bytes20=bytes_module.Bytes20,
            __new__=inspect.getattr_static(bytes_module.FixedBytes,'__new__'))
    expected = live_provenance()
    def identities():
        provenance(live_provenance(),expected)
        if (bytes_module.Bytes is not bytes or rlp.Bytes is not bytes or rlp.FixedBytes is not fixed
                or exceptions.DecodingError is not source_error or rlp.DecodingError is not source_error
                or source_error.__init__ is not exception_init or source_error.__str__ is not exception_str
                or constructor_fn.__code__ is not constructor_code or constructor_fn.__globals__ is not bytes_module.__dict__):
            raise ImportError('original bytes/exception identity drift')
        for n,value in aliases.items():
            if getattr(rlp,n) is not value:
                raise ImportError('original dispatch alias drift: '+n)
        for n,fn in functions.items():
            if getattr(rlp,n) is not fn or fn.__code__ is not saved_codes[n] or fn.__globals__ is not rlp.__dict__:
                raise ImportError('original function/code/global drift: '+n)
        for name,n,cls in carriers:
            if (getattr(bytes_module,name) is not cls or cls.__bases__ != (fixed,)
                    or fixed.__bases__ != (bytes,) or cls.LENGTH is not lengths[n]
                    or type(cls.LENGTH) is not int or cls.LENGTH != n
                    or inspect.getattr_static(cls,'__new__') is not constructor):
                raise ImportError('original class/width/constructor drift')
            for key,observer in observers.items():
                if (inspect.getattr_static(bytes,key) is not observer
                        or (key!='__new__' and inspect.getattr_static(cls,key) is not observer)):
                    raise ImportError('original native bytes observer drift')
        for fn,name,value in bindings:
            if resolved_global(fn,name) is not value:
                raise ImportError('original reflection/builtin drift')
        for name,(fn,code) in callbacks.items():
            if getattr(rlp,name) is not fn or fn.__code__ is not code:
                raise ImportError('original reflection callback/code drift')
    lock = tomllib.loads((context.eels/'uv.lock').read_text())
    wheel_dir = wheel_args.wheel_dir.resolve(); wheel_receipts = []
    for package,version,folder in [('ethereum-rlp','0.1.6','ethereum_rlp'),('ethereum-types','0.4.1','ethereum_types')]:
        wheel = wheel_dir/(package.replace('-','_')+'-'+version+'-py3-none-any.whl')
        digest = hashlib.sha256(wheel.read_bytes()).hexdigest()
        entries = [p for p in lock['package'] if p['name']==package and p['version']==version]
        if len(entries)!=1 or not any(w['hash']=='sha256:'+digest for w in entries[0]['wheels']):
            raise ImportError('wheel differs from original lock')
        with zipfile.ZipFile(wheel) as archive:
            members = [n for n in archive.namelist() if n.startswith(folder+'/') and n.endswith('.py')]
            for name in members:
                installed = context.eels/'.venv/lib/python3.13/site-packages'/name
                if installed.read_bytes()!=archive.read(name):
                    raise ImportError('installed source differs from lock wheel: '+name)
        wheel_receipts.append(dict(path=str(wheel),sha256=digest,source_members=len(members)))
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
        for row in wheel_receipts:
            if hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()!=row['sha256']:
                raise ImportError('wheel input drift')
    def serializable(value):
        if type(value) is bytes:
            return dict(native_type='builtins.bytes',bytes=list(value),hex=value.hex())
        if type(value) in (list,tuple):
            return [serializable(x) for x in value]
        if type(value) is dict:
            return {k:serializable(v) for k,v in value.items()}
        for name,n,cls in carriers:
            if value is cls:
                return dict(original_class=name,width=n)
        if type(value) in (str,int,bool,float) or value is None:
            return value
        if type(value) is type:
            return dict(unadmitted_class=value.__module__+'.'+value.__qualname__)
        return dict(unadmitted_object_type=type(value).__module__+'.'+type(value).__qualname__)
    closure()
    if helpers_only:
        helpers = helper_controls(carriers,expected)
        closure();print(json.dumps(serializable(dict(profile='helpers-only',runtime=runtime,**helpers)),sort_keys=True));return 0
    # Source execution never repeats helper fixtures or their constructor setups.
    helpers = dict(total_negatives=50,total_positives=9,
                   execution='separate final normal/-O runs; not repeated here')
    def trace(exc, original, width):
        frames, all_frames, authenticated = [], [], True
        fields = {}; tokens = []; tb = exc.__traceback__
        while tb:
            frame = tb.tb_frame; code = frame.f_code; local = frame.f_locals
            all_frames.append(dict(file=code.co_filename,function=code.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(code)).hexdigest()))
            if code.co_filename==str(rlp_path):
                frames.append([code.co_name,tb.tb_lineno])
                if saved_codes.get(code.co_name) is not code:
                    authenticated = False
                if code.co_name in ['decode_to','deserialize_to','_deserialize_to_bytes']:
                    target = local['cls' if code.co_name=='decode_to' else 'class_']
                    tokens.append(target)
                    fields.update(target_exact=target is original,target_token=target)
                if code.co_name=='decode_to' and 'decoded' in local:
                    fields['outer_decoded']=model_observation(local['decoded'])
                if code.co_name=='deserialize_to':
                    fields['dispatch_value']=model_observation(local['value'])
                if code.co_name=='_deserialize_to_bytes':
                    value = local['value']
                    if tb.tb_lineno==258:
                        fields['frame_value'] = model_observation(value)
                    elif type(value) is bytes:
                        fields['raw_value'] = value
                    else:
                        # No coercion of a foreign native value at the capture boundary.
                        authenticated = False
                        fields['foreign_raw_type'] = type(value).__module__+'.'+type(value).__qualname__
            elif code.co_filename==str(bytes_path):
                frames.append([code.co_name,tb.tb_lineno])
                if code is not constructor_code:
                    authenticated = False
                target = local.get('cls'); tokens.append(target)
                result = local.get('result')
                fields.update(target_exact=target is original,target_token=target,
                    native_args=local.get('args'),native_kwargs=local.get('kwargs'),
                    native_message=local.get('message'),length_token=original.LENGTH,
                    result_token=type(result))
                # A length-failure result has the exact target class but the wrong length.
                # Admit class, then project its whole bytes; do not call success admission.
                if type(result) is original:
                    fields['result_bytes'] = bytes(result)
                else:
                    authenticated = False
                args = local.get('args')
                if type(args) is tuple and len(args)==1 and type(args[0]) is bytes:
                    fields['raw_value'] = args[0]
                else:
                    authenticated = False
            elif code not in (observe.__code__,enc.__code__):
                authenticated = False
            tb = tb.tb_next
        result = dict(exact=type(exc) is source_error,exact_value_error=type(exc) is ValueError,
            exception_class=type(exc).__module__+'.'+type(exc).__qualname__,
            authenticated=authenticated,frames=frames,traceback=all_frames,args=list(exc.args),
            message=str(exc),cause=trace(exc.__cause__,original,width) if exc.__cause__ is not None else None,
            context=exc.__context__ is not None,suppressed=exc.__suppress_context__,
            context_same_cause=exc.__cause__ is not None and exc.__cause__ is exc.__context__,
            context_detail=trace(exc.__context__,original,width)
                if exc.__context__ is not None and exc.__context__ is not exc.__cause__ else None)
        result.update(fields)
        if tokens:
            result['class_tokens'] = tokens
        return result
    guards = ['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base']
    records = []; counts = dict(encode=0,decode=0,decode_ok=0,typed_error=0,raw_error=0)
    call_path = context.output.with_suffix('.calls.jsonl')
    if context.output.exists() or call_path.exists() or context.output.with_suffix('.observations.json').exists():
        raise FileExistsError('fresh source evidence destinations required')
    def retain(event):
        with call_path.open('a') as out:
            out.write(json.dumps(serializable(event),sort_keys=True)+'\n')
    def lean_bytes(data):
        chunks = [list(data[i:i+64]) for i in range(0,len(data),64)]
        return f'(ByteArray.mk (({chunks} : List (List UInt8)).flatten.toArray))'
    def fixed_expr(width,payload):
        # Fixture construction for Lean only, after byte admission. Never source admission.
        return f'(Address.ofNat {int.from_bytes(payload,"big")})'
    def enc(case,width,payload,original):
        payload_input(payload,width);expected_wire = fixture_wire(payload)
        guard = f'#guard encodeOf {fixed_expr(width,payload)} = {lean_bytes(expected_wire)}'
        record = dict(id=case,operation='encode',width=width,carrier=f'Bytes{width}',
            input_payload=list(payload),expected_wire=list(expected_wire),guard=guard)
        retain(dict(record,event='planned-before-entry'))
        value = original(payload)
        if fixed_result(value,original,width)!=payload:
            raise ValueError('original constructor full bytes differ')
        identities();counts['encode']+=1
        try:
            wire = functions['encode'](value)
        except BaseException as exc:
            retain(dict(record,event='unexpected-error',exception=trace(exc,original,width)))
            raise
        projected = native_output(wire,original,width,value,payload,expected_wire)
        identities()
        record.update(wire=list(projected),wire_hex=projected.hex(),result='ok',
            native_class=type(wire).__module__+'.'+type(wire).__qualname__,
            same_object_as_constructor_input=wire is value,
            projection_after_native_admission=True)
        retain(dict(record,event='observed'));records.append(record);guards.append(guard+' -- '+case)
        return wire,value
    def observe(case,wire,width,original,payload=None,shape=None,expected_error=None,native_input=None):
        literal_wire(wire);projected = wire
        if expected_error is None:
            payload_input(payload,width)
            result = f'(Except.ok {fixed_expr(width,payload)} : Except RlpError Address)'
        else:
            result = f'(Except.error ({expected_error[0]}) : Except RlpError Address)'
        expr = f'decodeTo (α := Address) {lean_bytes(projected)}'
        guard = (f'#guard (match ({expr}), {result} with | .ok a, .ok b => decide (a = b) '
                 '| .error a, .error b => decide (a = b) | _, _ => false)')
        record = dict(id=case,operation='decode_to',width=width,carrier=f'Bytes{width}',
            wire=list(projected),wire_hex=projected.hex(),
            native_wire_class=type(wire).__module__+'.'+type(wire).__qualname__,
            wire_is_paired_constructor_input=wire is native_input,
            wire_is_actual_paired_encode_result=native_input is not None,
            expected_payload=list(payload) if payload is not None else None,
            expected_shape=model_observation(shape) if shape is not None else None,
            expected_error=expected_error,lean_result=result,lean_expression=expr,guard=guard,
            lean_common_expression=f'({expr}).mapError (fun (_ : RlpError) => ())')
        retain(dict(record,event='planned-before-entry'));identities();counts['decode']+=1
        try:
            value = functions['decode_to'](original,wire)
        except BaseException as exc:
            identities();event = trace(exc,original,width)
            retain(dict(record,event='observed-exception-before-admission',exception=event))
            error,phase,site = admit(event,original,width,payload=payload,shape=shape,wire=wire)
            if expected_error != (error,phase,site):
                raise RuntimeError('case-specific complete rejection differs: '+case)
            counts[phase+'_error']+=1
            record.update(result='error',diagnostic=error,phase=phase,site=site,
                exception=serializable(event),
                raw_singleton_same_wire=(event['cause']['raw_value'] is wire
                    and event['cause']['cause']['raw_value'] is wire)
                    if phase=='typed' and site==36 and wire in (b'\x00',b'\x01',b'\x7f') else None,
                common_channel=dict(type=f'Except Unit Address',constructor='error'))
        else:
            identities();actual = fixed_result(value,original,width)
            if expected_error is not None or payload is None or actual!=payload:
                retain(dict(record,event='unexpected-success',payload=list(actual)))
                raise RuntimeError('unexpected exact source success: '+case)
            counts['decode_ok']+=1
            record.update(result='ok',payload=list(actual),result_class=type(value).__module__+'.'+type(value).__qualname__,
                projection_after_native_admission=True,
                common_channel=dict(type=f'Except Unit Address',constructor='ok',bytes=list(actual)))
        retain(dict(record,event='observed'));records.append(record);guards.append(guard+' -- '+case)
    original=carriers[0][2]
    for i,(n,payload) in enumerate(success_catalog()):
        wire,value=enc(f'A{i:02}-E',n,payload,original)
        observe(f'A{i:02}-D',wire,n,original,payload=payload,native_input=value)
    for i,payload in enumerate([bytes(reversed(range(20))),b'\x80'+bytes(19)]):
        observe(f'B{i:02}',fixture_wire(payload),20,original,payload=payload)
    for i,(wire,shape) in enumerate(SHAPES):
        observe(f'C{i:02}',wire,20,original,shape=shape,
                expected_error=('.shape "bytes"','typed',258))
    for i,k in enumerate(LENGTHS):
        payload=bytes(k)
        observe(f'D{i:02}',fixture_wire(payload),20,original,payload=payload,
                expected_error=('.shape "fixed bytes length"','typed',36))
    for i,payload in enumerate([b'\x01',b'\x7f',b'\x80',b'\xff',b'\x00\x01']):
        observe(f'E{i:02}',fixture_wire(payload),20,original,payload=payload,
                expected_error=('.shape "fixed bytes length"','typed',36))
    for i,(wire_hex,site) in enumerate(RAW_CASES):
        observe(f'R{i:02}',bytes.fromhex(wire_hex),20,original,
                expected_error=(RAW[site][1],'raw',site))
    if counts != dict(encode=6,decode=41,decode_ok=8,typed_error=21,raw_error=12):
        raise RuntimeError('released profile counts differ')
    if len(records)!=47 or len(guards)!=49 or max(len(r['wire']) for r in records)!=259:
        raise RuntimeError('released profile cardinality/extent differs')
    closure()
    identity = dict(runtime=runtime,functions={n:dict(file=c.co_filename,line=c.co_firstlineno,
        code_sha256=hashlib.sha256(marshal.dumps(c)).hexdigest()) for n,c in saved_codes.items()},
        constructor=dict(file=constructor_code.co_filename,line=constructor_code.co_firstlineno,
            code_sha256=hashlib.sha256(marshal.dumps(constructor_code)).hexdigest()),
        carriers={name:dict(module=cls.__module__,name=cls.__qualname__,width=n,
            LENGTH_exact_int=type(cls.LENGTH) is int,LENGTH=n,exact_original=True,
            bases=[x.__module__+'.'+x.__qualname__ for x in cls.__mro__]) for name,n,cls in carriers},
        observers={n:dict(type=type(v).__module__+'.'+type(v).__qualname__) for n,v in observers.items()},
        bindings=[dict(function=fn.__qualname__,name=name,type=type(value).__module__+'.'+type(value).__qualname__,
            code_sha256=hashlib.sha256(marshal.dumps(value.__code__)).hexdigest() if inspect.isfunction(value) else None)
            for fn,name,value in bindings],
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected},
        rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest(),wheels=wheel_receipts,
        wheel_directory=dict(supplied=str(wheel_args.wheel_dir),resolved=str(wheel_dir)))
    observation_path = context.output.with_suffix('.observations.json')
    observation_path.write_text(json.dumps(dict(seed=29801,cases=records,identities=identity,helpers=helpers,
        counts=counts,total_success=14,direct_constructor_setups=6,
        decode_constructor_success=8,decode_constructor_length_failures=17,total_constructors=31,
        max_payload=256,max_wire=259,max_raw_wire=3,max_raw_valid_depth=2,max_raw_valid_arity=1,
        trust='finite original-class correspondence only; native/interpreter/startup/install/host/compiler/kernel trusted'),indent=2)+'\n')
    closure()
    result = context.run(guards,counts=dict(**counts,total_success=14),observations=str(observation_path),
        domain='exact original Bytes20; seed29801; no RNG; literal raw singleton identities retained')
    closure()
    return result


if __name__ == '__main__':
    raise SystemExit(main())
