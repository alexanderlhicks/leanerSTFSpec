#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Authentic ordered typing.List[original Uint] RLP observations.

Use frozen EELS/.venv/bin/python -I -B --eels EELS --wheel-dir WHEELS
--output EXTERNAL.lean --seed 30001. Original locked wheels required:
ethereum_rlp-0.1.6-py3-none-any.whl and ethereum_types-0.4.1-py3-none-any.whl.
--helpers-only runs exactly40 negative/8 positive admission groups and zero RLP
entries, with four explicit numeric setups. Run normally, then under -O, before
one source profile: E01–E08,D01–D08,T01–T06,R01–R06, exactly28 entries and guards.
The profile has five explicit Uint setups, one retained genuine alias, no RNG,
extra raw decode, trace hook, source replacement, With callback or crypto call.
Native operations, interpreter/startup/install/RECORD, ambient host, orchestration
and Lean compiler/kernel remain trust inputs. Finite whole-value evidence is no
universal refinement, callback trace/cost, schema-depth, EEST or guest theorem.
Full Lean diagnostics and external Except Unit observation remain separate.
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

FUNCTIONS = ['encode','encode_bytes','encode_sequence','join_encodings','decode',
    'decode_to','deserialize_to','_deserialize_to_annotation','_deserialize_to_list',
    '_deserialize_to_uint','decode_to_bytes','decode_to_sequence',
    'decode_joined_encodings','decode_item_length']
NUMERIC = ['__init__','__int__','__index__','__eq__','to_be_bytes','from_be_bytes','_in_range']
SUCCESS = [([], 'c0'),([0],'c180'),([1],'c101'),([0,1,0],'c3800180'),
    ([128,255,256],'c7818081ff820100'),([256,1,256],'c782010001820100'),
    ([0]*55,'f7'+'80'*55),([0]*56,'f838'+'80'*56)]
TYPED = [('80',b'',None,374,'.shape "list"'),
    ('c200c0',[b'\0',[]],0,271,'.nonCanonical "integer leading zero"'),
    ('c100',[b'\0'],0,271,'.nonCanonical "integer leading zero"'),
    ('c1c0',[[]],0,269,'.shape "integer"'),
    ('c3800080',[b'',b'\0',b''],1,271,'.nonCanonical "integer leading zero"'),
    ('c2c000',[[],b'\0'],0,269,'.shape "integer"')]
RAW = [('',('Cannot decode empty bytestring',),[['decode_to',167],['decode',149]],'.empty'),
    ('c2c0',('truncated',),[['decode_to',167],['decode',156],['decode_to_sequence',435]],'.truncated'),
    ('c10000',('trailing bytes',),[['decode_to',167],['decode',156],['decode_to_sequence',437]],'.trailing'),
    ('c20081',('truncated',),[['decode_to',167],['decode',156],['decode_to_sequence',461],['decode_joined_encodings',477]],'.truncated'),
    ('c3008101',(),[['decode_to',167],['decode',156],['decode_to_sequence',461],['decode_joined_encodings',481],['decode',153],['decode_to_bytes',404]],'.nonCanonical "prefixed single byte"'),
    ('f800',(),[['decode_to',167],['decode',156],['decode_to_sequence',444]],'.nonCanonical "leading zero length"')]


def literal_wire(value):
    require_type(value,bytes)
    return value


def request(value):
    require_type(value,int)
    if value < 0:
        raise ValueError('negative plain-int request')
    return value


def uint_values(value, original):
    # Admit the whole native shape before conversion, equality or serialization.
    require_type(value,list)
    numbers=[]
    for child in value:
        require_type(child,original)
        number=child._number
        request(number)
        numbers.append(number)
    return numbers


def uint_output(value,original,expected):
    numbers=uint_values(value,original)
    require_type(expected,list)
    for n in expected:
        request(n)
    if numbers != expected:
        raise ValueError('complete ordered Uint result differs')
    return numbers


def model_observation(value):
    if type(value) is bytes:
        return dict(constructor='bytes',bytes=list(value))
    require_type(value,list)
    return dict(constructor='list',children=[model_observation(x) for x in value])


def provenance(actual,expected):
    if set(actual)!=set(expected):
        raise ValueError('finite provenance inventory differs')
    for name,wanted in expected.items():
        got=actual[name]
        if name.endswith('_body'):
            if type(got) is not bytes or got!=wanted:
                raise ValueError('authenticated body differs: '+name)
        elif got is not wanted:
            raise ValueError('original identity/default differs: '+name)


def alias_descriptor(target, original):
    return dict(token=target,alias_class=type(target),origin=typing.get_origin(target),
        args=typing.get_args(target),name=target._name,inst=target._inst,
        parameters=target.__parameters__,dunder_name=target.__name__,
        qualname=target.__qualname__,render=str(target),representation=repr(target),
        annotated_with=False)


def admit_alias(actual,expected,original):
    # Descriptors are primitive controls; no fake alias is instantiated.
    for key in ['token','alias_class','origin']:
        if actual.get(key) is not expected[key]:
            raise ValueError('retained original alias identity differs: '+key)
    args=actual.get('args')
    if type(args) is not tuple or len(args)!=1 or args[0] is not original:
        raise ValueError('original alias argument differs')
    if actual['origin'] is not list:
        raise ValueError('original alias origin differs')
    if (actual.get('name')!='List' or actual.get('inst') is not False
            or actual.get('parameters')!=() or actual.get('dunder_name')!='List'
            or actual.get('qualname')!='List' or actual.get('annotated_with') is not False
            or actual.get('render')!='typing.List[ethereum_types.numeric.Uint]'
            or actual.get('representation')!='typing.List[ethereum_types.numeric.Uint]'):
        raise ValueError('authentic List metadata differs')
    return dict(origin='builtins.list',argument='ethereum_types.numeric.Uint',
        name=actual['name'],render=actual['render'],parameters=[],inst=False,
        exact_retained_identity=True,alias_class=type(expected['token']).__qualname__)


def primitive_event(kind,target,original,index=None,site=None,raw=None):
    """Closed primitive admission fixtures; these are never source exceptions."""
    base=dict(exact=True,authenticated=True,args=[],cause=None,context=False,
        suppressed=False,context_same_cause=False,context_detail=None,frames=[])
    if kind=='raw':
        return dict(base,args=list(RAW[0][1]),frames=RAW[0][2])
    middle=dict(base,frames=[['decode_to',169],['deserialize_to',201],
        ['_deserialize_to_annotation',318],['_deserialize_to_list',374 if index is None else 382]],
        args=['invalid list'] if index is None else
            [f'cannot decode list item {index} of type `typing.List[ethereum_types.numeric.Uint]`'],
        alias_exact=True,argument_exact=True,raw=model_observation(raw),
        raw_identity=True,index=index,child_identity=True)
    if index is not None:
        middle.update(context=True,suppressed=True,context_same_cause=True,
            child=model_observation(raw[index]),cause=dict(base,
                frames=[['_deserialize_to_list',379],['deserialize_to',205],['_deserialize_to_uint',site]],
                args=['invalid uint' if site==269 else 'non-canonical integer'],
                alias_exact=True,argument_exact=True,raw=model_observation(raw),
                child=model_observation(raw[index]),raw_identity=True,
                child_identity=True,index=index))
    return dict(base,frames=[['decode_to',171]],args=['cannot decode into `List`'],
        cause=middle,context=True,suppressed=True,context_same_cause=True,
        alias_exact=True,wire_exact=True,raw=model_observation(raw),raw_identity=True)


def admit_event(record,kind,target,original,index=None,site=None,raw=None,raw_case=0):
    def base(r):
        if r['exact'] is not True or r['authenticated'] is not True:
            raise ValueError('wrong original exception class/code/globals')
        if r.get('context_detail') is not None:
            raise ValueError('unexpected distinct exception context')
    def terminal(r):
        base(r)
        if r['cause'] is not None or r['context'] or r['suppressed'] or r['context_same_cause']:
            raise ValueError('unexpected complete terminal exception chain')
    base(record)
    if kind=='raw':
        terminal(record)
        _,args,frames,error=RAW[raw_case]
        if record['frames']!=frames or record['args']!=list(args):
            raise ValueError('foreign complete raw exception path/args')
        return error,'raw',frames[-1][1]
    middle=record['cause']
    if (record['frames']!=[['decode_to',171]] or record['args']!=['cannot decode into `List`']
            or record['context'] is not True or record['suppressed'] is not True
            or record['context_same_cause'] is not True or middle is None
            or record.get('alias_exact') is not True or record.get('wire_exact') is not True
            or record.get('raw_identity') is not True
            or record.get('raw')!=model_observation(raw)):
        raise ValueError('missing/foreign complete typed wrapper/target/raw')
    base(middle)
    frames=[['decode_to',169],['deserialize_to',201],['_deserialize_to_annotation',318],
        ['_deserialize_to_list',374 if index is None else 382]]
    if (middle['frames']!=frames or middle.get('alias_exact') is not True
            or middle.get('argument_exact') is not True or middle.get('raw_identity') is not True
            or middle.get('raw')!=model_observation(raw) or middle.get('index')!=index):
        raise ValueError('wrong list origin/alias/raw/first index')
    if index is None:
        terminal(middle)
        if middle['args']!=['invalid list']:
            raise ValueError('wrong complete list-shape cause')
        return '.shape "list"','typed',374
    leaf=middle['cause']
    if (middle['args']!=[f'cannot decode list item {index} of type `typing.List[ethereum_types.numeric.Uint]`']
            or middle['context'] is not True or middle['suppressed'] is not True
            or middle['context_same_cause'] is not True or leaf is None
            or middle.get('child_identity') is not True
            or middle.get('child')!=model_observation(raw[index])):
        raise ValueError('wrong complete indexed list wrapper/cause')
    terminal(leaf)
    if (leaf['frames']!=[['_deserialize_to_list',379],['deserialize_to',205],['_deserialize_to_uint',site]]
            or leaf['args']!=['invalid uint' if site==269 else 'non-canonical integer']
            or site not in (269,271) or leaf.get('alias_exact') is not True
            or leaf.get('argument_exact') is not True or leaf.get('raw_identity') is not True
            or leaf.get('child_identity') is not True or leaf.get('index')!=index
            or leaf.get('raw')!=model_observation(raw)
            or leaf.get('child')!=model_observation(raw[index])):
        raise ValueError('wrong original Uint leaf cause/child/index')
    return ('.shape "integer"' if site==269 else '.nonCanonical "integer leading zero"'),'typed',site


def clone(value):
    if type(value) is dict:
        return {k:clone(v) for k,v in value.items()}
    if type(value) is list:
        return [clone(v) for v in value]
    return value


def helper_controls(original,u256,target,expected,alias_expected,serialize):
    # Exactly four explicit constructions, reused across all48 fixture groups.
    zero=original(request(0));one=original(request(1));two56=original(request(256));wide=u256(request(0))
    uint_values([zero,one,two56],original)
    records=[]
    def test(i,rule,thunk,negative,fixture):
        row=dict(id=i,rule=rule,fixture=serialize(fixture))
        try:
            result=thunk()
        except (TypeError,ValueError) as e:
            if not negative:
                raise
            row.update(result='rejected',exception=type(e).__name__,message=str(e))
        else:
            if negative:
                raise RuntimeError('negative admission fixture accepted: '+i)
            row.update(result='accepted',observation=serialize(result))
        records.append(row)
    class BytesSubclass(bytes):
        pass
    for n,v in enumerate([bytearray(),memoryview(b''),'',[],None,BytesSubclass()],1):
        test(f'N{n:02}','exact builtin bytes',lambda v=v:literal_wire(v),True,v)
    for n,v in enumerate([(zero,),[True],[0],[wide],[None],-1,[1.0]],7):
        test(f'N{n:02}','exact list/original Uint/nonnegative request',
            (lambda v=v:request(v)) if n==12 else (lambda v=v:uint_values(v,original)),True,v)
    expected_numbers=[256,1,256]
    for n,v in enumerate([(two56,one,two56),[True],[0],[wide],[one,two56,two56],[two56,one]],14):
        test(f'N{n:02}','exact result classes then complete order',
            lambda v=v:uint_output(v,original,expected_numbers),True,v)
    for n,key in enumerate(['rlp_body','encode','encode_code','encode_defaults',
            'encode_kwdefaults','get_origin','get_args'],20):
        d=dict(expected);d[key]=b'altered body' if key.endswith('_body') else ('altered',) if n in (23,24) else object()
        test(f'N{n:02}','finite original provenance/default closure',lambda d=d:provenance(d,expected),True,
            dict(changed_field=key,descriptor=d))
    goodraw=primitive_event('raw',target,original)
    goodshape=primitive_event('typed',target,original,raw=b'')
    goodtyped=primitive_event('typed',target,original,index=1,site=271,raw=[b'',b'\0',b''])
    for n in range(27,33):
        kind='raw' if n in (27,28) else 'typed';d=clone(goodraw if kind=='raw' else goodtyped)
        if n==27:d['exact']=False
        elif n==28:d['frames']=[['decode_to',167],['decode',999]]
        elif n==29:d['cause']['cause']['exact']=False;d['cause']['cause']['exception_class']='builtins.MemoryError'
        elif n==30:d['cause']['index']=0
        elif n==31:d['cause']['cause']['args']=['invalid uint']
        elif n==32:d['frames']=[['decode_to',169]];d['args']=[]
        test(f'N{n:02}','complete admitted exception path',
            lambda d=d,kind=kind:admit_event(d,kind,target,original,index=1 if kind=='typed' else None,
                site=271 if kind=='typed' else None,raw=[b'',b'\0',b''] if kind=='typed' else None),True,d)
    for n,key,value in [(33,'origin',tuple),(34,'args',(u256,)),(35,'name','Tuple'),
            (36,'token',object()),(37,'args',()),(38,'annotated_with',True)]:
        d=dict(alias_expected);d[key]=value
        test(f'N{n:02}','authentic retained alias metadata',lambda d=d:admit_alias(d,alias_expected,original),True,d)
    for n,key in [(39,'Uint_to_be_bytes'),(40,'is_dataclass')]:
        d=dict(expected);d[key]=object()
        test(f'N{n:02}','original numeric/reflection method',lambda d=d:provenance(d,expected),True,d)
    for i,rule,thunk,fixture in [
        ('P01','exact empty bytes',lambda:literal_wire(b''),b''),
        ('P02','exact empty list',lambda:uint_values([],original),[]),
        ('P03','exact Uint0 input',lambda:uint_values([zero],original),[zero]),
        ('P04','exact Uint1 output',lambda:uint_output([one],original,[1]),[one]),
        ('P05','whole ordered result',lambda:uint_output([two56,one,two56],original,[256,1,256]),[two56,one,two56]),
        ('P06','complete raw R01',lambda:admit_event(goodraw,'raw',target,original),goodraw),
        ('P07','complete T01',lambda:admit_event(goodshape,'typed',target,original,raw=b''),goodshape),
        ('P08','complete T05',lambda:admit_event(goodtyped,'typed',target,original,index=1,site=271,raw=[b'',b'\0',b'']),goodtyped)]:
        test(i,rule,thunk,False,fixture)
    if ([x['id'] for x in records]!=[f'N{i:02}' for i in range(1,41)]+[f'P{i:02}' for i in range(1,9)]
            or sum(x['result']=='rejected' for x in records)!=40
            or sum(x['result']=='accepted' for x in records)!=8):
        raise RuntimeError('closed helper inventory differs')
    return dict(records=records,total_negatives=40,total_positives=8,
        constructor_setups=4,alias_parameterizations=1,rlp_entries=0)


def fresh_codes(path):
    path=Path(path).absolute();codes={}
    def visit(code):
        codes[code.co_qualname]=code
        for child in code.co_consts:
            if inspect.iscode(child):
                visit(child)
    visit(compile(path.read_bytes(),str(path),'exec',dont_inherit=True))
    return codes


def main():
    wheel_parser=argparse.ArgumentParser(add_help=False)
    wheel_parser.add_argument('--wheel-dir',type=Path,metavar='WHEELS')
    wheel_args,remaining=wheel_parser.parse_known_args()
    if '--help' not in remaining and '-h' not in remaining:
        if wheel_args.wheel_dir is None or not wheel_args.wheel_dir.is_dir():
            wheel_parser.error('--wheel-dir WHEELS is required; see --help for exact filenames')
        for name in ['ethereum_rlp-0.1.6-py3-none-any.whl','ethereum_types-0.4.1-py3-none-any.whl']:
            if not (wheel_args.wheel_dir/name).is_file():
                wheel_parser.error('missing original locked wheel: '+name)
    sys.argv=[sys.argv[0],*remaining]
    helpers_only='--helpers-only' in sys.argv
    if helpers_only:
        sys.argv.remove('--helpers-only')
    context=setup_driver(__doc__,__file__,30001)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode or context.seed!=30001:
        context.parser.error('use frozen -I -B and released seed30001')
    if sys.version_info[:2]!=(3,13):
        context.parser.error('released interpreter is Python3.13')
    if any(n.split('.',1)[0]=='ethereum_rlp' for n in sys.modules):
        raise ImportError('RLP imported before authentication')
    auth=RlpSourceAuth(context);sys.meta_path.insert(0,RlpFreshFinder(auth))
    from ethereum_rlp import rlp,exceptions
    from ethereum_types import numeric,bytes as bytes_module
    context.check_source(rlp,'ethereum_rlp/rlp.py',dependency=True)
    context.check_source(numeric,'ethereum_types/numeric.py',dependency=True)
    original=numeric.Uint;u256=numeric.U256
    target=typing.List[original]  # The sole genuine alias parameterization in this process.
    alias_expected=alias_descriptor(target,original)
    alias_metadata=admit_alias(alias_expected,alias_expected,original)
    rlp_path=Path(rlp.__file__).absolute();numeric_path=Path(numeric.__file__).absolute()
    source_error=exceptions.DecodingError
    functions={n:getattr(rlp,n) for n in FUNCTIONS}
    codes={n:f.__code__ for n,f in functions.items()}
    methods={n:inspect.getattr_static(original,n) for n in NUMERIC}
    def method_fn(method):
        return method.__func__ if type(method) in (classmethod,staticmethod) else method
    numeric_functions={n:method_fn(m) for n,m in methods.items()}
    callbacks={n:getattr(rlp,n) for n in ['get_origin','get_args','is_dataclass']}
    if callbacks!={'get_origin':typing.get_origin,'get_args':typing.get_args,'is_dataclass':dataclasses.is_dataclass}:
        raise ImportError('original direct reflection aliases differ')
    if (rlp.Uint is not original or rlp.FixedUnsigned is not numeric.FixedUnsigned
            or rlp.List is not typing.List or rlp.Bytes is not bytes or bytes_module.Bytes is not bytes
            or rlp.DecodingError is not source_error or original.__bases__!=(numeric.Unsigned,)
            or original.__mro__!=(original,numeric.Unsigned,object)
            or (original.__name__,original.__qualname__,original.__module__)!=('Uint','Uint','ethereum_types.numeric')):
        raise ImportError('original numeric/dispatch hierarchy differs')
    original_slot=inspect.getattr_static(original,'_number')
    rlp_fresh=fresh_codes(rlp_path);numeric_fresh=fresh_codes(numeric_path)
    # Every selected pure Python method/function is checked against current authenticated bytes.
    selected_functions={**functions,**{'Uint_'+k:v for k,v in numeric_functions.items()},**callbacks}
    function_closure=[]
    def bind_function(label,fn,none_defaults=False):
        if not inspect.isfunction(fn):
            raise ImportError('selected callback is not Python source: '+label)
        path=Path(inspect.getsourcefile(fn)).absolute();code=fn.__code__
        if code!=fresh_codes(path).get(code.co_qualname) or code.co_filename!=str(path):
            raise ImportError('selected current code differs: '+label)
        if none_defaults and (fn.__defaults__ is not None or fn.__kwdefaults__ is not None):
            raise ImportError('selected finite None defaults differ: '+label)
        bindings={}
        for name in code.co_names:
            if name in fn.__globals__:
                bindings[name]=fn.__globals__[name]
            elif name in fn.__builtins__:
                bindings[name]=fn.__builtins__[name]
        function_closure.append(dict(label=label,function=fn,code=code,globals=fn.__globals__,
            builtins=fn.__builtins__,defaults=fn.__defaults__,kwdefaults=fn.__kwdefaults__,
            path=path,body=path.read_bytes(),bindings=bindings))
    for label,fn in selected_functions.items():
        bind_function(label,fn,True)
    # Reached core reflection and alias construction/rendering dependencies: retain ACTUAL defaults.
    reflection=[]
    reflection_classes=['_BaseGenericAlias','_GenericAlias','GenericAlias','_SpecialGenericAlias',
        '_SpecialForm','ParamSpec','TypeVar','TypeVarTuple','_AnnotatedAlias','_CallableGenericAlias']
    for name in reflection_classes:
        if hasattr(typing,name):
            reflection.append((typing,name,getattr(typing,name)))
    for name in ['_should_unflatten_callable_args','_type_check','_type_convert','_type_repr',
            '_is_param_expr','_collect_type_parameters','_unpack_args','_is_unpacked_typevartuple']:
        if hasattr(typing,name):
            obj=getattr(typing,name);reflection.append((typing,name,obj))
            if inspect.isfunction(obj):
                bind_function('typing.'+name,obj)
    reflection.append((dataclasses,'_FIELDS',dataclasses._FIELDS))
    reflection.append((typing,'List',typing.List))
    alias_class=type(target)
    alias_descriptors={}
    for cls in [alias_class,type(typing.List),typing._BaseGenericAlias]:
        for name in ['__init__','__getitem__','__getattr__','__repr__','copy_with']:
            if hasattr(cls,name):
                value=inspect.getattr_static(cls,name);alias_descriptors[(cls,name)]=value
                fn=method_fn(value)
                # _tp_cache wrappers retain their actual callable closure/defaults too.
                if inspect.isfunction(fn):
                    bind_function(cls.__name__+'.'+name,fn)
                    wrapped=getattr(fn,'__wrapped__',None)
                    if inspect.isfunction(wrapped):bind_function(cls.__name__+'.'+name+'.wrapped',wrapped)
    exception_functions=[source_error.__str__]
    for fn in exception_functions:
        if inspect.isfunction(fn):bind_function('DecodingError.'+fn.__name__,fn)
    exception_init=source_error.__init__;exception_str=source_error.__str__
    native_descriptors={n:inspect.getattr_static(int,n) for n in ['from_bytes','to_bytes','bit_length']}
    def live_provenance():
        return dict(rlp_body=rlp_path.read_bytes(),numeric_body=numeric_path.read_bytes(),
            encode=rlp.encode,encode_code=rlp.encode.__code__,encode_defaults=rlp.encode.__defaults__,
            encode_kwdefaults=rlp.encode.__kwdefaults__,get_origin=rlp.get_origin,get_args=rlp.get_args,
            Uint_to_be_bytes=inspect.getattr_static(numeric.Uint,'to_be_bytes'),is_dataclass=rlp.is_dataclass)
    expected=live_provenance()
    def identities():
        provenance(live_provenance(),expected)
        admit_alias(alias_descriptor(target,original),alias_expected,original)
        if (numeric.Uint is not original or numeric.U256 is not u256 or rlp.Uint is not original
                or rlp.FixedUnsigned is not numeric.FixedUnsigned or rlp.List is not typing.List
                or rlp.Bytes is not bytes or bytes_module.Bytes is not bytes
                or original.__bases__!=(numeric.Unsigned,) or original.__mro__!=(original,numeric.Unsigned,object)
                or inspect.getattr_static(original,'_number') is not original_slot
                or (original.__name__,original.__qualname__,original.__module__)!=('Uint','Uint','ethereum_types.numeric')
                or rlp.DecodingError is not source_error or exceptions.DecodingError is not source_error
                or source_error.__init__ is not exception_init or source_error.__str__ is not exception_str):
            raise ImportError('original class/alias/exception drift')
        for n,fn in functions.items():
            if getattr(rlp,n) is not fn or fn.__globals__ is not rlp.__dict__:
                raise ImportError('original RLP function/globals drift: '+n)
        for n,method in methods.items():
            if inspect.getattr_static(original,n) is not method:
                raise ImportError('original inherited numeric descriptor drift: '+n)
        for owner,name,value in reflection:
            if getattr(owner,name) is not value:
                raise ImportError('original reflection helper/class drift: '+name)
        for (cls,name),value in alias_descriptors.items():
            if inspect.getattr_static(cls,name) is not value:
                raise ImportError('original alias constructor/renderer descriptor drift')
        for name,value in native_descriptors.items():
            if inspect.getattr_static(int,name) is not value:
                raise ImportError('native integer descriptor drift')
        for row in function_closure:
            fn=row['function'];code=row['code'];path=row['path']
            if (fn.__code__ is not code or fn.__globals__ is not row['globals']
                    or fn.__builtins__ is not row['builtins'] or fn.__defaults__ is not row['defaults']
                    or fn.__kwdefaults__ is not row['kwdefaults'] or path.read_bytes()!=row['body']
                    or code!=fresh_codes(path).get(code.co_qualname)):
                raise ImportError('original function/code/default closure drift: '+row['label'])
            for name,value in row['bindings'].items():
                live=fn.__globals__[name] if name in fn.__globals__ else fn.__builtins__[name]
                if live is not value:
                    raise ImportError('original scoped global/builtin drift: '+name)
    lock=tomllib.loads((context.eels/'uv.lock').read_text());wheel_dir=wheel_args.wheel_dir.resolve()
    wheel_receipts=[]
    for package,version,folder,wanted in [('ethereum-rlp','0.1.6','ethereum_rlp',
            'f4144caa96b975720c62b967bbfd6c98601e95ee3c36457ece11ef4ce0cffa04'),
            ('ethereum-types','0.4.1','ethereum_types',
            '33de3e2a0c0e57ea1b67802485de556b92d557aae7c8c640070800f2b4f639e3')]:
        wheel=wheel_dir/(package.replace('-','_')+'-'+version+'-py3-none-any.whl')
        digest=hashlib.sha256(wheel.read_bytes()).hexdigest()
        entries=[p for p in lock['package'] if p['name']==package and p['version']==version]
        if digest!=wanted or len(entries)!=1 or not any(w['hash']=='sha256:'+digest for w in entries[0]['wheels']):
            raise ImportError('original lock wheel differs')
        members=[]
        with zipfile.ZipFile(wheel) as archive:
            for name in archive.namelist():
                if name.startswith(folder+'/') and name.endswith('.py'):
                    installed=context.eels/'.venv/lib/python3.13/site-packages'/name
                    if installed.read_bytes()!=archive.read(name):
                        raise ImportError('installed wheel Python member differs: '+name)
                    members.append(dict(name=name,sha256=hashlib.sha256(archive.read(name)).hexdigest()))
        wheel_receipts.append(dict(path=str(wheel),sha256=digest,members=members))
    def closure():
        identities();auth.check();context.check_dependency();context.check_clean()
        for row in wheel_receipts:
            if hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()!=row['sha256']:
                raise ImportError('original wheel drift')
    def serialize(value):
        if value is target:return dict(retained_alias=alias_metadata)
        if value is original:return dict(original_class='ethereum_types.numeric.Uint')
        if value is u256:return dict(original_class='ethereum_types.numeric.U256')
        if type(value) is original:
            return dict(original_Uint=uint_values([value],original)[0])
        if type(value) is bytes:return dict(native_type='builtins.bytes',bytes=list(value),hex=value.hex())
        if type(value) is list or type(value) is tuple:return [serialize(x) for x in value]
        if type(value) is dict:
            if all(type(k) is str for k in value):
                return {k:serialize(v) for k,v in value.items()}
            # Preserve non-string metadata keys as entries, without coercion/collision.
            return dict(native_type='builtins.dict',entries=[
                dict(key=serialize(k),value=serialize(v)) for k,v in value.items()])
        if type(value) in (str,int,bool,float) or value is None:return value
        if inspect.iscode(value):return dict(code=value.co_qualname,file=value.co_filename,sha256=hashlib.sha256(marshal.dumps(value)).hexdigest())
        if inspect.isfunction(value):return dict(function=value.__qualname__,module=value.__module__,code=serialize(value.__code__))
        if type(value) is type:return dict(original_type_module=value.__module__,name=value.__name__,qualname=value.__qualname__,token=id(value))
        if type(value) is u256:return dict(original_U256_fixture=True,number_type=type(value._number).__name__,number=value._number)
        return dict(native_type=type(value).__module__+'.'+type(value).__qualname__,token=id(value))
    runtime=dict(executable=sys.executable,version=sys.version,prefix=sys.prefix,base_prefix=sys.base_prefix,
        flags=repr(sys.flags),original_argv=sys.orig_argv,effective_argv=sys.argv,cwd=str(Path.cwd()))
    closure()
    if helpers_only:
        helpers=helper_controls(original,u256,target,expected,alias_expected,serialize)
        closure();print(json.dumps(dict(profile='helpers-only',runtime=runtime,**helpers),sort_keys=True));return 0
    # Source profile never reexecutes helpers or their constructors.
    setups={n:original(request(n)) for n in [0,1,128,255,256]}
    uint_values(list(setups.values()),original)
    records=[];guards=['import STFSpec.Codec','open STFSpec.Codec STFSpec.Codec.Rlp\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000']
    counts=dict(encode=0,decode=0,decode_ok=0,typed_error=0,raw_error=0)
    call_path=context.output.with_suffix('.calls.jsonl')
    observation_path=context.output.with_suffix('.observations.json')
    if any(p.exists() for p in [context.output,call_path,observation_path]):
        raise FileExistsError('fresh source evidence destination required')
    def retain(event):
        with call_path.open('a') as out:out.write(json.dumps(serialize(event),sort_keys=True)+'\n')
    def trace(exc,wire,raw_expected,index):
        frames=[];all_frames=[];authenticated=True;fields={};raw_tokens=[];child_tokens=[]
        tb=exc.__traceback__
        while tb:
            frame=tb.tb_frame;code=frame.f_code;local=frame.f_locals
            row=dict(file=code.co_filename,function=code.co_name,line=tb.tb_lineno,
                code_sha256=hashlib.sha256(marshal.dumps(code)).hexdigest(),
                original_code=False,original_globals=False)
            if code.co_filename==str(rlp_path):
                row.update(original_code=codes.get(code.co_name) is code,original_globals=frame.f_globals is rlp.__dict__)
                authenticated=authenticated and row['original_code'] and row['original_globals']
                frames.append([code.co_name,tb.tb_lineno])
                if code.co_name=='decode_to':
                    fields['alias_exact']=local['cls'] is target
                    fields['wire_exact']=local['encoded_data'] is wire
                    row['target_exact']=local['cls'] is target
                    row['wire_exact']=local['encoded_data'] is wire
                    if 'decoded' in local:raw_tokens.append(local['decoded']);row['decoded']=model_observation(local['decoded'])
                elif code.co_name=='deserialize_to':
                    want=original if tb.tb_lineno==205 else target
                    authenticated=authenticated and local['class_'] is want
                    row['target_exact']=local['class_'] is want;row['value']=model_observation(local['value'])
                    (child_tokens if want is original else raw_tokens).append(local['value'])
                elif code.co_name=='_deserialize_to_annotation':
                    fields['alias_exact']=local['annotation'] is target
                    row['annotation_exact']=local['annotation'] is target;raw_tokens.append(local['value'])
                elif code.co_name=='_deserialize_to_list':
                    fields['alias_exact']=local['annotation'] is target
                    raw_tokens.append(local['values']);row['values']=model_observation(local['values'])
                    if index is not None:
                        fields.update(argument_exact=local['argument'] is original,index=local['index'])
                        child_tokens.append(local['value']);row.update(index=local['index'],child=model_observation(local['value']),argument_exact=local['argument'] is original)
                elif code.co_name=='_deserialize_to_uint':
                    fields['argument_exact']=local['class_'] is original
                    child_tokens.append(local['decoded']);row.update(target_exact=local['class_'] is original,decoded=model_observation(local['decoded']))
            elif code is observe.__code__:
                row.update(driver_call_frame=True,original_code=True,original_globals=frame.f_globals is globals())
            else:
                authenticated=False
            all_frames.append(row);tb=tb.tb_next
        if raw_tokens:
            raw=raw_tokens[0];fields['raw']=model_observation(raw)
            fields['raw_identity']=all(x is raw for x in raw_tokens)
            if index is not None:
                require_type(raw,list)
                fields['child_identity']=all(x is raw[index] for x in child_tokens)
        elif raw_expected is not None and index is not None and child_tokens:
            # Leaf traceback has its list frame, so absence of that raw is unadmitted.
            fields['raw_identity']=False
        if child_tokens:fields['child']=model_observation(child_tokens[0])
        if index is None and raw_tokens:fields['argument_exact']=True
        if 'index' not in fields and index is None:fields['index']=None
        if type(exc.args) is not tuple or any(type(x) is not str for x in exc.args):authenticated=False
        cause=exc.__cause__;context_exc=exc.__context__
        result=dict(exact=type(exc) is source_error,authenticated=authenticated,
            exception_class=type(exc).__module__+'.'+type(exc).__qualname__,args=list(exc.args),
            message=str(exc),frames=frames,traceback=all_frames,
            cause=trace(cause,wire,raw_expected,index) if cause is not None else None,
            context=context_exc is not None,suppressed=exc.__suppress_context__,
            context_same_cause=cause is not None and context_exc is cause,
            context_detail=trace(context_exc,wire,raw_expected,index)
                if context_exc is not None and context_exc is not cause else None)
        result.update(fields)
        if raw_tokens:result['raw_token']=id(raw_tokens[0])
        if child_tokens:result['child_token']=id(child_tokens[0])
        return result
    def lean_bytes(data):
        literal_wire(data)
        return '(ByteArray.mk ('+str(list(data))+' : List UInt8).toArray)'
    def result_guard(expr,result):
        return ('#guard (match ('+expr+'), '+result+' with | .ok a, .ok b => decide (a = b) '
            '| .error a, .error b => decide (a = b) | _, _ => false)')
    for i,(numbers,wire_hex) in enumerate(SUCCESS,1):
        case=f'E{i:02}';source_input=[setups[n] for n in numbers]
        actual_numbers=uint_output(source_input,original,numbers);wire_expected=bytes.fromhex(wire_hex)
        guard=f'#guard encodeOf ({actual_numbers} : List Nat) = {lean_bytes(wire_expected)}'
        record=dict(id=case,operation='encode',input=actual_numbers,expected_wire=list(wire_expected),guard=guard)
        retain(dict(record,event='planned-before-entry'));identities();counts['encode']+=1
        try:wire=functions['encode'](source_input)
        except BaseException:
            retain(dict(record,event='unexpected-source-encode-failure'));raise
        literal_wire(wire)
        if wire!=wire_expected:raise RuntimeError('entire source wire differs: '+case)
        uint_output(source_input,original,numbers);identities()
        record.update(result='ok',wire=list(wire),wire_hex=wire.hex(),input_native_type='builtins.list',
            child_native_type='ethereum_types.numeric.Uint',projection_after_native_admission=True)
        records.append(record);retain(dict(record,event='observed'));guards.append(guard+' -- G'+case)
    def observe(case,wire,numbers=None,kind=None,raw=None,index=None,site=None,error=None,raw_case=0):
        literal_wire(wire);expr=f'decodeTo (α := List Nat) {lean_bytes(wire)}'
        result=(f'(Except.ok {numbers} : Except RlpError (List Nat))' if kind is None else
            f'(Except.error ({error}) : Except RlpError (List Nat))')
        guard=result_guard(expr,result)
        record=dict(id=case,operation='decode_to',wire=list(wire),wire_hex=wire.hex(),
            expected_numbers=numbers,expected_raw=model_observation(raw) if raw is not None else None,
            expected_error=error,phase=kind,index=index,site=site,lean_expression=expr,
            lean_result=result,guard=guard,lean_common_expression=f'({expr}).mapError (fun (_ : RlpError) => ())')
        retain(dict(record,event='planned-before-entry'));identities();counts['decode']+=1
        try:value=functions['decode_to'](target,wire)
        except BaseException as exc:
            event=trace(exc,wire,raw,index)
            retain(dict(record,event='observed-exception-before-admission',exception=event))
            if kind is None:raise
            admitted=admit_event(event,kind,target,original,index=index,site=site,raw=raw,raw_case=raw_case)
            if admitted!=(error,kind,site):raise RuntimeError('complete source exception differs: '+case)
            if kind=='typed':
                middle=event['cause'];leaf=middle['cause']
                if (event['raw_token']!=middle['raw_token'] or
                        (leaf is not None and (middle['raw_token']!=leaf['raw_token'] or middle['child_token']!=leaf['child_token']))):
                    raise RuntimeError('actual traceback raw/child identity differs')
            counts[kind+'_error']+=1
            record.update(result='error',exception=event,common_channel=dict(type='Except Unit (List Nat)',constructor='error'))
        else:
            actual=uint_output(value,original,numbers if numbers is not None else [])
            if kind is not None:raise RuntimeError('unexpected source success: '+case)
            counts['decode_ok']+=1
            record.update(result='ok',values=actual,result_native_type='builtins.list',child_native_type='ethereum_types.numeric.Uint',
                projection_after_native_admission=True,common_channel=dict(type='Except Unit (List Nat)',constructor='ok',values=actual))
        identities();records.append(record);retain(dict(record,event='observed'));guards.append(guard+' -- G'+case)
    for i,(numbers,wire_hex) in enumerate(SUCCESS,1):observe(f'D{i:02}',bytes.fromhex(wire_hex),numbers=numbers)
    for i,(wire_hex,raw,index,site,error) in enumerate(TYPED,1):
        observe(f'T{i:02}',bytes.fromhex(wire_hex),kind='typed',raw=raw,index=index,site=site,error=error)
    for i,(wire_hex,args,frames,error) in enumerate(RAW,1):
        observe(f'R{i:02}',bytes.fromhex(wire_hex),kind='raw',site=frames[-1][1],error=error,raw_case=i-1)
    if counts!=dict(encode=8,decode=20,decode_ok=8,typed_error=6,raw_error=6) or len(records)!=28 or len(guards)!=30:
        raise RuntimeError('released exact source inventory differs')
    if max(len(r['wire']) for r in records)!=58:raise RuntimeError('released wire bound differs')
    closure()
    identity=dict(runtime=runtime,alias=alias_metadata,alias_parameterizations=1,
        Uint=dict(name=original.__name__,qualname=original.__qualname__,module=original.__module__,
            bases=[x.__module__+'.'+x.__qualname__ for x in original.__bases__],
            mro=[x.__module__+'.'+x.__qualname__ for x in original.__mro__],slot_type=type(original_slot).__name__),
        function_closure=[dict(label=r['label'],file=str(r['path']),line=r['code'].co_firstlineno,
            code_sha256=hashlib.sha256(marshal.dumps(r['code'])).hexdigest(),source_sha256=hashlib.sha256(r['body']).hexdigest(),
            defaults=serialize(r['defaults']),kwdefaults=serialize(r['kwdefaults']),
            bindings={n:serialize(v) for n,v in r['bindings'].items()}) for r in function_closure],
        sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in auth.expected},
        rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),types_sources=context.dependency_sources(),
        types_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest(),wheels=wheel_receipts,
        wheel_directory=dict(supplied=str(wheel_args.wheel_dir),resolved=str(wheel_dir)))
    observation_path.write_text(json.dumps(dict(seed=30001,cases=serialize(records),identities=identity,
        counts=counts,direct_constructor_setups=5,alias_parameterizations=1,
        helpers=dict(total_negatives=40,total_positives=8,execution='separate final normal/-O runs; not repeated'),
        static_intrinsic_constructor_prediction=125,intrinsic_prediction_is_dynamic_trace=False,
        max_wire=58,max_list_length=56,max_raw_depth=2,max_natural=256,
        trust='finite authentic intended-class correspondence; native/interpreter/startup/install/RECORD/host/orchestration/compiler/kernel trusted'),indent=2)+'\n')
    closure()
    result=context.run(guards,counts=counts,observations=str(observation_path),
        domain='one authentic retained typing.List[original Uint]; seed30001; no RNG/replay/extra decode')
    closure();return result


if __name__=='__main__':
    raise SystemExit(main())
