"""Adversarial negative controls; no assert disappears under -O."""
import importlib.util
import json
from pathlib import Path

path = Path(__file__).resolve().parents[1] / 'STFSpec/Conformance/Stateless/output_differential.py'
spec = importlib.util.spec_from_file_location('wi356_check_target', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
rows = module.expected_rows()
good = '\n'.join(json.dumps(r) for r in rows) + '\n'
if module.check(good) != 19:
    raise ValueError('positive control rejected')
controls = {'missing': '\n'.join(good.splitlines()[:-1]), 'empty': '', 'extra': good + '{}\n',
            'noise': 'noise\n' + good, 'blank_line': good + '\n',
            'order': '\n'.join(reversed(good.splitlines())), 'truncated_json': good[:-5]}
for key, value in [('wrong_byte', 'ff' + rows[0]['actual_hex'][2:]),
                   ('short', rows[0]['actual_hex'][:-2]),
                   ('long', rows[0]['actual_hex'] + '00'),
                   ('uppercase', rows[2]['actual_hex'].upper()), ('number', 0), ('bool', False)]:
    altered = [dict(r) for r in rows]
    altered[0]['actual_hex'] = value
    controls[key] = '\n'.join(json.dumps(r) for r in altered)
for name, first in [('duplicate_key', '{"name":"zero_false","name":"zero_false","actual_hex":"' + rows[0]['actual_hex'] + '"}'),
                    ('extra_key', json.dumps(dict(rows[0], ignored=True))),
                    ('array', json.dumps(list(rows[0].values()))),
                    ('null', 'null')]:
    controls[name] = first + '\n' + '\n'.join(good.splitlines()[1:])
for name, text in controls.items():
    try:
        module.check(text)
    except (ValueError, TypeError, KeyError):
        continue
    raise ValueError('negative control accepted: ' + name)
print(f'Parser controls passed: 1 positive, {len(controls)} negative.')
