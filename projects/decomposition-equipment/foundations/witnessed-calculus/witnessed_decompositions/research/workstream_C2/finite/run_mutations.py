#!/usr/bin/env python3
"""Execute actual in-memory C2 source mutants against the unchanged tests.

No checkpoint source is edited. Each mutant gets an isolated Python namespace,
and PASS means the named test raises AssertionError/ValueError as expected.
This is C negative-control evidence, not a kernel theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import types

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'check_c2_model.py'
MUTATIONS=(
    ('reverse_containment',
     'if self.profile.composite.mask & ~self.whole.mask:',
     'if self.whole.mask & ~self.profile.composite.mask:',
     'named_checks'),
    ('conflate_pulled_composite_with_composite_of_pulls',
     'composed=join(ap,bp,cp,rp,sp)',
     'composed=pull(a,c,original,f,h)',
     'exhaustive_f1'),
    ('identify_repeated_occurrence_replacements',
     'children = tuple(children)\n    if tuple(c.whole for c in children)',
     'children = tuple(children)\n    first = {}\n    children = tuple(first.setdefault(c.whole, c) for c in children)\n    if tuple(c.whole for c in children)',
     'named_checks'),
    ('empty_path_composite_is_empty_relation',
     'out = diagonal(sizes[0])',
     'out = 0 if not relations else diagonal(sizes[0])',
     'named_checks'),
)

def run():
    source=SOURCE.read_text(); rows=[]
    for name,old,new,test in MUTATIONS:
        assert source.count(old)==1, (name,'mutation anchor must be unique')
        mutant=source.replace(old,new,1)
        module=types.ModuleType('_c2_mutant_'+name)
        module.__file__=str(SOURCE)
        sys.modules[module.__name__]=module
        exec(compile(mutant,str(SOURCE)+' [mutant '+name+']','exec'),module.__dict__)
        try:
            module.__dict__[test]()
        except (AssertionError,ValueError) as exc:
            rows.append({'mutation':name,'test':test,'detected':True,
                         'failure_type':type(exc).__name__,'message':str(exc),
                         'mutant_sha256':hashlib.sha256(mutant.encode()).hexdigest()})
        else:
            raise AssertionError('undetected mutant: '+name)
        finally:
            del sys.modules[module.__name__]
    return {'schema':'C2-executed-mutations-v1','status':'PASS',
            'original_source_sha256':hashlib.sha256(source.encode()).hexdigest(),
            'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'mutations':rows}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    text=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text)
