#!/usr/bin/env python3
"""Source-bound E3 actual-cell baseline/mutation runner. Results are external."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

REQUIRED = frozenset(('checks/e3_model_cells.py','checks/run_e3_checks.py',
                      'checks/test_e3_guards.py','checks/README.md'))
MUTATIONS = ('omit_grade_inverse','sort_graph_partition','erase_graph_scalar','drop_nullary_scalar',
             'forget_comparison_scalar','forget_refinement_slots','drop_pullback_fibre','erase_unary_graph_profile')

def need(ok,message):
    if not ok: raise RuntimeError(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def source_state(root):
    manifest=root/'checks/source_scope_manifest.json'
    raw=manifest.read_bytes();record=json.loads(raw)
    need(record.get('schema')=='E3 finite source scope v1','source manifest schema')
    files=record.get('files',{})
    need(REQUIRED <= files.keys(),'source manifest omits mandatory input')
    actual={}
    for name,digest in sorted(files.items()):
        rel=Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts and rel.as_posix()==name,'nonportable source path')
        path=root/rel
        need(path.is_file() and not path.is_symlink(),'source must be regular file: '+name)
        need(root in path.resolve().parents,'source path escapes source tree')
        actual[name]=sha(path.read_bytes())
        need(actual[name]==digest,'source drift: '+name)
    return sha(raw),actual

def output_is_protected(root,output):
    resolved=output.expanduser().resolve()
    if resolved==root or root in resolved.parents: return True
    if resolved.exists():
        for path in root.rglob('*'):
            if path.is_file() and path.samefile(resolved): return True
    return False

def run():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parent.parent
    if output_is_protected(root,a.output):
        print(json.dumps({'status':'REJECT','reason':'output must be outside source tree and not alias a source file'},sort_keys=True));return 2
    output=a.output.expanduser().resolve()
    try:
        before=source_state(root)
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
        modes={'normal':[],'-O':['-O'],'-OO':['-OO']};baselines={};exact=None;data=None
        script=root/'checks/e3_model_cells.py'
        for mode,flags in modes.items():
            result=subprocess.run([sys.executable,'-B',*flags,str(script),'--expect-optimize',str({'normal':0,'-O':1,'-OO':2}[mode])],cwd=root,env=env,capture_output=True,timeout=600)
            need(result.returncode==0,'baseline failed in '+mode+': '+result.stdout.decode(errors='replace')+result.stderr.decode(errors='replace'))
            need(not result.stderr,'unexpected baseline stderr')
            observed=json.loads(result.stdout);need(observed.get('status')=='PASS','baseline status')
            if exact is None: exact=result.stdout;data=observed
            need(exact==result.stdout,'optimization changed exact baseline bytes')
            baselines[mode]={'status':'PASS','stdout_sha256':sha(result.stdout)}
        mutations={}
        for mutation in MUTATIONS:
            prior=None
            for mode,flags in modes.items():
                result=subprocess.run([sys.executable,'-B',*flags,str(script),'--expect-optimize',str({'normal':0,'-O':1,'-OO':2}[mode]),'--mutate',mutation],cwd=root,env=env,capture_output=True,timeout=600)
                need(result.returncode==1,'semantic mutation escaped rejection: '+mutation+'/'+mode)
                need(not result.stderr,'semantic mutation crashed: '+mutation+'/'+mode)
                observed=json.loads(result.stdout)
                need(observed.get('status')=='REJECT' and observed.get('mutation')==mutation,'mutation rejection metadata')
                if prior is None: prior=result.stdout
                need(prior==result.stdout,'optimization changed semantic mutation rejection')
                mutations[mutation+'/'+mode]=observed
        after=source_state(root);need(before==after,'source changed during verification; invalid receipt')
        receipt={'status':'PASS','schema':'E3 finite verification receipt v1','source_manifest_sha256':before[0],
                 'source_sha256':before[1],'optimization_modes':baselines,'semantic_mutation_controls':mutations,
                 'finite_evidence':data,'limits':['Bounded actual-cell regressions, not the uniform P proofs.',
                 'Full Span model includes noninvertible vertical maps; graph groupoid finite slice does not replace it.',
                 'Typed core Lean bridge is verified separately; no full E3 mechanization claimed.']}
        code=0
    except (RuntimeError,OSError,ValueError,subprocess.TimeoutExpired) as err:
        receipt={'status':'REJECT','reason':str(err)};code=1
    rendered=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    # Recheck destination after tests, then replace an external temporary sibling.
    need(not output_is_protected(root,output),'output alias changed during verification')
    output.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=output.parent,prefix='.e3_receipt_',delete=False) as f:
        temporary=Path(f.name);f.write(rendered);f.flush();os.fsync(f.fileno())
    temporary.replace(output)
    sys.stdout.write(rendered);return code

if __name__=='__main__': raise SystemExit(run())
