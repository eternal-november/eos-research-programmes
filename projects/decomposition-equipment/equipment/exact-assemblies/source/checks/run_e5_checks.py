#!/usr/bin/env python3
"""Frozen relative-source E5 replay. All receipts must be external to sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

REQUIRED=frozenset(('checks/e5_exact_cells.py','checks/run_e5_checks.py','checks/test_e5_guards.py',
                    'checks/README.md','checks/dependencies/e4_completion_cells.py',
                    'checks/dependencies/dependencies/e3_model_cells.py'))
DEPENDENCIES={
 'checks/dependencies/e4_completion_cells.py':'32cf6e969554d593f76e905339bcca7ac71e17a1da345b390b8030f4bf71cb30',
 'checks/dependencies/dependencies/e3_model_cells.py':'5941532e760980f0324a958d094e06396010c4d88db7883caa0008ed3edcbfcb'}
MUTATIONS=('deduplicate_internal_lifts','endpoint_support_is_coefficient','check_only_adjacent_runs','nullary_empty_product',
'rotate_tree_coefficient','root_only_reconstruction','drop_nullary_stage_scalar','quotient_invariant_is_existential','forget_cross_edges')
OLD_ROOTS=tuple(Path('/workspace/shared')/name for name in (
 'contract_revision_20261028','i4_mixed_interchange_20261031','d2_d3_interface_descent_20261031',
 'e2_presentation_reconstruction_20261031','e3_substantive_models_20261031',
 'e4_ordinary_completion_20261031','e5_exact_assembly_transport_20261031'))

def need(ok,message):
    if not ok: raise RuntimeError(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def protected_roots(root): return (root,)+tuple(p.resolve() for p in OLD_ROOTS)

def output_is_protected(root,output):
    resolved=output.expanduser().resolve()
    for protected in protected_roots(root):
        if resolved==protected or protected in resolved.parents: return True
    if resolved.exists():
        for protected in protected_roots(root):
            for path in protected.rglob('*'):
                if path.is_file() and path.samefile(resolved): return True
    return False

def source_state(root):
    manifest=root/'checks/source_scope_manifest.json'
    need(manifest.is_file() and not manifest.is_symlink(),'source manifest must be a regular file')
    raw=manifest.read_bytes();record=json.loads(raw)
    need(record.get('schema')=='E5 finite source scope v1','source manifest schema')
    files=record.get('files',{})
    need(REQUIRED==files.keys(),'source manifest must bind exactly the declared finite sources')
    need(all(files[name]==digest for name,digest in DEPENDENCIES.items()),'frozen E3/E4 dependency identities')
    actual={}
    for name,digest in sorted(files.items()):
        rel=Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts and rel.as_posix()==name,'nonportable source path')
        path=root/rel
        need(path.is_file() and not any(p.is_symlink() for p in (path,*path.parents) if p!=root and root in p.parents),
             'source must be a non-symlink regular file: '+name)
        need(root in path.resolve().parents,'source path escapes source tree')
        actual[name]=sha(path.read_bytes())
        need(actual[name]==digest,'source drift: '+name)
    return sha(raw),actual

def atomic_external_write(root,output,rendered):
    need(not output_is_protected(root,output),'output aliases protected source')
    output.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=output.parent,prefix='.e5_receipt_',delete=False) as f:
        temporary=Path(f.name);f.write(rendered);f.flush();os.fsync(f.fileno())
    need(not output_is_protected(root,output),'output alias changed during receipt publication')
    temporary.replace(output)

def run():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parent.parent
    if output_is_protected(root,a.output):
        print(json.dumps({'status':'REJECT','reason':'output must be outside protected source trees and not alias a source file'},sort_keys=True));return 2
    output=a.output.expanduser().resolve()
    try:
        before=source_state(root)
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
        modes={'normal':[],'-O':['-O'],'-OO':['-OO']};baselines={};exact=None;data=None
        script=root/'checks/e5_exact_cells.py'
        for mode,flags in modes.items():
            result=subprocess.run([sys.executable,'-B',*flags,str(script),'--expect-optimize',str({'normal':0,'-O':1,'-OO':2}[mode])],
                                  cwd=root,env=env,capture_output=True,timeout=120)
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
                result=subprocess.run([sys.executable,'-B',*flags,str(script),'--expect-optimize',str({'normal':0,'-O':1,'-OO':2}[mode]),'--mutate',mutation],
                                      cwd=root,env=env,capture_output=True,timeout=120)
                need(result.returncode==1,'semantic mutation escaped rejection: '+mutation+'/'+mode)
                need(not result.stderr,'semantic mutation crashed: '+mutation+'/'+mode)
                observed=json.loads(result.stdout)
                need(observed.get('status')=='REJECT' and observed.get('mutation')==mutation,'semantic mutation metadata')
                if prior is None: prior=result.stdout
                need(prior==result.stdout,'optimization changed semantic mutation rejection')
                mutations[mutation+'/'+mode]=observed
        after=source_state(root);need(before==after,'source changed during verification; invalid receipt')
        receipt={'status':'PASS','schema':'E5 finite verification receipt v1','source_manifest_sha256':before[0],
                 'source_sha256':before[1],'optimization_modes':baselines,'semantic_mutation_controls':mutations,
                 'finite_evidence':data,'limits':data['limits']};code=0
    except (RuntimeError,OSError,ValueError,subprocess.TimeoutExpired) as error:
        receipt={'status':'REJECT','reason':str(error)};code=1
    rendered=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    atomic_external_write(root,output,rendered)
    sys.stdout.write(rendered);return code

if __name__=='__main__': raise SystemExit(run())
