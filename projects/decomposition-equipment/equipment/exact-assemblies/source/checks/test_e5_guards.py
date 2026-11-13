#!/usr/bin/env python3
"""Isolated-copy negative guard tests. Never changes original or final sources."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

spec=importlib.util.spec_from_file_location('e5_runner',Path(__file__).resolve().with_name('run_e5_checks.py'))
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)

def need(b,m):
    if not b: raise RuntimeError(m)

def hash_file(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent
    if r.output_is_protected(root,args.output):
        print(json.dumps({'status':'REJECT','reason':'guard output aliases protected source'},sort_keys=True));return 2
    destination=args.output.expanduser().resolve();before=r.source_state(root)
    manifest=json.loads((root/'checks/source_scope_manifest.json').read_text());results={}
    env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    with tempfile.TemporaryDirectory(prefix='e5_guards_') as directory:
        work=Path(directory);clone=work/'source';clone.mkdir()
        for name in manifest['files']:
            p=clone/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(root/name,p)
        shutil.copy2(root/'checks/source_scope_manifest.json',clone/'checks/source_scope_manifest.json')
        runner=clone/'checks/run_e5_checks.py';source=clone/'checks/e5_exact_cells.py'
        dependency=clone/'checks/dependencies/dependencies/e3_model_cells.py'
        original=source.read_bytes();dep_bytes=dependency.read_bytes()
        manifest_path=clone/'checks/source_scope_manifest.json';manifest_bytes=manifest_path.read_bytes()
        symbolic=work/'source-link';symbolic.symlink_to(source)
        dirlink=work/'directory-link';dirlink.symlink_to(clone/'checks',target_is_directory=True)
        hardlink=work/'hard-link';os.link(source,hardlink)
        cases={'self':runner,'source':source,'manifest':manifest_path,'dependency':dependency,
               'new-inside':clone/'receipt.json','root-directory':clone,'symbolic-file':symbolic,
               'symbolic-parent':dirlink/'new.json','hard-link':hardlink,'dotdot':clone/'checks'/'..'/'bad.json'}
        # Old source protection is exercised without writing to any old source.
        cases['old-source-tree']=r.OLD_ROOTS[4]/'checks/new_e5_receipt.json'
        cases['original-E5-tree']=r.OLD_ROOTS[-1]/'checks/new_e5_receipt.json'
        for name,output in cases.items():
            for flag in ((),('-O',),('-OO',)):
                p=subprocess.run([sys.executable,'-B',*flag,str(runner),'--output',str(output)],env=env,capture_output=True)
                need(p.returncode==2 and json.loads(p.stdout)['status']=='REJECT','output guard '+name)
                need(source.read_bytes()==original and manifest_path.read_bytes()==manifest_bytes and dependency.read_bytes()==dep_bytes,
                     'guard source was mutated')
                results['output/'+name+'/'+str(len(flag) and (1 if flag==('-O',) else 2) or 0)]='PASS'
        for name in ('source-drift','dependency-drift','missing-mandatory','extra-traversal','wrong-schema','source-symlink'):
            for flag in ((),('-O',),('-OO',)):
                if name=='source-drift': source.write_bytes(original+b'\n# disposable drift\n')
                elif name=='dependency-drift': dependency.write_bytes(dep_bytes+b'\n# disposable dependency drift\n')
                elif name=='source-symlink':
                    source.unlink();source.symlink_to(root/'checks/e5_exact_cells.py')
                else:
                    data=json.loads(manifest_bytes)
                    if name=='missing-mandatory': del data['files']['checks/e5_exact_cells.py']
                    elif name=='extra-traversal': data['files']['../outside']=hash_file(source)
                    else: data['schema']='wrong schema'
                    manifest_path.write_text(json.dumps(data))
                receipt=work/(name+'.json')
                p=subprocess.run([sys.executable,'-B',*flag,str(runner),'--output',str(receipt)],env=env,capture_output=True)
                need(p.returncode==1 and json.loads(receipt.read_text())['status']=='REJECT','source guard '+name)
                results['source/'+name+'/'+str(len(flag) and (1 if flag==('-O',) else 2) or 0)]='PASS'
                if source.is_symlink(): source.unlink()
                source.write_bytes(original);dependency.write_bytes(dep_bytes);manifest_path.write_bytes(manifest_bytes)
        for flag,actual in (((),0),(('-O',),1),(('-OO',),2)):
            p=subprocess.run([sys.executable,'-B',*flag,str(source),'--expect-optimize',str((actual+1)%3)],env=env,capture_output=True)
            data=json.loads(p.stdout)
            need(p.returncode==1 and data['reason']=='interpreter optimization mode mismatch','actual semantic mode guard')
            results['mode/'+str(actual)]='PASS'
        # This is an actual complete replay under inherited optimization, not an environment-only assertion.
        inherited=env.copy();inherited['PYTHONOPTIMIZE']='2';receipt=work/'inherited-optimize.json'
        p=subprocess.run([sys.executable,'-B',str(runner),'--output',str(receipt)],env=inherited,capture_output=True,timeout=180)
        data=json.loads(receipt.read_text())
        need(p.returncode==0 and data['status']=='PASS' and len(data['optimization_modes'])==3,'inherited optimization reset actual replay')
        results['inherited-PYTHONOPTIMIZE-2/full-replay']='PASS'
    need(before==r.source_state(root),'real source changed during guard tests')
    receipt={'status':'PASS','schema':'E5 guard verification v1','results':results,
             'source_manifest_sha256':before[0],'source_sha256':before[1]}
    rendered=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    r.atomic_external_write(root,destination,rendered);print(rendered,end='');return 0

if __name__=='__main__': raise SystemExit(main())
