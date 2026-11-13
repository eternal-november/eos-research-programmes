#!/usr/bin/env python3
"""Adversarial output/source/mode guards, isolated copies, no source mutation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def need(b,m):
    if not b: raise RuntimeError(m)

def hash_file(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent;destination=args.output.expanduser().resolve()
    need(destination!=root and root not in destination.parents,'guard receipt outside source tree')
    if destination.exists(): need(not any(p.is_file() and p.samefile(destination) for p in root.rglob('*')),'guard receipt not source hard link')
    manifest=json.loads((root/'checks/source_scope_manifest.json').read_text())
    initial={name:hash_file(root/name) for name in manifest['files']}
    results={}
    with tempfile.TemporaryDirectory(prefix='e3_guards_') as directory:
        work=Path(directory);clone=work/'source';clone.mkdir()
        for name in manifest['files']:
            p=clone/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(root/name,p)
        shutil.copy2(root/'checks/source_scope_manifest.json',clone/'checks/source_scope_manifest.json')
        runner=clone/'checks/run_e3_checks.py';source=clone/'checks/e3_model_cells.py'
        original=source.read_bytes();manifest_path=clone/'checks/source_scope_manifest.json';manifest_bytes=manifest_path.read_bytes()
        symbolic=work/'source-link';symbolic.symlink_to(source)
        dirlink=work/'directory-link';dirlink.symlink_to(clone/'checks',target_is_directory=True)
        hardlink=work/'hard-link';os.link(source,hardlink)
        cases={'self':runner,'source':source,'manifest':manifest_path,'new-inside':clone/'receipt.json',
               'root-directory':clone,'symbolic-file':symbolic,'symbolic-parent':dirlink/'new.json',
               'hard-link':hardlink,'dotdot':work/'source'/'checks'/'..'/'bad.json'}
        for name,output in cases.items():
            p=subprocess.run([sys.executable,'-B',str(runner),'--output',str(output)],capture_output=True)
            need(p.returncode==2 and json.loads(p.stdout)['status']=='REJECT','output guard '+name)
            need(source.read_bytes()==original and manifest_path.read_bytes()==manifest_bytes,'guard source was mutated')
            results['output/'+name]='PASS'
        # Tamper changes happen only to a disposable copy. Refusal is before baselines.
        for name in ('source-drift','missing-mandatory','traversal','wrong-schema'):
            if name=='source-drift': source.write_bytes(original+b'\n# disposable drift\n')
            else:
                data=json.loads(manifest_bytes)
                if name=='missing-mandatory': del data['files']['checks/e3_model_cells.py']
                elif name=='traversal': data['files']['../outside']=hash_file(source)
                else: data['schema']='wrong schema'
                manifest_path.write_text(json.dumps(data))
            receipt=work/(name+'.json')
            p=subprocess.run([sys.executable,'-B',str(runner),'--output',str(receipt)],capture_output=True)
            need(p.returncode==1 and json.loads(receipt.read_text())['status']=='REJECT','source guard '+name)
            results['source/'+name]='PASS';source.write_bytes(original);manifest_path.write_bytes(manifest_bytes)
        # Wrong claimed mode is rejected inside the actual semantic subprocess.
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
        for flag,actual in (((),0),(('-O',),1),(('-OO',),2)):
            p=subprocess.run([sys.executable,'-B',*flag,str(source),'--expect-optimize',str((actual+1)%3)],
                             env=env,capture_output=True,text=True)
            data=json.loads(p.stdout)
            need(p.returncode==1 and data['status']=='REJECT' and data['reason']=='interpreter optimization mode mismatch',
                 'actual semantic subprocess rejects wrong claimed mode')
            results['mode/'+str(actual)]='PASS'
    need(initial=={name:hash_file(root/name) for name in manifest['files']},'real source changed during guards')
    receipt={'status':'PASS','schema':'E3 guard verification v1','results':results,'source_sha256':initial}
    destination.parent.mkdir(parents=True,exist_ok=True);destination.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True));return 0

if __name__=='__main__': raise SystemExit(main())
