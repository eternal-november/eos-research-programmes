#!/usr/bin/env python3
"""Test immutable-bundle validation and output-alias guards in isolated copies."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import replay_bundle as r

ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise ValueError(message)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    r.external_output(ROOT,args.output)
    before=r.validate(ROOT)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONOPTIMIZE',None)
    results={}
    with tempfile.TemporaryDirectory(prefix='e4-bundle-guards-') as temp:
        work=Path(temp);source=work/'source'
        shutil.copytree(ROOT,source,copy_function=shutil.copyfile)
        for p in [source,*source.rglob('*')]:p.chmod(0o755 if p.is_dir() else 0o644)
        target=source/'theorem.md';original=target.read_bytes()
        manifest_path=source/'source_manifest.json';manifest=manifest_path.read_bytes()
        symlink=work/'symlink';symlink.symlink_to(target)
        hardlink=work/'hardlink';os.link(target,hardlink)
        rootlink=work/'rootlink';rootlink.symlink_to(source,target_is_directory=True)
        for mode,flags in (('normal',()),('-O',('-O',)),('-OO',('-OO',))):
            hardlink.unlink();os.link(target,hardlink)
            def execute(script,arguments):
                return subprocess.run([sys.executable,'-B',*flags,str(source/script),*arguments],env=env,capture_output=True,text=True)
            clean=execute('replay_bundle.py',['--validate-only'])
            need(clean.returncode==0 and json.loads(clean.stdout)['status']=='PASS','Clean validation '+mode)
            results['clean/'+mode]='PASS'
            for label,path in (('direct',target),('new-inside',source/'receipt.json'),('symlink',symlink),('hardlink',hardlink)):
                for script in ('replay_bundle.py','make_source_zip.py'):
                    result=execute(script,['--output',str(path)])
                    need(result.returncode==2 and json.loads(result.stdout)['status']=='REJECT' and not result.stderr,'Output guard '+script+'/'+label+'/'+mode)
                    need(target.read_bytes()==original and manifest_path.read_bytes()==manifest,'Source overwritten by output guard')
                    results['output/'+script+'/'+label+'/'+mode]='PASS'
            for label in ('source-drift','missing-manifest-entry','traversal-entry','source-symlink'):
                if label=='source-drift':target.write_bytes(original+b'\nDISPOSABLE DRIFT\n')
                elif label=='source-symlink':target.unlink();target.symlink_to(ROOT/'theorem.md')
                else:
                    value=json.loads(manifest)
                    if label=='missing-manifest-entry':value.pop('theorem.md')
                    else:value['../outside']={'bytes':0,'sha256':'0'*64}
                    manifest_path.write_text(json.dumps(value))
                result=execute('replay_bundle.py',['--validate-only'])
                need(result.returncode==2 and json.loads(result.stdout)['status']=='REJECT' and not result.stderr,'Manifest/source guard '+label+'/'+mode)
                results['manifest/'+label+'/'+mode]='PASS'
                if target.is_symlink():target.unlink()
                target.write_bytes(original);manifest_path.write_bytes(manifest)
            result=execute('make_source_zip.py',['--source',str(rootlink),'--output',str(work/'forbidden.zip')])
            need(result.returncode==2 and json.loads(result.stdout)['status']=='REJECT','Source-root symlink guard '+mode)
            results['source-root-symlink/'+mode]='PASS'
        r.validate(source)
    need(before==r.validate(ROOT),'Original bundle bytes changed')
    receipt={'status':'PASS','schema':'E4 immutable bundle guard evidence v1','results':results,'source_bytes_unchanged':True}
    r.atomic_write(ROOT,args.output,receipt)
    print(json.dumps(receipt,sort_keys=True,indent=2));return 0
if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,OSError,KeyError,TypeError) as error:
        print(json.dumps({'status':'REJECT','reason':str(error)},sort_keys=True));raise SystemExit(2)
