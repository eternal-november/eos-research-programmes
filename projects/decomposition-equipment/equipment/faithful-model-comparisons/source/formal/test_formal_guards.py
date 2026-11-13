#!/usr/bin/env python3
"""Guards are tested in private source copies; no accepted source is mutated."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,m):
    if not b:raise RuntimeError(m)
def main():
    frozen=json.loads((ROOT/'source_freeze.json').read_text())['sources']
    with tempfile.TemporaryDirectory(prefix='e3_formal_guards_') as td:
        base=pathlib.Path(td);src=base/'formal';src.mkdir()
        for rel in [*frozen,'source_freeze.json']:
            p=src/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/rel,p)
        expected={rel:sha(src/rel) for rel in [*frozen,'source_freeze.json']}
        evidence=base/'external';evidence.mkdir();results=[]
        def check(label,flags,args):
            cp=subprocess.run([sys.executable,*flags,str(src/'verify_fresh.py'),*args],capture_output=True,text=True)
            require(cp.returncode!=0,label+' was accepted')
            try:r=json.loads(cp.stdout)
            except Exception:raise RuntimeError(label+' did not give JSON rejection: '+cp.stdout+cp.stderr)
            require(r.get('status')=='REJECT',label+' did not reject')
            results.append({'name':label,'flags':flags,'returncode':cp.returncode,'reason':r['reason']})
        for flags,mode in [([], 'normal'),(['-O'],'optimized'),(['-OO'],'double-optimized')]:
            out=evidence/(mode+'.json')
            check(mode+'_direct_source',flags,['--output',str(src/'E3GraphGroupoidCore.lean')])
            alias=evidence/(mode+'_symlink.json');alias.symlink_to(src/'source_freeze.json')
            check(mode+'_symlink_source',flags,['--output',str(alias)]);alias.unlink()
            hard=evidence/(mode+'_hardlink.json');os.link(src/'source_freeze.json',hard)
            check(mode+'_hardlink_source',flags,['--output',str(hard)]);hard.unlink()
            check(mode+'_bad_mode',flags,['--output',str(out),'--mode','nonsense'])
            wrong='optimized' if mode=='normal' else 'normal'
            check(mode+'_mismatch',flags,['--output',str(out),'--mode',wrong])
            check(mode+'_work_source',flags,['--output',str(out),'--work-parent',str(src/'original_source')])
            require(not out.exists(),'guard unexpectedly wrote output')
        changed=src/'E3FiniteExamples.lean';old=changed.read_bytes();changed.write_bytes(old+b'\n-- unauthorized mutation\n')
        check('mutated_source',[],['--output',str(evidence/'mutated.json')]);changed.write_bytes(old)
        manifest=src/'source_freeze.json';old=manifest.read_bytes();m=json.loads(old);m['sources'].pop('E3FiniteExamples.lean');manifest.write_text(json.dumps(m))
        check('tampered_manifest',[],['--output',str(evidence/'tampered.json')]);manifest.write_bytes(old)
        link=evidence/'symlink_parent';link.symlink_to(src/'original_source',target_is_directory=True)
        check('symlink_output_parent',[],['--output',str(link/'receipt.json')]);link.unlink()
        other=evidence/'unrelated.json';other.write_text('{"unrelated":true}\n');old=other.read_bytes()
        check('unrelated_existing_output',[],['--output',str(other)]);require(other.read_bytes()==old,'existing output changed')
        require(expected=={rel:sha(src/rel) for rel in expected},'guard mutated protected copy')
        result={'status':'PASS','schema':'e3-formal-guard-receipt-v1','source_freeze_sha256':sha(ROOT/'source_freeze.json'),'controls':results,'count':len(results),'protected_source_copy_unchanged':True,'optimization_modes':['normal','optimized','double-optimized']}
        print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
