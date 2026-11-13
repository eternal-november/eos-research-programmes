#!/usr/bin/env python3
"""Actual source mutations with mandatory intended assertion classification."""
from pathlib import Path
import subprocess,hashlib,json,shutil,time
HERE=Path(__file__).resolve().parent
WRONG_TYPED_RESIDUAL="""ls=leaves(t)
    bad=list(F)
    for i in range(len(ls)):
        for j in range(i+1,len(ls)):
            if (ls[i].graph,ls[i].arrow)==(ls[j].graph,ls[j].arrow) and F[i]!=F[j]:
                bad[i],bad[j]=bad[j],bad[i]
                return apply_step(graft(t,tuple(bad)),addr,rule,M)
    return apply_step(graft(t,F),addr,rule,M)"""
MUTANTS=[
 ('omit_MIn','model.py',"MIXED_SCHEMAS={'MOut','MIn'}","MIXED_SCHEMAS={'MOut'}",'MIn certificate not admitted by syntactic basis','check_paths'),
 ('merge_repeated_occurrences','model.py','    return graft(t,forest)\n\ndef compose_forest', '''    ls=leaves(t)
    forest=tuple(next(forest[j] for j,q in enumerate(ls) if (q.graph,q.arrow)==(l.graph,l.arrow)) for l in ls)
    return graft(t,forest)

def compose_forest''','positional raw graft disagrees with independent flat substitution','named_six'),
 ('erase_nullary_value','model.py','return replace(w,value=M.mul(t.value,w.value))',"return replace(w,value=0 if t.children[0].kind=='U' else M.mul(t.value,w.value))",'decorated nullary value disagrees with root-address evaluator','named_controls'),
 ('erase_entry_profile','model.py','    return tuple(entries)\n\nMIXED_SCHEMAS', '    return tuple(sorted(e.value for e in entries))\n\nMIXED_SCHEMAS','entry profile collision','named_controls'),
 ('corrupt_MOut_residual','check_integration.py','return apply_step(graft(t,F),addr,rule,M)',WRONG_TYPED_RESIDUAL,'well-typed MOut residual target disagrees with positional graft','check_mout')]
def main():
    base=json.loads((HERE/'AuthorCertificate.json').read_text())
    assert base['status']=='PASS','a completed unmutated run is required'
    for name,h in base['source_sha256'].items():assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==h
    rows=[]
    for name,file,old,new,expected,function in MUTANTS:
        d=HERE/'mutations'/name;d.mkdir(parents=True,exist_ok=True)
        for f in ('model.py','check_integration.py','DOMAIN.md'):shutil.copy2(HERE/f,d/f)
        p=d/file;source=p.read_text();assert source.count(old)==1,(name,source.count(old))
        p.write_text(source.replace(old,new));start=time.monotonic()
        r=subprocess.run(['python',str(d/'check_integration.py')],cwd=d,text=True,capture_output=True)
        (d/'stdout.log').write_text(r.stdout);(d/'stderr.log').write_text(r.stderr)
        last=r.stderr.rstrip().splitlines()[-1] if r.stderr.rstrip() else ''
        assert r.returncode==1,(name,'not an ordinary assertion failure',r.returncode)
        assert last=='AssertionError: '+expected,(name,'UNEXPECTED failure context',last)
        assert ('in '+function+'\n') in r.stderr,(name,'wrong detecting function')
        assert not any(x in r.stderr for x in ('SyntaxError:','TypeError:','NameError:','ImportError:'))
        rows.append({'name':name,'source_file':file,'original_sha256':hashlib.sha256((HERE/file).read_bytes()).hexdigest(),'mutant_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'edit_from':old,'edit_to':new,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'detected_failure':last,'expected_assertion':expected,'detecting_function':function,'classification':'INTENDED_ASSERTION','stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(r.stderr.encode()).hexdigest()})
        print(name,'DETECTED at',function,flush=True)
    report={'status':'PASS','evidence':'actual source mutant replay; intended finite implementation failures, not mathematical relation independence','domain_sha256':hashlib.sha256((HERE/'DOMAIN.md').read_bytes()).hexdigest(),'unmutated_certificate_sha256':hashlib.sha256((HERE/'AuthorCertificate.json').read_bytes()).hexdigest(),'mutants':rows}
    (HERE/'MutationCertificate.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
