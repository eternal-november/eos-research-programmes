#!/usr/bin/env python3
"""Verify that semantic and source-freeze rejection survives Python -O and -OO.
Uses temporary private source copies; never mutates the deliverable's sources.
"""
import hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent

def main():
    records=[]
    for flag in ('','-O','-OO'):
        with tempfile.TemporaryDirectory(prefix='e1_guard_',dir=HERE) as td:
            root=Path(td)
            for name in ('e1_finite_model.py','test_e1_finite.py'):
                (root/name).write_bytes((HERE/name).read_bytes())
            # A hash is captured by main before run_positive; change only its
            # temporary copied source during that call, then demand rejection.
            source_probe="""import sys
from pathlib import Path
import test_e1_finite as t
def changed_source():
    p=Path(t.__file__)
    p.write_text(p.read_text()+'\\n# deliberate temporary source mutation\\n')
    return {}
t.run_positive=changed_source
t.run_mutations=lambda: []
sys.argv=['test_e1_finite.py','--output','should_not_exist.json']
t.main()
"""
            cmd=[sys.executable]+([flag] if flag else [])+['-c',source_probe]
            run=subprocess.run(cmd,cwd=root,capture_output=True,text=True)
            valid=run.returncode!=0 and 'Source changed while running' in run.stderr and not (root/'should_not_exist.json').exists()
            if not valid: raise RuntimeError({'probe':'source_hash_guard','mode':flag,'result':run.stderr})
            records.append({'probe':'source_hash_guard','mode':flag or 'normal','exit_code':run.returncode,'rejected':valid,'stderr':run.stderr})
            # Make one declared mutant identical to the oracle in a temporary
            # source copy. run_mutations MUST reject this failed negative control.
            source=(HERE/'test_e1_finite.py').read_text().replace('wrong_zero=frozenset()','wrong_zero=evaluate_tuple_oracle(p)')
            (root/'test_e1_finite.py').write_text(source)
            run=subprocess.run([sys.executable]+([flag] if flag else [])+['-B','-c','import test_e1_finite as t; t.run_mutations()'],cwd=root,capture_output=True,text=True)
            valid=run.returncode!=0 and 'nullary_is_empty_relation' in run.stderr and "'rejected': False" in run.stderr
            if not valid: raise RuntimeError({'probe':'negative_control_guard','mode':flag,'result':run.stderr})
            records.append({'probe':'negative_control_guard','mode':flag or 'normal','exit_code':run.returncode,'rejected':valid,'stderr':run.stderr})
            run=subprocess.run([sys.executable]+([flag] if flag else [])+['-B','-c',"from e1_finite_model import *; a=Obj('a',1); Cell(Path((a,),()),diagonal(a),identity(a),identity(a),-1)"],cwd=root,capture_output=True,text=True)
            valid=run.returncode!=0 and 'Model invariant failed: self.weight >= 0' in run.stderr
            if not valid: raise RuntimeError({'probe':'model_invariant_guard','mode':flag,'result':run.stderr})
            records.append({'probe':'model_invariant_guard','mode':flag or 'normal','exit_code':run.returncode,'rejected':valid,'stderr':run.stderr})
    result={'status':'PASS','checks':len(records),'source_sha256':{n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in ('e1_finite_model.py','test_e1_finite.py','test_e1_guards.py')},'records':records}
    out=HERE/'guard_results.json'; tmp=out.with_name(out.name+'.tmp'); tmp.write_text(json.dumps(result,indent=2)+'\n'); os.replace(tmp,out)
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
