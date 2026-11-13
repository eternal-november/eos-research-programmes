#!/usr/bin/env python3
"""Reviewer positive kernel certificates and expected type/validity rejections.
Run after rebuild.py; LEAN_PATH prefers the independently rebuilt modules.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'scripts'))
from verify_export import lean_code
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
env['LEAN_PATH']=str(OUT/'fresh')+os.pathsep+env['LEAN_PATH']
previous=json.loads((OUT/'rebuild_result.json').read_text())
assert all(h(ROOT/n)==s for n,s in previous['input_sha256'].items()),'Rebuild input changed'
results=[]
for f in [OUT/'IndependentChecks.lean']+sorted(OUT.glob('negative_*.lean')):
    p=subprocess.run(['lean',str(f)],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    f.with_suffix('.log').write_text(p.stdout)
    if f.name=='IndependentChecks.lean':
        ok=p.returncode==0
        closures=re.findall(r'depends on axioms:\s*\[([^]]*)\]',p.stdout,re.S)
        axioms={x.strip() for c in closures for x in c.split(',') if x.strip()}
        assert len(closures)+p.stdout.count('does not depend on any axioms')==7
        assert axioms <= {'propext','Classical.choice','Quot.sound'}
    elif f.stem in ('negative_overlap','negative_reverse_arrow'):
        ok=p.returncode==1 and 'Tactic `decide` proved that the proposition' in p.stdout and '\nis false' in p.stdout
    else:
        ok=p.returncode==1 and ('Type mismatch' in p.stdout or 'Application type mismatch' in p.stdout)
    results.append({'source':f.name,'sha256':h(f),'exit_code':p.returncode,'expected_behavior':ok,'log':f.with_suffix('.log').name})
    print(f.name,p.returncode,ok,flush=True)
assert all(r['expected_behavior'] for r in results)
files=[ROOT/n for n in previous['input_sha256'] if n.endswith('.lean')]
for f in files:
    code=lean_code(f.read_text())
    assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom|unsafe|implemented_by)\b',code),str(f)
index=json.loads((ROOT/'research/workstream_C1/lean/TheoremIndex.json').read_text())
for record in index['theorems']:
    line=(ROOT/record['source']).read_text().splitlines()[record['line']-1]
    assert re.search(r'\btheorem\s+'+re.escape(record['declaration'].split('.')[-1])+r'\b',line),record
for record in index['files']:
    assert h(ROOT/record['path'])==record['sha256'],record
result={'status':'PASS','tests':results,'positive_axiom_reports':7,'positive_axiom_union':sorted(axioms),'source_screened_files':len(files),'theorem_index_locations_checked':len(index['theorems']),'inputs_unchanged':True,'adapter_sha256':h(ROOT/'research/workstream_C1/lean/Adapter_Comparison.md'),'theorem_index_sha256':h(ROOT/'research/workstream_C1/lean/TheoremIndex.json'),'harness_note':'Initial inline runner expected the wrong wording for decide rejection; two valid rejections were flagged false. No Lean source changed; final runner matches the actual diagnostic and reruns all checks.'}
(OUT/'independent_checks_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
