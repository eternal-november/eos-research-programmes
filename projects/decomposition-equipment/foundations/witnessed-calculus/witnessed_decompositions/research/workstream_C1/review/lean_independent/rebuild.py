#!/usr/bin/env python3
"""Independent fresh-source C1 dependency and fragment rebuild; no author source edits."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
BUILD=OUT/'fresh'
(BUILD/'WitnessedDecompositions').mkdir(parents=True,exist_ok=True)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,name,expected=0):
    p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/(name+'.log')).write_text(p.stdout)
    records.append({'command':list(map(str,args)),'exit_code':p.returncode,'log':str((OUT/(name+'.log')).relative_to(ROOT))})
    print(name,p.returncode,flush=True)
    if p.returncode!=expected: raise RuntimeError(name+': unexpected exit code '+str(p.returncode))
    return p.stdout
modules=['Core','Examples','Collections','PathOccurrences','Positive','TreeOccurrences','Calculus','FreeCalculus','FreeExtension','Congruence','QuotientCalculus','PresentedCalculus']
sources=[Path('WitnessedDecompositions')/(x+'.lean') for x in modules]+[Path('research/workstream_A/rewrite/GraphCoordinates.lean'),Path('research/workstream_C1/lean/GraphCutFragment.lean'),Path('research/workstream_C1/lean/GraphCutAxioms.lean')]
inputs={str(x):digest(ROOT/x) for x in sources}
inputs.update({x:digest(ROOT/x) for x in ['research/CompletionContract.md','research/workstream_C1/C1_Targets.md','research/workstream_C1/proof/C1_Model_Theorem.md','lakefile.toml','lake-manifest.json','lean-toolchain']})
env=json.loads(subprocess.check_output(['lake','env','python3','-c','import json,os; print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
env['LEAN_PATH']=str(BUILD)+os.pathsep+env.get('LEAN_PATH','')
records=[]
version=run(['lean','--version'],'version')
for x in modules:
    run(['lean','-R','.', '-o',str(BUILD/'WitnessedDecompositions'/(x+'.olean')),str(Path('WitnessedDecompositions')/(x+'.lean'))],x)
run(['lean','-R','research/workstream_A/rewrite','-o',str(BUILD/'GraphCoordinates.olean'),'research/workstream_A/rewrite/GraphCoordinates.lean'],'GraphCoordinates')
run(['lean','-R','research/workstream_C1/lean','-o',str(BUILD/'GraphCutFragment.olean'),'research/workstream_C1/lean/GraphCutFragment.lean'],'GraphCutFragment')
log=run(['lean','research/workstream_C1/lean/GraphCutAxioms.lean'],'GraphCutAxioms')
expected=len(re.findall(r'^#print axioms ',(ROOT/'research/workstream_C1/lean/GraphCutAxioms.lean').read_text(),re.M))
closures=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
seen={a.strip() for c in closures for a in c.split(',') if a.strip()}
assert len(closures)+log.count('does not depend on any axioms')==expected
assert seen <= {'propext','Classical.choice','Quot.sound'}
assert all(digest(ROOT/x)==h for x,h in inputs.items()),'Source changed during rebuild'
result={'status':'PASS','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_sha256':inputs,'records':records,'axiom_reports':expected,'axiom_union':sorted(seen),'lean_version':version.strip(),'claim':'Fresh project-source dependency closure and C1 fragment; mathlib is pinned cache, not rebuilt.'}
(OUT/'rebuild_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
