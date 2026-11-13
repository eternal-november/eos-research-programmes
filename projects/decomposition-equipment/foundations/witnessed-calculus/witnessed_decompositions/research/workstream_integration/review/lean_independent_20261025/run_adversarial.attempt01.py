from pathlib import Path
import json, os, subprocess, re, hashlib
H=Path(__file__).resolve().parent
R=json.loads((H/'result.json').read_text());env=dict(os.environ);env['LEAN_PATH']=R['LEAN_PATH']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(p,positive=False):
 cmd=['lean','-R',str(H)]
 if positive:cmd+=['-o',str(H/'fresh/IndependentChecks.olean')]
 cmd += [str(p)]
 proc=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=H/(p.stem+'.log');log.write_text(proc.stdout)
 print(p.name,proc.returncode,flush=True)
 if positive:assert proc.returncode==0,proc.stdout
 else:
  assert proc.returncode!=0,proc.stdout
  assert 'unknown module' not in proc.stdout.lower() and 'file not found' not in proc.stdout.lower(),proc.stdout
  assert ('type mismatch' in proc.stdout.lower() or 'is false' in proc.stdout.lower() or 'unsolved goals' in proc.stdout.lower()),proc.stdout
 return {'source':str(p.relative_to(H)),'source_sha256':sha(p),'exit':proc.returncode,'log':log.name,'log_sha256':sha(log),'command':cmd}
r={'status':'RUNNING','checks':[]}
try:
 r['checks'].append(run(H/'IndependentChecks.lean',True))
 for p in sorted(H.glob('negative_*.lean')):r['checks'].append(run(p))
 src=(H/'source/research/workstream_integration/lean/GraphForestNormalForms.lean').read_text()
 mutations={
  'mutation_collapse_second_local':('else if i.val = 2 then .deco 2','else if i.val = 2 then .deco 1'),
  'mutation_erase_nullary_value':('def labelledNullary : CutTerm 1 1 := .deco 1 (.unit 1)','def labelledNullary : CutTerm 1 1 := .unit 1'),
  'mutation_replace_full_tuple_by_identity':('FrontierForest t := fun i => reify (F i).normalize','FrontierForest t := fun i => .leaf (frontierEntry t i).arrow (frontierEntry t i).block'),
 }
 for name,(before,after) in mutations.items():
  assert src.count(before)==1
  p=H/(name+'.lean');p.write_text(src.replace(before,after));r['checks'].append(run(p))
 log=(H/'IndependentChecks.log').read_text()
 axioms={n:[a.strip() for a in c.split(',') if a.strip()] for n,c in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):axioms[n]=[]
 assert len(axioms)==11 and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values()),axioms
 r['axioms']=axioms;r['status']='PASS'
except BaseException as e:r.update(status='FAIL',error=repr(e));print(repr(e),flush=True)
(H/'adversarial_result.json').write_text(json.dumps(r,indent=2)+'\n')
raise SystemExit(r['status']!='PASS')
