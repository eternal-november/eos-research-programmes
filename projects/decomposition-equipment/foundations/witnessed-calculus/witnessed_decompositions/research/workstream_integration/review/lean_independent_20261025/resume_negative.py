from pathlib import Path
import json,os,subprocess,hashlib,datetime
H=Path(__file__).resolve().parent;ROOT=H.parents[3];SRC=H/'source';R=json.loads((H/'result.attempt01.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ);env['LEAN_PATH']=R['LEAN_PATH']
assert all(c['exit']==0 for c in R['commands'] if '/negative' not in c['source'])
R['runner_repair']={'prior_result':'result.attempt01.json','prior_result_sha256':sha(H/'result.attempt01.json'),'cause':'Reviewer negative-diagnostic parser omitted the expected Lean decide diagnostic is false; all positive compilations had passed. Accept that diagnostic and rerun all ten inherited negatives. No project source was changed.'}
R['negative_controls']=[]
try:
 for p in sorted((SRC/'research/workstream_C1/review/lean_independent').glob('negative_*.lean'))+sorted((SRC/'research/workstream_C2/review/lean_audit_evidence/negative').glob('*.lean')):
  proc=subprocess.run(['lean','-R',str(SRC),str(p)],cwd=SRC,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  rel=str(p.relative_to(SRC));log=H/'logs'/('recheck_'+rel.replace('/','_')+'.log');log.write_text(proc.stdout)
  assert proc.returncode==1 and ('type mismatch' in proc.stdout.lower() or 'is false' in proc.stdout.lower()),proc.stdout
  assert 'unknown module' not in proc.stdout.lower(),proc.stdout
  R['negative_controls'].append({'source':rel,'sha256':sha(p),'exit':proc.returncode,'log':str(log.relative_to(H)),'log_sha256':sha(log)})
  print(rel,proc.returncode,flush=True)
 items=json.loads((ROOT/'research/workstream_integration/BaselinePreservation.json').read_text())['files']
 for i in items:assert sha(ROOT/i['path'])==i['sha256'],i['path']
 for i in R['snapshots']:assert sha(ROOT/i['path'])==i['sha256'],i['path']
 R['baseline_after']=len(items);R['source_snapshot_stable_after']=True;R['status']='PASS'
 R.pop('error',None);R.pop('traceback',None)
except BaseException as e:R.update(status='FAIL',error=repr(e));print(repr(e))
R['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(H/'result.json').write_text(json.dumps(R,indent=2)+'\n')
raise SystemExit(R['status']!='PASS')
