#!/usr/bin/env python3
"""Additional final source-only confirmation of the already reproduced D1 bridge."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,tempfile,time
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--original-source',type=Path,required=True)
ap.add_argument('--d1-source',type=Path,required=True)
ap.add_argument('--toolchain-root',type=Path,required=True,help='Contains lean-4.35.0-linux/ and project/.lake/packages/ with only pinned public dependencies')
ap.add_argument('--output-dir',type=Path,required=True)
args=ap.parse_args();S=args.original_source.resolve();D=args.d1_source.resolve();T=args.toolchain_root.resolve();R=args.output_dir.resolve();R.mkdir(parents=True,exist_ok=True);started=time.monotonic()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
need(not R.is_relative_to(S) and not R.is_relative_to(D),'output must be outside source roots')
run=Path(tempfile.mkdtemp(prefix='fresh_d1_',dir=R));p=run/'project';p.mkdir();rec={'status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run_directory':str(run),'reason':'Additional source-only confirmation. The final delivered D1 package already rebuilt this source closure; this does not claim to repair an uncovered delivered-version gap.'}
stages=[]
try:
 files=list((S/'WitnessedDecompositions').glob('*.lean'))+[S/x for x in ['WitnessedDecompositions.lean','lakefile.toml','lake-manifest.json','lean-toolchain','research/workstream_C2/lean/RelationInterface.lean']]
 hashes={str(x.relative_to(S)):sha(x) for x in files}
 for x in files:
  y=p/x.relative_to(S);y.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(x,y)
 for name in ['D1FiniteTypedAction.lean','D1OriginalAPIBridge.lean']:shutil.copy2(D/name,p/name)
 d1hashes={n:sha(D/n) for n in ['D1FiniteTypedAction.lean','D1OriginalAPIBridge.lean']}
 need(not list(p.rglob('*.olean')),'old project objects')
 lock=json.loads((S/'lake-manifest.json').read_text());pins=[];(p/'.lake/packages').mkdir(parents=True)
 for dep in lock['packages']:
  q=T/'project/.lake/packages'/dep['name'];actual=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip()
  need(actual==dep['rev'],'upstream pin mismatch');need(subprocess.run(['git','-C',str(q),'diff','--quiet','HEAD','--']).returncode==0,'dirty upstream tracked files')
  (p/'.lake/packages'/dep['name']).symlink_to(q.resolve(),target_is_directory=True);pins.append({'name':dep['name'],'revision':actual,'tracked_source_clean':True})
 env=dict(os.environ);env.pop('LEAN_PATH',None);env['PATH']=str(T/'lean-4.35.0-linux/bin')+os.pathsep+env['PATH'];env.pop('PYTHONOPTIMIZE',None)
 need(sha(T/'lean-4.35.0-linux/bin/lean')=='bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38','compiler hash')
 rec['compiler']=subprocess.check_output(['lean','--version'],env=env,text=True).strip()
 def stage(name,cmd,negative=False):
  log=run/(name+'.log')
  with log.open('w') as f:z=subprocess.run(cmd,cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
  s=log.read_text();stages.append({'name':name,'command':cmd,'returncode':z.returncode,'log':str(log),'sha256':sha(log)})
  if negative:
   need(z.returncode!=0 and 'error:' in s,'mutant survived')
   need(not any(t in s for t in ['unknown module','object file does not exist','must be contained in root directory','unknown identifier']),'infrastructure mutation failure')
  else:need(z.returncode==0,name+' failed');need('sorryAx' not in s and 'declaration uses `sorry`' not in s,'proof hole')
  return s
 stage('fresh_original',['lake','build','WitnessedDecompositions','WitnessedDecompositions.RefinementFunctoriality'])
 target=p/'.lake/build/lib/lean/research/workstream_C2/lean';target.mkdir(parents=True,exist_ok=True)
 stage('fresh_relation',['lake','env','lean','-o',str(target/'RelationInterface.olean'),'research/workstream_C2/lean/RelationInterface.lean'])
 closures={}
 for n in ['D1FiniteTypedAction','D1OriginalAPIBridge']:
  txt=stage(n,['lake','env','lean','-o',str(p/'.lake/build/lib/lean'/f'{n}.olean'),n+'.lean'])
  for m in re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",txt,re.S):
   ax=[] if m[2] is None else [a.strip() for a in m[2].split(',')];need(set(ax)<={'propext','Quot.sound'},'unexpected axiom');closures[m[1]]=ax
 need(len(closures)==22,'wrong number of principal D1 closures')
 src=(p/'D1FiniteTypedAction.lean').read_text();old='fun x y => R ((p a).backward x) ((p b).backward y)';new='fun x y => R ((p a).forward x) ((p b).forward y)';need(src.count(old)==1,'mutation not unique')
 (p/'Mutant.lean').write_text(src.replace(old,new));stage('wrong_coordinate_mutation',['lake','env','lean','Mutant.lean'],True)
 need(hashes=={str(x.relative_to(S)):sha(x) for x in files},'original changed');need(d1hashes=={n:sha(D/n) for n in d1hashes},'D1 changed')
 rec.update(runner_sha256=sha(Path(__file__)),invocation={'original_source':str(S),'d1_source':str(D),'toolchain_root':str(T),'output_dir':str(R)},status='PASS',source_only=True,project_objects_reused=False,public_pinned_upstream_objects_reused=True,source_hashes=hashes,d1_hashes=d1hashes,pins=pins,axiom_closures=closures,mutation='inverse coordinates replaced with forward coordinates; mathematically rejected',stages=stages)
except Exception as e:rec.update(status='FAIL',error=str(e),stages=stages);raise
finally:
 rec.update(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-started);(R/'d1_fresh_result.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'status':rec['status'],'receipt':str(R/'d1_fresh_result.json')}))
