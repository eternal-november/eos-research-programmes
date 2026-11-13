#!/usr/bin/env python3
"""Source-only B4/G1 closure replay with frozen inputs and mutation controls.
Only pinned public upstream compiler/libraries are reused; project objects
are freshly built. No network. Failure replaces this run's PASS receipt.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,shutil,subprocess,tempfile,time,sys
R=pathlib.Path(__file__).resolve().parent
DEFAULT=pathlib.Path('/workspace/shared/d1_equivariant_transport_20261031/formal/toolchain')
B4={'B4.weight_monotone','B4.weight_strict'}|{'WitnessedDecompositions.'+n for n in ['Tree.graft_injective','Tree.graft_no_cycle','Tree.graftLeafEquiv','Tree.graftLeafEquiv_component','Tree.collect_graftLeaf','Tree.collect_profileGraftLeaf','Tree.frontier_profileGraft','Tree.weight_profileGraft','Tree.weight_substituteOperation','Presentation.derives_weight','Raw.antisymm']}
G1={'WitnessedDecompositions.'+n for n in ['ParallelCongruence.kernel','ParallelCongruence.factor','ParallelCongruence.projection_factor','ParallelCongruence.factor_unique','Presentation.sound','Presentation.extend_respects','Presentation.projection_extend','Presentation.quotient_eq_iff','Presentation.extend_unique','Presentation.derives_iff_all_models']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def validate_dest(out,src):
 out=out.absolute()
 for p in [out,*out.parents]:need(not p.is_symlink(),'symlink output directory')
 need(not out.is_relative_to(src.resolve()),'output inside frozen original source')
 p=out/'result.json';need(not p.is_symlink(),'symlink receipt')
 if p.exists():need(p.is_file() and p.stat().st_nlink==1,'receipt is not independent regular file')
 return out,p

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=pathlib.Path,default=R/'original_source');ap.add_argument('--toolchain-root',type=pathlib.Path,default=DEFAULT);ap.add_argument('--output-dir',type=pathlib.Path,default=R);args=ap.parse_args()
 S=args.source_root.resolve();T=args.toolchain_root.resolve();out,receipt=validate_dest(args.output_dir,S);out.mkdir(parents=True,exist_ok=True)
 def write(obj):receipt.write_text(json.dumps(obj,indent=2)+'\n')
 write({'schema':'b4-formal-receipt-v1','status':'RUNNING','started_utc':utc()})
 try:
  start=time.monotonic();freeze=json.loads((R/'source_freeze.json').read_text());need(freeze['schema']=='b4-formal-freeze-v1','wrong freeze')
  need(sha(pathlib.Path(__file__))==freeze['runner_sha256'],'runner differs from freeze')
  need(all(sha(R/n)==h for n,h in freeze['modules'].items()),'audit source differs from freeze')
  inputs=[S/x for x in freeze['original_source']]
  need(all(q.is_file() and not q.is_symlink() for q in inputs),'missing or symlink original source')
  hashes={str(q.relative_to(S)):sha(q) for q in inputs};need(hashes==freeze['original_source'],'original source byte mismatch')
  (out/'runs').mkdir(exist_ok=True);run=pathlib.Path(tempfile.mkdtemp(prefix='fresh_',dir=out/'runs'));p=run/'project';p.mkdir()
  for q in inputs:
   d=p/q.relative_to(S);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,d)
  for name in freeze['modules']:shutil.copy2(R/name,p/name)
  need(not list(p.rglob('*.olean')),'inherited project objects')
  lock=json.loads((S/'lake-manifest.json').read_text());pins=[]
  need((S/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0','wrong toolchain')
  need(sha(S/'lake-manifest.json')=='0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc','wrong lock')
  (p/'.lake/packages').mkdir(parents=True)
  for x in lock['packages']:
   q=T/'project/.lake/packages'/x['name'];rev=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip()
   need(rev==x['rev'],'upstream revision mismatch');need(subprocess.run(['git','-C',str(q),'diff','--quiet','HEAD','--']).returncode==0,'dirty upstream')
   (p/'.lake/packages'/x['name']).symlink_to(q.resolve(),target_is_directory=True);pins.append({'name':x['name'],'revision':rev})
  env=dict(os.environ);env.pop('LEAN_PATH',None);env['PATH']=str(T/'lean-4.35.0-linux/bin')+os.pathsep+env['PATH']
  version=subprocess.check_output(['lean','--version'],env=env,text=True).strip()
  need('4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version,'wrong compiler')
  need(sha(T/'lean-4.35.0-linux/bin/lean')=='bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38','compiler hash mismatch')
  stages=[]
  def stage(name,cmd,positive=True):
   log=run/(name+'.log')
   with log.open('w') as f:res=subprocess.run(cmd,cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
   txt=log.read_text();stages.append({'name':name,'command':cmd,'returncode':res.returncode,'log':str(log),'sha256':sha(log)})
   if positive:need(res.returncode==0,f'{name} failed: {log}');need('sorryAx' not in txt and 'declaration uses `sorry`' not in txt,'proof hole')
   else:
    need(res.returncode!=0 and 'error:' in txt,f'mutation survived: {name}')
    need(not any(s in txt for s in ['unknown module','object file does not exist','must be contained in root directory']),f'infrastructure rejection: {name}')
   return txt
  stage('fresh_original_modules',['lake','build','WitnessedDecompositions.RawRefinement','WitnessedDecompositions.WeightInvariant','WitnessedDecompositions.PresentedCalculus'])
  closures={}
  for name,expected,allowed in [('B4Elementary',B4,{'propext','Quot.sound'}),('G1KernelFactorizationAudit',G1,{'propext','Quot.sound','Classical.choice'})]:
   txt=stage(name,['lake','env','lean',name+'.lean']);found={}
   for m in re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",txt,re.S):
    ax=[] if m[2] is None else [z.strip() for z in m[2].split(',')];need(set(ax)<=allowed,'unexpected axiom');found[m[1]]=ax
   need(set(found)==expected,'wrong exact declaration set');closures[name]=found
  original=(R/'B4Elementary.lean').read_text();mutations=[]
  targets=[('reverse_growth','Tree.weight w t ≤ Tree.weight w (Tree.profileGraft t f)','Tree.weight w (Tree.profileGraft t f) ≤ Tree.weight w t'),('weaken_strict_positivity','(h : 0 < Path.sum','(h : 0 ≤ Path.sum')]
  for name,old,new in targets:
   need(original.count(old)==1,'nonunique mutation target');mutant=original.replace(old,new,1);(p/'B4Elementary.lean').write_text(mutant)
   stage('mutation_'+name,['lake','env','lean','B4Elementary.lean'],False);mutations.append({'name':name,'status':'REJECTED','sha256':hashlib.sha256(mutant.encode()).hexdigest()})
  (p/'B4Elementary.lean').write_text(original);stage('restored_B4',['lake','env','lean','B4Elementary.lean'])
  need(hashes=={str(q.relative_to(S)):sha(q) for q in inputs},'original source changed')
  need(all(sha(R/n)==h for n,h in freeze['modules'].items()),'audit source changed')
  need(sha(pathlib.Path(__file__))==freeze['runner_sha256'],'runner changed during replay')
  result={'schema':'b4-formal-receipt-v1','status':'PASS','finished_utc':utc(),'elapsed_seconds':time.monotonic()-start,'source_only':True,'project_objects_reused':False,'public_pinned_upstream_objects_reused':True,'source_root':str(S),'toolchain_root':str(T),'original_source_hashes':hashes,'source_freeze_sha256':sha(R/'source_freeze.json'),'module_hashes':freeze['modules'],'runner_sha256':sha(pathlib.Path(__file__)),'compiler':version,'compiler_sha256':sha(T/'lean-4.35.0-linux/bin/lean'),'pins':pins,'axiom_closures':closures,'mutation_controls':mutations,'stages':stages}
  write(result);print(json.dumps({'status':'PASS','receipt':str(receipt),'axiom_closures':sum(map(len,closures.values())),'mutations':len(mutations)}));return 0
 except Exception as e:
  write({'schema':'b4-formal-receipt-v1','status':'FAIL','finished_utc':utc(),'error':str(e)});raise
if __name__=='__main__':
 try:sys.exit(main())
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
