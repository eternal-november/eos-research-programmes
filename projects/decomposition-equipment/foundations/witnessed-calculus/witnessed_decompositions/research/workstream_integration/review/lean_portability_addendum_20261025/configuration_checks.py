"""Reviewer tests of the exact parsed configuration function; no theorem edits."""
from pathlib import Path
import ast,os,subprocess,shutil,re,json,types,hashlib
HERE=Path(__file__).resolve().parent
ROOT=Path('/workspace/shared/witnessed_integration_20261025/reproduction/fresh_source/witnessed_decompositions')
SOURCE=ROOT/'research/workstream_integration/lean/build.py'
node=next(n for n in ast.parse(SOURCE.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='configure_environment')
code=compile(ast.Module(body=[node],type_ignores=[]),str(SOURCE),'exec')
for key in ('WITNESSED_TOOLCHAIN_ROOT','WITNESSED_LAKE_PROJECT','WITNESSED_USE_RECOVERY'):os.environ.pop(key,None)
real_run=subprocess.run;real_check=subprocess.check_output
alias=HERE/'project_build_alias';alias.symlink_to(ROOT/'.lake/build/lib/lean',target_is_directory=True) if not alias.exists() and not alias.is_symlink() else None
records=[]
for case in ('actual_current_configuration','head_mismatch','dirty_tracked_worktree','stale_project_alias','missing_git_metadata'):
 def run(cmd,*args,**kwargs):
  if case=='dirty_tracked_worktree' and 'diff' in cmd:return subprocess.CompletedProcess(cmd,1,'','')
  if case=='stale_project_alias' and cmd[:4]==['lake','env','printenv','LEAN_PATH']:
   prefix=real_check(['lean','--print-prefix'],text=True).strip()
   return subprocess.CompletedProcess(cmd,0,str(alias)+os.pathsep+str(Path(prefix)/'lib/lean')+'\n','')
  if case=='missing_git_metadata' and '--show-toplevel' in cmd:return subprocess.CompletedProcess(cmd,128,'','not a git repository')
  return real_run(cmd,*args,**kwargs)
 def check(cmd,*args,**kwargs):
  if case=='head_mismatch' and 'rev-parse' in cmd and '--verify' in cmd:return '0'*40+'\n'
  return real_check(cmd,*args,**kwargs)
 glob=dict(json=json,Path=Path,os=os,subprocess=types.SimpleNamespace(run=run,check_output=check),shutil=shutil,re=re,ROOT=ROOT,RECOVERY=Path('/workspace/shared/witnessed_B_20261024/toolchain_recovery'),BUILD=HERE/'isolated_output')
 exec(code,glob)
 try:
  env,conf=glob['configure_environment']()
  assert case in ('actual_current_configuration','missing_git_metadata'),case
  assert conf['dependency_selection']=='current_source_checkout'
  assert all(not Path(p).is_relative_to(Path(conf['canonical_project_build_excluded'])) for p in conf['external_lean_path'])
  statuses={v['status'] for v in conf['package_git_checks'].values()}
  assert statuses==({'GIT_METADATA_UNAVAILABLE_LOCK_ONLY'} if case=='missing_git_metadata' else {'HEAD_MATCH_TRACKED_WORKTREE_CLEAN'}),statuses
  records.append({'case':case,'status':'PASS','configuration':conf})
 except RuntimeError as e:
  expected={'head_mismatch':'Actual dependency Git HEAD mismatch','dirty_tracked_worktree':'Tracked dependency worktree differs','stale_project_alias':'No supported package dependency paths'}
  assert case in expected and expected[case] in str(e),(case,str(e))
  records.append({'case':case,'status':'EXPECTED_REJECTION','error':str(e)})
result={'status':'PASS','exact_build_py_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'method':'AST extract exact configure_environment; actual current project paths/packages except explicitly mocked fault-injection subprocess results. No mock is used by the separate full Lean replay.','cases':records}
(HERE/'configuration_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','cases':[(x['case'],x['status']) for x in records]},indent=2))
