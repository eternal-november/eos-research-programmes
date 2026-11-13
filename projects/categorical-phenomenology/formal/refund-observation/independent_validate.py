#!/usr/bin/env python3
"""Independent isolated clean build of audited sources and edge-case checks."""
from pathlib import Path
import os, subprocess, json, hashlib, shutil
root=Path(__file__).resolve().parent
build=root/'.independent_build'
if build.exists(): shutil.rmtree(build)
build.mkdir()
lean=os.environ.get('LEAN_BIN') or shutil.which('lean')
if not lean:
 raise SystemExit('Lean not found. Install Lean 4.35.0, then set LEAN_BIN or put lean on PATH.')
lean=str(Path(lean).expanduser().resolve())
version=subprocess.check_output([lean,'--version'],text=True).strip()
if 'version 4.35.0,' not in version:
 raise SystemExit('This package is pinned to Lean 4.35.0. Found: '+version)
sources=['dependencies/ResourceObservation.lean','dependencies/ResourceObservationIff.lean','OrderedGroupRefunds.lean','BoundedRefunds.lean','ClassicalGroupCorollary.lean','PreorderControl.lean','IndependentAudit.lean']
results=[]
for s in sources:
 p=root/s
 run=subprocess.run([lean,'-o',str((build/(p.stem+'.olean')).relative_to(root)),s],cwd=root,env=dict(os.environ,LEAN_PATH=str(build)),capture_output=True,text=True)
 output=run.stdout+run.stderr
 (build/(p.stem+'.log')).write_text(output)
 results.append({'source':s,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exit_code':run.returncode,'output':output})
 if run.returncode: break
passed=all(x['exit_code']==0 and 'sorryAx' not in x['output'] for x in results) and len(results)==len(sources)
(root/'independent_audit.json').write_text(json.dumps({'lean':version,'results':results,'all_passed':passed},indent=2)+'\n')
print('Independent clean build:', 'PASS' if passed else 'FAIL')
raise SystemExit(0 if passed else 1)
