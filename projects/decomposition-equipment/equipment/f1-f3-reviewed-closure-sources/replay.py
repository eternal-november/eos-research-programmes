#!/usr/bin/env python3
"""Replay shipped finite checks in an isolated copy; preserve reference JSON bytes."""
if not __debug__:
    raise RuntimeError('Assertions are required; do not run replay.py with -O')
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'f1_f3_recognition_20261031'
JOBS=[
 ('verify_cluster.py','verify_cluster_results.json','stdout'),
 ('verify_cluster_formula.py','verify_cluster_formula_results.json','stdout'),
 ('verify_cluster_rewrites.py','verify_cluster_rewrites_results.json','stdout'),
 ('verify_group_classification.py','verify_group_classification_results.json','file'),
 ('verify_partition_erasure_boundary.py','verify_partition_erasure_boundary.json','file'),
 ('independent_re_classification.py','independent_re_classification.json','file'),
 ('reviewer_replay/verify_hypothesis_controls.py','reviewer_replay/verify_hypothesis_controls_results.json','stdout'),
]
def digest(b):return hashlib.sha256(b).hexdigest()
results=[]
env=dict(os.environ)
env.pop('PYTHONOPTIMIZE',None)
env['PYTHONDONTWRITEBYTECODE']='1'
with tempfile.TemporaryDirectory(prefix='f1_f3_replay_') as temp:
    work=Path(temp)
    for script,reference,_ in JOBS:
        (work/script).parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(SRC/script,work/script)
    for script,reference,mode in JOBS:
        reference_bytes=(SRC/reference).read_bytes()
        disabled=subprocess.run([sys.executable,'-O',script],cwd=work,env=env,capture_output=True)
        disabled_env=subprocess.run([sys.executable,script],cwd=work,env={**env,'PYTHONOPTIMIZE':'1'},capture_output=True)
        assert disabled.returncode!=0 and b'assertion' in disabled.stderr.lower(), script+' accepted -O or failed for wrong reason'
        assert disabled_env.returncode!=0 and b'assertion' in disabled_env.stderr.lower(), script+' accepted PYTHONOPTIMIZE=1 or failed for wrong reason'
        print('Replaying '+script,file=sys.stderr,flush=True)
        run=subprocess.run([sys.executable,script],cwd=work,env=env,capture_output=True)
        if run.returncode:raise RuntimeError(script+' failed\n'+run.stderr.decode(errors='replace'))
        actual=run.stdout if mode=='stdout' else (work/reference).read_bytes()
        assert json.loads(actual)==json.loads(reference_bytes), script+' substantive JSON mismatch'
        assert actual==reference_bytes, script+' JSON byte mismatch'
        results.append({'script':script,'reference':reference,'status':'PASS','assertions_enabled':True,'optimized_mode_rejected':True,'environment_optimized_mode_rejected':True,'result_json_byte_identical':True,'source_sha256':digest((SRC/script).read_bytes()),'reference_sha256':digest(reference_bytes)})
result={'status':'PASS','scope':'All seven shipped verifier entrypoints; four main cluster/formula/rewrite/classification routes and three auxiliary erasure/reviewer/control routes. Each executes in an isolated temporary source copy; all substantive JSON fields and exact bytes match frozen reference results.','runtime':'Python 3 standard library only; no network; no timing-dependent exit','universal_claims':'None. Finite checks do not prove all-degree results, B3 path coherence, or original F2 acceptance.','checks':results}
data=json.dumps(result,sort_keys=True,indent=2)+'\n'
(ROOT/'replay_results.json').write_text(data)
print(data,end='')
