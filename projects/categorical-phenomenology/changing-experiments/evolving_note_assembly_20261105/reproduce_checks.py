from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import shutil,subprocess,sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCES=[('evolving_bridge_research_20261105','check_evolving_incidence.py'),('interface_composition_theorem_20261105_1420','check_resource_classification.py'),('native_transport_witnesses_20261105','check_trace_resource_transport.py'),('evolving_interface_adversarial_20261105','finite_checks.py')]
def one(spec):
 d,n=spec; src=ROOT.parent/d/n
 out=ROOT/'checks/replay'/d; out.mkdir(parents=True,exist_ok=True)
 script=out/n; shutil.copy2(src,script); start=time.monotonic()
 result=subprocess.run([sys.executable,str(script)],cwd=out,text=True,capture_output=True)
 (out/'stdout.txt').write_text(result.stdout);(out/'stderr.txt').write_text(result.stderr)
 if d=='evolving_bridge_research_20261105' and result.returncode==0:
  obj=json.loads(result.stdout);(out/'check_results.json').write_text(json.dumps(obj,indent=2)+'\n')
 return {'suite':d,'script':n,'returncode':result.returncode,'seconds':round(time.monotonic()-start,3),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
with ThreadPoolExecutor(max_workers=4) as pool: reports=list(pool.map(one,SOURCES))
# A direct independent check of the integrated paired-test response example.
S={(0,0),(0,1),(1,0),(1,1)}; src_labels=[(a,b) for a in range(2) for b in range(2) if a+b<=1 and 2*a>=1 and 2*b>=1]
tgt_labels=[(a,b) for a in range(3) for b in range(3) if a+b<=2 and a>=1 and b>=1]
assert src_labels==[] and tgt_labels==[(1,1)]
C={(1,1)}
assert len({tuple(x in c for c in []) for x in S})==1
assert len({tuple(x in c for c in [C]) for x in S})==2
result={'suites':reports,'paired_response_example':'PASS','all_passed':all(x['returncode']==0 for x in reports),'scope':'Finite independent regression checks. No TeX compilation and no claim to prove general categorical results.'}
(ROOT/'checks/replay_summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));sys.exit(not result['all_passed'])
