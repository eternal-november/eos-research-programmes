#!/usr/bin/env python3
"""Verify this archive and replay finite-cover checks without changing reviewed files."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent
expected={
 "finite_cover_recovery/finite_cover_recovery.tex":"137724f0f1c29d3a84180513282ead25567df6281a564ff6b4424c37f59132d2",
 "evidence_limits/evidence_limits.tex":"a44e1e628ca0d09938035e3985b54e06a26647560c1cadc376326906ebb6b4ed",
}
verified=0
for line in (root/"MANIFEST.sha256").read_text().splitlines():
 digest,name=line.split("  ",1)
 actual=hashlib.sha256((root/name).read_bytes()).hexdigest()
 assert actual==digest,(name,actual,digest)
 verified+=1
for name,digest in expected.items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
out=root/"replay_outputs"; out.mkdir(exist_ok=True)
run=subprocess.run([sys.executable,str(root/"finite_cover_recovery/checks/verify.py")],text=True,capture_output=True,check=True)
(out/"results.json").write_text(run.stdout)
result=json.loads(run.stdout)
assert result["all_checks_passed"] is True
assert result["source_sha256"]==expected["finite_cover_recovery/finite_cover_recovery.tex"]
recorded=json.loads((root/"finite_cover_recovery/checks/results.json").read_text())
comparison=dict(result); baseline=dict(recorded)
for key in ("python","numpy"):
 comparison.pop(key,None); baseline.pop(key,None)
summary={"manifest_files_verified":verified,"reviewed_source_hashes":expected,"all_checks_passed":True,"recorded_results_match_excluding_versions":comparison==baseline,"python":result["python"],"numpy":result["numpy"],"scope":"Finite seeded/algebraic checks supplement, and do not replace, the analytic proofs and independent mathematical reviews."}
(out/"summary.json").write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
print(json.dumps(summary,indent=2,sort_keys=True))
