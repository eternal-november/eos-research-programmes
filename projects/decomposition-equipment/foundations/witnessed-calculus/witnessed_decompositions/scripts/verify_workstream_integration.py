#!/usr/bin/env python3
"""Reproduce frozen integrated technical evidence; scientific acceptance is separate."""
from pathlib import Path
import argparse,ast,datetime,hashlib,json,os,shutil,subprocess,sys,traceback,tempfile
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'research/workstream_integration'
CONTRACT='47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET='2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b'
DOMAIN='d01495686d5f3f01cc635061d7789f64ab0cf5a370571d144971cb819dba52fa'
FINITE_FILES=['model.py','check_integration.py','run_mutations.py','mutation_probes.py','smoke_integration.py','verify_certificate.py','DOMAIN.md']
REVIEW_FILES=['check_noimport.py','targeted_mutation_probes.py','REVIEW_DOMAIN.md']
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def invariant():
 b=json.loads((P/'BaselinePreservation.json').read_text());assert len(b['files'])==811
 for row in b['files']:assert digest(ROOT/row['path'])==row['sha256'],row['path']
 assert digest(ROOT/'research/CompletionContract.md')==CONTRACT
 assert digest(P/'Integrated_Targets.md')==TARGET
 assert digest(P/'finite/DOMAIN.md')==DOMAIN
 for line in (P/'Integrated_SourceSnapshot.sha256').read_text().splitlines():
  h,rel=line.split('  ',1);assert digest(ROOT/rel)==h,rel
 return 811
def run(cmd,cwd,log):
 with log.open('w') as f:r=subprocess.run([str(x) for x in cmd],cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode==0,(cmd,r.returncode,str(log))
def stable(x):
 if isinstance(x,dict):return {k:stable(v) for k,v in x.items() if k not in {'elapsed_seconds','python','python_version'}}
 if isinstance(x,list):return [stable(v) for v in x]
 return x
def compare(a,b):assert stable(json.loads(a.read_text()))==stable(json.loads(b.read_text())),(a,b)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--completed-fresh-inherited-result',type=Path,help='Optional already-completed SAME-checkout C3 chain result; hashes still rechecked. Default reruns complete chain.');ap.add_argument('--check-receipts',action='store_true',help='Only validate exact final source/evidence receipts and orchestration syntax; does NOT rerun mathematical checks.');args=ap.parse_args()
 if args.check_receipts:
  count=invariant();manifest=json.loads((P/'evidence/FinalEvidenceManifest.json').read_text())
  for row in manifest['files']:assert digest(ROOT/row['path'])==row['sha256'],row['path']
  for rel in manifest['python_sources']:ast.parse((ROOT/rel).read_text(),filename=rel)
  subprocess.run(['bash','-n',str(ROOT/'verify_workstream_integration.sh')],check=True)
  with tempfile.TemporaryDirectory(prefix='integration-orchestration-') as tmp:
   d=Path(tmp)
   for name in FINITE_FILES:shutil.copy2(P/'finite'/name,d/name)
   subprocess.run([sys.executable,'-B','-c','import model, check_integration, run_mutations, mutation_probes, smoke_integration; print("finite copied-source import closure PASS; no domain execution")'],cwd=d,check=True)
  result={'status':'PASS_RECEIPT_CHECK_NOT_REEXECUTION','baseline_files':count,'verified_receipt_files':len(manifest['files']),'orchestration_check':'shell/Python syntax plus clean finite source-copy/import closure; no domain rerun','source_snapshot_sha256':digest(P/'Integrated_SourceSnapshot.sha256'),'manifest_sha256':digest(P/'evidence/FinalEvidenceManifest.json'),'wrapper_execution':'Only syntax/source/receipt checks executed. Complete mathematical coverage is the separately documented fresh component runs; default full wrapper was NOT executed as a whole.'}
  (P/'evidence/ReceiptVerification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return 0
 out=ROOT/'reproduction_integration'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out.mkdir(parents=True)
 report={'status':'RUNNING','contract_sha256':CONTRACT,'target_sha256':TARGET,'domain_sha256':DOMAIN,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'out':str(out.relative_to(ROOT))}
 try:
  report['baseline_before']=invariant()
  if args.completed_fresh_inherited_result:
   prev=args.completed_fresh_inherited_result.resolve();assert prev.is_relative_to((ROOT/'reproduction_C3').resolve())
   q=json.loads(prev.read_text());assert q['status']=='PASS' and q['contract_sha256']==CONTRACT
   report['inherited_chain']={'mode':'Completed fresh same-checkout chain reused; baseline bytes reverified','result':str(prev.relative_to(ROOT)),'sha256':digest(prev),'original_started_utc':q['started_utc'],'original_finished_utc':q['finished_utc']}
  else:
   run(['bash','verify_workstream_C3.sh'],ROOT,out/'inherited-full-chain.log')
   prev=max((ROOT/'reproduction_C3').glob('*/result.json'),key=lambda x:x.stat().st_mtime);q=json.loads(prev.read_text());assert q['status']=='PASS'
   report['inherited_chain']={'mode':'Complete inherited A/B/C1/C2/C3 rerun','result':str(prev.relative_to(ROOT)),'sha256':digest(prev)}
  run([sys.executable,P/'lean/build.py'],ROOT,out/'new-lean.log')
  lr=max((P/'lean/runs').glob('*/result.json'),key=lambda x:x.stat().st_mtime);l=json.loads(lr.read_text());assert l['status']=='PASS' and l['axiom_report_count']==31
  report['new_lean']={'result':str(lr.relative_to(ROOT)),'sha256':digest(lr),'module_count':len(l['modules']),'axiom_report_count':l['axiom_report_count'],'dependency_selection':l['dependency_selection']}
  finite=out/'finite';finite.mkdir()
  for name in FINITE_FILES:shutil.copy2(P/'finite'/name,finite/name)
  run([sys.executable,'-u','check_integration.py'],finite,out/'finite-author.log')
  compare(finite/'AuthorCertificate.json',P/'finite/AuthorCertificate.json')
  run([sys.executable,'verify_certificate.py'],finite,out/'finite-formulas.log')
  run([sys.executable,'-u','run_mutations.py'],finite,out/'finite-mutations.log')
  muts=json.loads((finite/'MutationCertificate.json').read_text());assert muts['status']=='PASS' and len(muts['mutants'])==5
  for row in muts['mutants']:assert row['classification']=='INTENDED_ASSERTION' and row['exit_code']==1
  original=json.loads((P/'finite/MutationCertificate.json').read_text())
  keys=['name','source_file','original_sha256','mutant_sha256','edit_from','edit_to','detected_failure','expected_assertion','detecting_function','classification','targeted_probe']
  assert [{k:r[k] for k in keys} for r in muts['mutants']]==[{k:r[k] for k in keys} for r in original['mutants']]
  independent=out/'independent';independent.mkdir();src=P/'review/finite_independent_20261025'
  for name in REVIEW_FILES:shutil.copy2(src/name,independent/name)
  run([sys.executable,'-u','check_noimport.py'],independent,out/'finite-independent.log')
  compare(independent/'IndependentNoImportCertificate.json',src/'IndependentNoImportCertificate.json')
  run([sys.executable,'targeted_mutation_probes.py',finite],independent,out/'finite-independent-mutation-probes.log')
  compare(independent/'TargetedMutationCertificate.json',src/'TargetedMutationCertificate.json')
  report['finite']={'author_certificate_sha256':digest(finite/'AuthorCertificate.json'),'same_mathematical_certificate':True,'mutants':5,'independent_targeted_probe_sha256':digest(independent/'TargetedMutationCertificate.json'),'independent_noimport_certificate_sha256':digest(independent/'IndependentNoImportCertificate.json'),'independent_scope':'Full T plus reviewer-defined mixed/named subset; complete author domain separately replayed, not falsely equated'}
  report['baseline_after']=invariant();report['status']='PASS'
  report['source_snapshot_sha256']=digest(P/'Integrated_SourceSnapshot.sha256')
  report['limits']='Technical evidence only; P proofs separately reviewed; no scientific significance or full §3.6 acceptance.'
 except BaseException as e:report.update(status='FAIL',error=repr(e));traceback.print_exc()
 finally:
  report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(out/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
 return 0 if report['status']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
