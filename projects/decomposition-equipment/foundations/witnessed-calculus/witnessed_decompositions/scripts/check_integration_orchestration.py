#!/usr/bin/env python3
"""Control-flow/copy smoke only: stub expensive commands with already audited receipts.
Never a mathematical replay, never an aggregate full-wrapper PASS claim.
"""
from pathlib import Path
import contextlib,hashlib,importlib.util,io,json,shutil,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'research/workstream_integration'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 spec=importlib.util.spec_from_file_location('integration_driver',ROOT/'scripts/verify_workstream_integration.py')
 d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
 seen=[]
 with tempfile.TemporaryDirectory(prefix='integration-control-flow-') as folder:
  root=Path(folder);p=root/'research/workstream_integration';p.mkdir(parents=True)
  for relative in ['Integrated_SourceSnapshot.sha256','lean/current_source_replay/result.json','finite/AuthorCertificate.json','finite/MutationCertificate.json','review/finite_independent_20261025/IndependentNoImportCertificate.json','review/finite_independent_20261025/TargetedMutationCertificate.json']:
   dest=p/relative;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/relative,dest)
  for name in d.FINITE_FILES:
   dest=p/'finite'/name;shutil.copy2(P/'finite'/name,dest)
  for name in d.REVIEW_FILES:shutil.copy2(P/'review/finite_independent_20261025'/name,p/'review/finite_independent_20261025'/name)
  def stub(cmd,cwd,log):
   names=[Path(str(x)).name for x in cmd];seen.append(names)
   log.write_text('STUB: no mathematical command executed\n')
   if 'verify_workstream_C3.sh' in names:
    dest=root/'reproduction_C3/STUB/result.json';dest.parent.mkdir(parents=True);dest.write_text(json.dumps({'status':'PASS'}))
   elif 'build.py' in names:
    dest=p/'lean/runs/STUB/result.json';dest.parent.mkdir(parents=True);shutil.copy2(P/'lean/current_source_replay/result.json',dest)
   elif 'check_integration.py' in names:shutil.copy2(P/'finite/AuthorCertificate.json',cwd/'AuthorCertificate.json')
   elif 'verify_certificate.py' in names:pass
   elif 'run_mutations.py' in names:shutil.copy2(P/'finite/MutationCertificate.json',cwd/'MutationCertificate.json')
   elif 'check_noimport.py' in names:shutil.copy2(P/'review/finite_independent_20261025/IndependentNoImportCertificate.json',cwd/'IndependentNoImportCertificate.json')
   elif 'targeted_mutation_probes.py' in names:shutil.copy2(P/'review/finite_independent_20261025/TargetedMutationCertificate.json',cwd/'TargetedMutationCertificate.json')
   else:raise AssertionError(names)
  d.ROOT=root;d.P=p;d.run=stub;d.invariant=lambda:811
  original=sys.argv;sys.argv=['verify_workstream_integration.py']
  try:
   with contextlib.redirect_stdout(io.StringIO()):code=d.main()
  finally:sys.argv=original
  assert code==0,code
  assert len(seen)==7,seen
  result=json.loads(next((root/'reproduction_integration').glob('*/result.json')).read_text())
  assert result['finite']['same_mathematical_certificate'] and result['new_lean']['axiom_report_count']==31
 report={'status':'PASS_CONTROL_FLOW_WITH_STUBBED_COMMANDS_ONLY','driver_sha256':sha(ROOT/'scripts/verify_workstream_integration.py'),'smoke_script_sha256':sha(Path(__file__)),'commands_dispatched':seen,'scope':'Tests temporary file copying, certificate comparison and default control flow with all expensive subprocesses stubbed. Source invariants are stubbed here and separately checked by --check-receipts. NO new mathematical replay or full-wrapper execution is claimed. Temporary simulated PASS files were deleted.'}
 (P/'evidence/OrchestrationControlFlowCheck.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
