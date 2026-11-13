#!/usr/bin/env python3
"""Final independent exact-byte/result reconciliation; requires terminal certificates."""
from pathlib import Path
import json,hashlib,sys,platform,datetime
P=Path(__file__).parent;work=P.parent.parent;root=work.parent.parent;author=work/'finite';copy=P/'clean_replay03'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
clear=read(P/'SourceCoverageClearance.json');expected=read(P/'ExpectedAuthorCounts.json')['expected_counts']
report=read(copy/'AuthorCertificate.json');origin=read(author/'AuthorCertificate.json')
assert report['status']==origin['status']=='PASS'
assert read(P/'CleanReplay03Status.json')['exit_code']==0
assert read(P/'MutationReplay03Status.json')['exit_code']==0
assert report['domain_sha256']==origin['domain_sha256']==clear['domain_sha256']==sha(author/'DOMAIN.md')==sha(copy/'DOMAIN.md')
sourcefiles=('model.py','check_integration.py','run_mutations.py','mutation_probes.py','smoke_integration.py','verify_certificate.py')
for name in sourcefiles:assert sha(copy/name)==sha(author/name)==clear['input_sha256'][name],name
for key in ('source_sha256','counts','T_rows','F_exhaustive_cases','trace_sha256'):assert report[key]==origin[key],key
for key,v in expected.items():
    if not isinstance(v,int):continue
    got=report['F_exhaustive_cases'] if key=='F_exhaustive_cases' else report['counts'][key]
    assert got==v,(key,got,v)
assert len(report['T_rows'])==54 and sum(r['executed'] for r in report['T_rows'])==112785
assert all(r['executed']==r['formula'] for r in report['T_rows'])
mut=read(copy/'MutationCertificate.json');assert mut['status']=='PASS' and mut['kind']=='FINAL_MUTATION_REPLAY'
assert mut['unmutated_certificate_sha256']==sha(copy/'AuthorCertificate.json')
assert mut['runner_sha256']==sha(copy/'run_mutations.py')
assert mut['targeted_probe_source_sha256']==sha(copy/'mutation_probes.py')
assert len(mut['mutants'])==5
for row in mut['mutants']:
    folder=copy/'mutations'/row['name'];name=row['source_file']
    assert row['exit_code']==1 and row['classification']=='INTENDED_ASSERTION'
    assert row['original_sha256']==sha(copy/name) and row['mutant_sha256']==sha(folder/name)
    assert (folder/name).read_text()==(copy/name).read_text().replace(row['edit_from'],row['edit_to'])
    assert row['stdout_sha256']==sha(folder/'stdout.log') and row['stderr_sha256']==sha(folder/'stderr.log')
    assert row['detected_failure']=='AssertionError: '+row['expected_assertion']
    if row['name'] in ('omit_MIn','erase_nullary_value'):
        assert row['targeted_probe']['status']=='PASS'
        assert row['targeted_probe']==read(folder/'TargetedProbe.json')
supp=read(P/'TargetedMutationCertificate.json');assert supp['status']=='PASS'
for c,source in (('IndependentNoImportCertificate.json','check_noimport.py'),('ExpandedMInCertificate.json','check_x_label_mins.py'),('ExpandedOCertificate.json','check_expanded_O.py'),('ParallelPathCertificate.json','check_parallel_paths.py')):
    proof=read(P/c);assert proof['status']=='PASS'
    assert proof.get('source_sha256',proof.get('checker_sha256'))==sha(P/source)
    if 'engine_sha256' in proof:assert proof['engine_sha256']==sha(P/'check_noimport.py')
assert supp['source_sha256']==sha(P/'targeted_mutation_probes.py')
base=read(work/'BaselinePreservation.json');mismatches=[]
for entry in base['files']:
    f=root/entry['path']
    if not f.exists() or sha(f)!=entry['sha256']:mismatches.append(entry['path'])
assert len(base['files'])==811 and not mismatches
baseline={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':811,'mismatches':mismatches,'contract_sha256':sha(root/'research/CompletionContract.md'),'target_sha256':sha(work/'Integrated_Targets.md'),'domain_sha256':sha(author/'DOMAIN.md')}
(P/'BaselineAfter.json').write_text(json.dumps(baseline,indent=2)+'\n')
evidence=['SourceCoverageClearance.json','CleanReplay03Input.sha256','CleanReplay03.log','CleanReplay03Status.json','MutationReplay03Status.json','IndependentNoImportCertificate.json','ExpandedMInCertificate.json','ExpandedOCertificate.json','ParallelPathCertificate.json','ExpectedAuthorCounts.json','TargetedMutationCertificate.json','BaselineBefore.json','BaselineAfter.json','check_noimport.py','check_x_label_mins.py','check_expanded_O.py','check_parallel_paths.py','derive_expected_counts.py','targeted_mutation_probes.py','verify_final_review.py']
out={'decision':'LOCAL_C_TECHNICALLY_VERIFIED','reviewer':'/root/audit_completion_finite_certificates','checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'assurance':'Agent-managed non-author source review, independent alternative representation subsets, exact-source fresh full replay; not external human certification','domain_sha256':clear['domain_sha256'],'source_sha256':{name:sha(copy/name) for name in sourcefiles},'clean_certificate_sha256':sha(copy/'AuthorCertificate.json'),'author_certificate_sha256':sha(author/'AuthorCertificate.json'),'mutation_certificate_sha256':sha(copy/'MutationCertificate.json'),'full_trace_sha256':report['trace_sha256'],'full_count_match':True,'full_counts':report['counts'],'F_exhaustive_cases':report['F_exhaustive_cases'],'full_elapsed_seconds':report['elapsed_seconds'],'baseline_811_unchanged':True,'evidence_sha256':{name:sha(P/name) for name in evidence},'python':sys.version,'platform':platform.platform(),'boundaries':['C supports fixed finite domain only, not unrestricted P coherence','Independent code covers full T and specified mixed/named subsets, not a separate full H/F engine','Full clean replay is exact author source reproduction, not independent authorship','Derived expectations and pair cardinalities are not executed-case multiplicities','No novelty or intended scientific scope acceptance','B4/F2 and full-program gates remain open; parent decides acceptance']}
(P/'IndependentCReviewCertificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
