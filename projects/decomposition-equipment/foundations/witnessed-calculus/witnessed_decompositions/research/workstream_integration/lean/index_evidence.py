#!/usr/bin/env python3
"""Bind final author Lean evidence without treating it as independent acceptance."""
from pathlib import Path
import json,re,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
runs=sorted((HERE/'runs').glob('*/result.json'))
passed=[p for p in runs if json.loads(p.read_text())['status']=='PASS']
assert passed, 'No complete fresh run'
run=passed[-1];data=json.loads(run.read_text());out=run.parent
assert data.get('axiom_report_count')==31,'Final audit has not run'
sources={
 'QuotientArrowCertificates.lean':'WitnessedDecompositions.Integration',
 'PublicExampleBridge.lean':'WitnessedDecompositions.Integration',
 'GraphForestNormalForms.lean':'IntegrationGraphForest'}
items=[]
for filename,ns in sources.items():
 p=HERE/filename;text=p.read_text()
 for m in re.finditer(r'^theorem (\w+)',text,re.M):
  end=text.index(':=',m.start())
  items.append({'declaration':ns+'.'+m.group(1),'source':str(p.relative_to(ROOT)),
   'source_sha256':sha(p),'line':text.count('\n',0,m.start())+1,
   'exact_statement':text[m.start():end].rstrip(),
   'scope':'conditional local-code transfer; no Comp formalization' if m.group(1)=='arrow_eq_iff_entry_codes' else
      ('six-vertex located graph representative, arbitrary finite forests' if ns=='IntegrationGraphForest' else 'actual arbitrary A3/B2 API; example bridge specializes accepted B2')})
axioms={name:[x.strip() for x in deps.split(',') if x.strip()] for name,deps in
 re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(out/'AxiomAudit.log').read_text(),re.S)}
assert len(items)==len(axioms)==31
assert set(axioms)=={x['declaration'] for x in items}
for item in items:item['actual_axioms']=axioms[item['declaration']]
(HERE/'TheoremIndex.json').write_text(json.dumps({'contract_sha256':'47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e','target_sha256':'2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b','assurance':'AUTHOR_VERIFIED; independent review/acceptance separate','evidence':'L for exact declarations; P bridges explicitly separate','declarations':items},indent=2)+'\n')
(HERE/'AxiomReport.json').write_text(json.dumps({'count':len(axioms),'actual_closures':axioms,'whitelist':['propext','Classical.choice','Quot.sound'],'audit_log':str((out/'AxiomAudit.log').relative_to(ROOT)),'audit_log_sha256':sha(out/'AxiomAudit.log')},indent=2)+'\n')
(HERE/'DependencySnapshot.json').write_text(json.dumps({'fresh_result':str(run.relative_to(ROOT)),'fresh_result_sha256':sha(run),'modules':data['modules'],'external_dependencies':data['external_lean_path'],'baseline_before':data['baseline_before'],'baseline_after':data['baseline_after'],'new_theorem_implementations':list(sources)},indent=2)+'\n')
paths=[HERE/f for f in list(sources)+['AxiomAudit.lean','build.py','index_evidence.py','README.md','TheoremIndex.json','AxiomReport.json','DependencySnapshot.json']]
if (HERE/'HarnessPortability.json').exists():paths.append(HERE/'HarnessPortability.json')
if (HERE/'HarnessRealpath.diff').exists():paths.append(HERE/'HarnessRealpath.diff')
(HERE/'SourceSnapshot.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(ROOT))+'\n' for p in paths))
print(json.dumps({'status':'PASS','source_snapshot_sha256':sha(HERE/'SourceSnapshot.sha256'),'final_run':str(run),'final_run_sha256':sha(run),'declarations':len(items),'fresh_modules':len(data['modules'])},indent=2))
