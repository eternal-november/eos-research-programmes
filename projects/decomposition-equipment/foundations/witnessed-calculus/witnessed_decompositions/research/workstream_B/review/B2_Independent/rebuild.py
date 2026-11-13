from pathlib import Path
import os,subprocess,hashlib,json,re,datetime
R=Path('/workspace/shared/witnessed_B_20261024/witnessed_decompositions')
D=Path('/workspace/shared/witnessed_B_20261024/reviews/B2_Independent')
modules='Core Examples Collections PathOccurrences Positive TreeOccurrences Calculus FreeCalculus FreeExtension FreeAdjunction Congruence QuotientCalculus PresentedCalculus WeightInvariant PresentationExamples RawRefinement SemanticRefinement RefinementLifting RefinementFunctoriality RefinementComparison RefinementExamples'.split()
paths=[R/'WitnessedDecompositions'/f'{n}.lean' for n in modules]+[R/'research/CompletionContract.md', R/'research/workstream_B/B1_B2_Targets.md',R/'research/workstream_B/B2_GeneralComparison.md',R/'research/workstream_B/B2_QuotientCertificate.md',R/'research/workstream_B/examples/check_semantic_refinements.py']
def hashes():return {str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
initial=hashes();(D/'source_hashes_initial.json').write_text(json.dumps(initial,indent=2)+'\n')
env=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=R,text=True))
env['LEAN_PATH']=str(D/'fresh-lean')+os.pathsep+env.get('LEAN_PATH','')
(D/'lean_env.json').write_text(json.dumps({k:env[k] for k in ['LEAN_PATH','PATH']},indent=2)+'\n')
(D/'toolchain.log').write_text(subprocess.check_output(['lean','--version'],env=env,text=True))
for n in modules:
 print('Compiling '+n,flush=True)
 p=subprocess.run(['lean','-R','.','-o',str(D/'fresh-lean/WitnessedDecompositions'/f'{n}.olean'),str(R/'WitnessedDecompositions'/f'{n}.lean')],cwd=R,env=env,capture_output=True,text=True)
 (D/(n+'.log')).write_text(p.stdout+p.stderr)
 if p.returncode:print(p.stdout+p.stderr,flush=True);raise SystemExit(p.returncode)
# Audit every named definition and theorem, not only the headline examples.
commands=[]
for module in ['SemanticRefinement','RefinementExamples']:
 stack=[]
 for line in (R/'WitnessedDecompositions'/f'{module}.lean').read_text().splitlines():
  line=line.strip()
  m=re.match(r'namespace ([\w.]+)',line)
  if m:stack.append(m.group(1));continue
  m=re.match(r'end(?: ([\w.]+))?$',line)
  if m:
   if stack:stack.pop()
   continue
  m=re.search(r'\b(?:theorem|def)\s+([\w.]+)',line)
  if m and not line.startswith(('/', '--')):
   commands.append('#print axioms '+'.'.join(stack+[m.group(1)]))
(D/'AllB2CoreExampleAxioms.lean').write_text('import WitnessedDecompositions.RefinementExamples\n'+'\n'.join(commands)+'\n')
for src in [D/'AllB2CoreExampleAxioms.lean', R/'audit/WorkstreamB2LiftingAxioms.lean', R/'audit/WorkstreamB2FunctorialityAxioms.lean', R/'audit/WorkstreamB2BridgeAxioms.lean', R/'tests/B2RefinementExamples.lean', R/'tests/B2RawEvaluationAudit.lean', D/'IndependentCompositeChecks.lean', D/'IndependentComparisonChecks.lean', R/'WorkstreamB.lean']:
 p=subprocess.run(['lean',str(src)],cwd=R,env=env,capture_output=True,text=True)
 (D/(src.stem+'.log')).write_text(p.stdout+p.stderr)
 if p.returncode:print(p.stdout+p.stderr,flush=True);raise SystemExit(p.returncode)
p=subprocess.run(['python3',str(R/'research/workstream_B/examples/check_semantic_refinements.py')],cwd=R,capture_output=True,text=True)
(D/'semantic-finite.json').write_text(p.stdout);(D/'semantic-finite.stderr').write_text(p.stderr)
if p.returncode:raise SystemExit(p.returncode)
final=hashes();(D/'source_hashes_final.json').write_text(json.dumps(final,indent=2)+'\n')
changed=[p for p in initial if initial[p]!=final[p]]
(D/'result.json').write_text(json.dumps({'status':'PASS','modules':modules,'source_changes_during_compile':changed,'axiom_commands':len(commands),'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print('PASS: final fresh 21-module build, complete B2 core/example and supplementary axiom audits, independent composite/comparison checks, author tests, aggregate import, finite checker; source changes '+repr(changed),flush=True)
