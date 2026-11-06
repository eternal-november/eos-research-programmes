"""Reproduce the revised Byzantine-control package at its declared scopes.

This checks evidence and exact source bindings. The independent scientific and
original-intent judgment belongs to AUDIT.md, not to successful exit codes.
Historical completion verdicts are never imported as the current verdict.
"""
from __future__ import annotations
import argparse
import ast
from concurrent.futures import ThreadPoolExecutor, as_completed
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent
REPO=PROJECT.parent.parent
GOAL_CONTRACT='7343f54e2c839cc7898c6f0e6c86bea8f4b53f25'
FULL_PROGRAM_WRAPPER=('> **Historical completion record.** The assessment below belongs to the earlier R1–R8 integration package and its then-current interpretation. It does not certify the later BC/RN/IA/AC program or the active Goal. Use [the current contract](DOWNSTREAM-CONTRACT.md) and [current research state](TODO.md). The prior body is retained unchanged for its scoped results and audit history; the new verifier checks that preserved body against the historical records.\n\n')
LEAN=Path(os.environ['USERPROFILE'])/'.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'
CONTRACT_FILES=('DOWNSTREAM-CONTRACT.md','FAULT-COVERAGE.md','ASSUMPTION-REVIEW.md',
    'ASSUMPTION-CHALLENGE-AUDIT.md','REMAINING-PROGRAM.md','CONTRACT-CHALLENGE.md','MOTIVATING-PROBLEM.md')
CHANGED_RETAINED={
    'integration':{'TODO.md'},
    'joint-control':{'ASSUMPTION-REVIEW.md','DOWNSTREAM-CONTRACT.md','FAULT-COVERAGE.md','REMAINING-PROGRAM.md'},
    'recurring-control':{'ASSUMPTION-REVIEW.md','CONTRACT-CHALLENGE.md','DOWNSTREAM-CONTRACT.md',
                         'FAULT-COVERAGE.md','REMAINING-PROGRAM.md','TODO.md'},
}
CURRENT_MODELS=(
    'information_model.py','timing_model.py','return_model.py','clamp_model.py','operation_model.py',
    'continuity_model.py','source_probe.py','capacity_probe.py','acquisition_model.py','streaming_model.py',
    'bootstrap_model.py','program_model.py','port_model.py','incidence_model.py','probe_map_model.py',
    'transducer_model.py','boundary_model.py','effects_model.py','geometry_model.py','hybrid_model.py',
    'initial_return_model.py','receiver_model.py','flow_existence_model.py','coupled_port_model.py',
    'composition_model.py','boundary_factorization_model.py','port_source_model.py','port_resource_model.py',
    'primary_assembly_model.py','primary_comparison_model.py',
    'cycle_model.py','resource_model.py','access_model.py','rate_comparison_model.py',
    'barrier_model.py','conduit_model.py','feasibility_model.py','hard_boundary_model.py','receiver_power_model.py',
)
LOCAL_MODEL_SCOPES={name:'Component evidence at its stated scope; positive use is through the named primary adapter'
                    for name in CURRENT_MODELS}
LOCAL_MODEL_SCOPES.update({
    'capacity_probe.py':'Generic chronological-resource/finite-health diagnostic; not achieved full-source service',
    'source_probe.py':'Retained unit-capacity and illustrative commissioning subcase; not the primary M_raw source',
    'access_model.py':'Historical conditional access/capacity point; current numbers are in PRIMARY-COMPARISONS',
    'rate_comparison_model.py':'Historical optional-electrical comparison; selected-source H is separately rebound',
    'barrier_model.py':'Conditional earlier barrier component; not independent admission of the primary source',
    'conduit_model.py':'Conditional earlier conduit candidate; no electrical realization is inferred',
    'feasibility_model.py':'Earlier candidate algebra; assumed service is not achieved return',
    'hard_boundary_model.py':'Hard-boundary/stock kernel used by the retained resource inventory; old point not promoted',
    'receiver_power_model.py':'Conditional electrical receiver realization; new source has its own direct work account',
})
ASSERT_FREE_COMPONENTS={'boundary_model.py','incidence_model.py','resource_model.py'}
RETAINED_MODELS={
    'joint-control':('information_model.py','evolution_model.py','control_model.py','boundary_model.py','joint_model.py'),
    'recurring-control':('renewal_model.py','runtime_model.py','control_model.py','replacement_model.py'),
}
CURRENT_PROOFS=('Information.lean','Timing.lean','Return.lean','Clamp.lean','Operations.lean',
                'Continuity.lean','Acquisition.lean','Streaming.lean','Hybrid.lean','Effects.lean','Receiver.lean')
RETAINED_PROOFS={
    'joint-control':('Information.lean','Evolution.lean','Restoration.lean','Control.lean'),
    'recurring-control':('Renewal.lean','Information.lean','Control.lean'),
}


def need(ok,message):
    if not ok:raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def fingerprints():
    paths=[p for p in PROJECT.rglob('*') if p.is_file()
           and (p.suffix in ('.md','.py','.lean','.json','.ps1') or p.name=='lean-toolchain')
           and p!=HERE/'verification.json' and '__pycache__' not in p.parts]
    return {p.relative_to(PROJECT).as_posix():digest(p) for p in sorted(paths)}


def contract_binding():
    bound={}
    for name in CONTRACT_FILES:
        data=subprocess.check_output(['git','show',GOAL_CONTRACT+':theories-and-designs/byzantine-control/'+name],cwd=REPO)
        expected=sha256(data.replace(b'\r\n',b'\n')).hexdigest()
        need(digest(PROJECT/name)==expected,'The active Goal contract changed: '+name)
        bound[name]=expected
    return dict(commit=GOAL_CONTRACT,sources_sha256_lf=bound)


def retained_binding():
    result={}
    for folder,allowed in CHANGED_RETAINED.items():
        path=PROJECT/folder/'verification.json'
        historical=subprocess.check_output(['git','show',GOAL_CONTRACT+':theories-and-designs/byzantine-control/'+folder+'/verification.json'],cwd=REPO)
        need(sha256(historical.replace(b'\r\n',b'\n')).hexdigest()==digest(path),
             'Historical manifest itself changed: '+folder)
        record=json.loads(path.read_text(encoding='utf-8-sig'))
        need(record['verification_passed'],'Retained record did not pass: '+folder)
        matched={};replaced={}
        for name,old in record['sources_sha256_lf'].items():
            actual=digest(PROJECT/name)
            if actual==old:matched[name]=actual
            elif name=='FULL-PROGRAM.md':
                current=(PROJECT/name).read_bytes().replace(b'\r\n',b'\n')
                prefix=FULL_PROGRAM_WRAPPER.encode('utf-8')
                need(current.startswith(prefix) and sha256(current[len(prefix):]).hexdigest()==old,
                     'Historical navigation wrapper changed substantive content')
                replaced[name]=dict(historical=old,current=actual,preserved_body_sha256_lf=old,
                    change='historical-scope navigation prefix only')
            else:
                need(name in allowed,'Unreviewed retained scientific change: '+name)
                replaced[name]=dict(historical=old,current=actual)
        need(set(replaced)==allowed|{'FULL-PROGRAM.md'},'Historical replacement inventory changed: '+folder)
        result[folder]=dict(record_sha256_lf=digest(path),matched_inputs=matched,
            replaced_requirements_or_workflow=replaced,
            scope='Original encoded/source conclusions only; historical completion verdict not reused')
    return result


def run(command):
    env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
    p=subprocess.run(command,cwd=HERE,capture_output=True,text=True,encoding='utf-8',env=env)
    need(p.returncode==0,repr(command)+'\n'+p.stdout+'\n'+p.stderr)
    need(not p.stderr.strip(),'Unexpected diagnostic from '+repr(command)+'\n'+p.stderr)
    return p.stdout.replace('\r\n','\n').strip()


def assert_free_project_closure(path):
    """Audit the explicit legacy exception, including its one dynamic source.

    This is not a general Python sandbox or arbitrary-program equivalence
    theorem. The actual bound --check runs are also compared in both modes.
    """
    pending=[path];seen={}
    allowed_exec=ast.parse("exec(compile(SOURCE.read_text(encoding='utf-8-sig'),str(SOURCE),'exec'),env)").body[0].value
    allowed_calls={ast.dump(allowed_exec),ast.dump(allowed_exec.args[0])}
    while pending:
        source=pending.pop()
        if source.name in seen:continue
        tree=ast.parse(source.read_text(encoding='utf-8-sig'))
        for node in ast.walk(tree):
            need(not isinstance(node,ast.Assert),'Optimization-sensitive assert in '+source.name)
            need(not (isinstance(node,ast.Name) and node.id=='__debug__'),
                 'Optimization-sensitive branch in '+source.name)
            if isinstance(node,ast.Import):names=[x.name for x in node.names]
            elif isinstance(node,ast.ImportFrom):names=[node.module] if node.module else []
            else:names=[]
            for name in names:
                candidate=source.parent/(name.split('.')[0]+'.py')
                if candidate.is_file():pending.append(candidate)
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id in ('exec','eval','compile','__import__'):
                need(source.name=='program_model.py' and ast.dump(node) in allowed_calls,
                     'Unaudited dynamic project code in '+source.name)
                pending.append(source.parent/'program_source.py')
        seen[source.name]=digest(source)
    return dict(sorted(seen.items()))


def check_model(path,lean):
    env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
    command=[sys.executable,'-B',str(path),'--check']
    source=path.read_text(encoding='utf-8-sig')
    if re.search(r"add_argument\(['\"]--lean['\"]",source):command+=['--lean',str(lean)]
    is_exception=path.parent==HERE and path.name in ASSERT_FREE_COMPONENTS
    closure=assert_free_project_closure(path) if is_exception else None
    probe=subprocess.run([command[0],'-O',*command[1:]],cwd=HERE,
        capture_output=True,text=True,encoding='utf-8',env=env)
    if is_exception:
        need(probe.returncode==0 and not probe.stderr.strip(),'Assert-free optimized check failed: '+str(path))
    else:
        need(probe.returncode!=0 and 'optimiz' in probe.stderr.lower(),
             'No demonstrated optimization rejection: '+str(path))
    output=run(command)
    if is_exception:need(probe.stdout.replace('\r\n','\n').strip()==output,
                         'Optimized/unoptimized bound results differ: '+str(path))
    return dict(passed=True,optimized_execution_rejected=not is_exception,
        assert_free_project_sources=closure,
        optimized_bound_check_also_matches=is_exception,
        supported_aggregate_execution='unoptimized Python3.12 with PYTHONOPTIMIZE removed',
        scope=LOCAL_MODEL_SCOPES[path.name] if path.parent==HERE else 'Retained result at its historical hypotheses',
        stdout_sha256_lf=sha256(output.encode()).hexdigest())


def check_coverage_inventory():
    coverage=(HERE/'COVERAGE.md').read_text(encoding='utf-8-sig')
    families=re.findall(r'^\| (M\d\d)\b',coverage,re.M)
    chains=re.findall(r'^\| (\d+) \|',coverage,re.M)
    assumptions=(HERE/'ASSUMPTIONS.md').read_text(encoding='utf-8-sig')
    patterns=re.findall(r'^\| (A\d\d)\b',assumptions,re.M)
    need(families==[f'M{i:02}' for i in range(1,46)],'Fault-family inventory incomplete or duplicated')
    need(chains==[str(i) for i in range(1,19)],'Joint-chain inventory incomplete or duplicated')
    need(patterns==[f'A{i:02}' for i in range(1,19)],'Assumption inventory incomplete or duplicated')
    return dict(families=families,chains=chains,assumption_patterns=patterns,
                scope='Inventory consistency only; adequacy is the independent audit judgment')


def load_checker():
    path=PROJECT/'integration/verify.py'
    spec=importlib.util.spec_from_file_location('primary_strict_lean_checker',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def main():
    need(not sys.flags.optimize and sys.version_info[:2]==(3,12),'Unoptimized Python3.12 is required')
    ap=argparse.ArgumentParser(description=__doc__)
    modes=ap.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    ap.add_argument('--lean',type=Path,default=LEAN)
    args=ap.parse_args()
    for name in ('PORT-SOURCE.md','PORT-RESOURCES.md','PRIMARY-ASSEMBLY.md','PRIMARY-COMPARISONS.md',
                 'ASSUMPTIONS.md','COVERAGE.md','AUDIT.md','SYNTHESIS.md','LEDGER.md'):
        need((HERE/name).is_file(),'Missing final artifact: '+name)
    before=fingerprints();path=HERE/'verification.json'
    expected=json.loads(path.read_text(encoding='utf-8-sig')) if args.check else None
    if expected:need(before==expected['sources_sha256_lf'],'Inputs differ; review before deliberate refresh')
    contract=contract_binding();retained=retained_binding();coverage=check_coverage_inventory()
    version=run([str(args.lean),'--version'])
    need('version 4.33.0,' in version,'Pinned Lean4.33.0 is required')
    checker=load_checker()
    print('Checking strict verifier rejection fixtures',flush=True)
    guards=checker.verifier_regressions(str(args.lean))
    present={p.name for pattern in ('*model.py','*probe.py') for p in HERE.glob(pattern)}
    need(set(CURRENT_MODELS)==present==set(LOCAL_MODEL_SCOPES),'Unclassified or missing current model/probe')
    need(set(CURRENT_PROOFS)=={p.name for p in HERE.glob('*.lean')},'Uninventoried current Lean module')
    proofs={}
    for folder,names in [('local-control',CURRENT_PROOFS),*RETAINED_PROOFS.items()]:
        for name in names:
            key=folder+'/'+name
            print('Strict proof check: '+key,flush=True)
            proofs[key]=checker.proof_check(PROJECT/key,str(args.lean))
    jobs={('local-control/'+name):HERE/name for name in CURRENT_MODELS}
    for folder,names in RETAINED_MODELS.items():
        jobs.update({folder+'/'+name:PROJECT/folder/name for name in names})
    checks={};failures={}
    with ThreadPoolExecutor(max_workers=3) as pool:
        futures={pool.submit(check_model,p,args.lean):name for name,p in jobs.items()}
        for future in as_completed(futures):
            name=futures[future]
            try:
                checks[name]=future.result()
                print('Reproduced '+name,flush=True)
            except Exception as error:
                failures[name]=str(error)
                print('FAILED '+name+': '+str(error),flush=True)
    need(not failures,'Failed evidence checks:\n'+'\n'.join(name+'\n'+failures[name] for name in sorted(failures)))
    need(before==fingerprints(),'Sources changed during aggregate checking')
    result=dict(schema='byzantine-primary-verification-v1',verification_passed=True,
        scope='Strict kernels, unchanged retained science, current source/adapter checks and exact bindings. Independent program/intent verdict is AUDIT.md.',
        python_major_minor=list(sys.version_info[:2]),lean_version=version,
        goal_contract=contract,sources_sha256_lf=before,retained_evidence=retained,
        coverage_inventory=coverage,axiom_dependencies=proofs,
        selected_declaration_count=sum(len(v) for v in proofs.values()),verifier_guard_checks=guards,
        executable_checks=dict(sorted(checks.items())))
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(result==expected,'Aggregate reproduction differs')
    print('PASS matching evidence; program completion additionally requires the independent audit',flush=True)


if __name__=='__main__':main()
