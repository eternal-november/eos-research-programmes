"""Reproduce recurring-control evidence and freeze the exact reviewed package.

Passing computations are distinct from the independent full-program verdict in
AUDIT.md. Historical completion labels are never imported as the current verdict.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent
LEAN=Path(os.environ['USERPROFILE'])/'.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'
CHANGED_REQUIREMENTS={'ASSUMPTION-REVIEW.md','DOWNSTREAM-CONTRACT.md',
                      'FAULT-COVERAGE.md','REMAINING-PROGRAM.md'}


def require(ok,message):
    if not ok:raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def retained_binding():
    result={}
    for folder,excluded in (('integration',{'TODO.md'}),('joint-control',CHANGED_REQUIREMENTS)):
        path=PROJECT/folder/'verification.json'
        record=json.loads(path.read_text(encoding='utf-8'))
        require(record['verification_passed'],'Historical record did not pass')
        matched={};replaced={}
        for name,expected in record['sources_sha256_lf'].items():
            current=digest(PROJECT/name)
            if name in excluded:
                require(current!=expected,'Declared historical replacement no longer differs: '+name)
                replaced[name]={'historical':expected,'current':current}
            else:
                require(current==expected,'Retained scientific input changed: '+name)
                matched[name]=current
        result[folder]={'record_sha256_lf':digest(path),'matched_inputs':matched,
            'replaced_requirements_or_workflow':replaced,
            'scope':'Unchanged encoded/source results at their original hypotheses; historical completion is not reused'}
    return result


def inputs():
    paths={p for p in HERE.iterdir() if p.is_file() and p.suffix in ('.md','.py','.lean','.json')
           and p.name!='verification.json'}
    parents=('DOWNSTREAM-CONTRACT.md','FAULT-COVERAGE.md','ASSUMPTION-REVIEW.md',
        'REMAINING-PROGRAM.md','CONTRACT-CHALLENGE.md','INTENT-ASSUMPTION-AUDIT.md',
        'MOTIVATING-PROBLEM.md','REVISED-AUDIT.md','TODO.md')
    paths.update(PROJECT/name for name in parents)
    for folder in ('integration','joint-control'):
        record_path=PROJECT/folder/'verification.json'
        paths.add(record_path)
        record=json.loads(record_path.read_text(encoding='utf-8'))
        paths.update(PROJECT/name for name in record['sources_sha256_lf'])
    return {p.relative_to(PROJECT).as_posix():digest(p) for p in sorted(paths)}


def run(command):
    env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
    p=subprocess.run(command,cwd=HERE,text=True,encoding='utf-8',capture_output=True,env=env)
    require(p.returncode==0,repr(command)+'\n'+p.stdout+'\n'+p.stderr)
    require(not p.stderr.strip(),'Unexpected diagnostic: '+p.stderr)
    return p.stdout.replace('\r\n','\n').strip()


def main():
    require(not sys.flags.optimize and sys.version_info[:2]==(3,12),
            'Unoptimized Python3.12 is required')
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    p.add_argument('--lean',type=Path,default=LEAN)
    args=p.parse_args()
    required=('PROGRAM.md','ASSEMBLY.md','INSTANCE.md','SOURCE.md','SOURCES.md',
        'ASSUMPTIONS.md','ADMISSION.md','LEDGER.md','RENEWAL.md','INFORMATION.md',
        'RUNTIME.md','CONTROL.md','COMPOSITION.md','BOUNDARIES.md','COVERAGE.md','AUDIT.md')
    for name in required:require((HERE/name).is_file(),'Missing reviewed artifact: '+name)
    before=inputs();retained=retained_binding()
    path=HERE/'verification.json'
    expected=json.loads(path.read_text(encoding='utf-8')) if args.check else None
    if expected:require(before==expected['sources_sha256_lf'],'Inputs differ; inspect before deliberate refresh')
    version=run([str(args.lean),'--version'])
    require('version 4.33.0,' in version,'Pinned Lean4.33.0 is required')
    checker=load_module('recurring_strict_checker',PROJECT/'integration/verify.py')
    print('Checking verifier rejection/axiom inventory guards',flush=True)
    guards=checker.verifier_regressions(str(args.lean))
    proofs={}
    for name in ('Renewal.lean','Information.lean','Control.lean'):
        print('Strict proof check: '+name,flush=True)
        proofs[name]=checker.proof_check(HERE/name,str(args.lean))
    require(set(proofs)=={p.name for p in HERE.glob('*.lean')},'Uninventoried current proof module')
    old_proofs={}
    for name in ('Information.lean','Evolution.lean','Restoration.lean','Control.lean'):
        print('Rechecking retained joint proof: '+name,flush=True)
        old_proofs[name]=checker.proof_check(PROJECT/'joint-control'/name,str(args.lean))
    commands={}
    for name in ('renewal_model.py','runtime_model.py','control_model.py','replacement_model.py'):
        command=[sys.executable,'-B',str(HERE/name),'--check']
        if name in ('renewal_model.py','runtime_model.py'):command+=['--lean',str(args.lean)]
        commands['recurring-control/'+name]=command
    for name in ('information_model.py','evolution_model.py','control_model.py','boundary_model.py','joint_model.py'):
        command=[sys.executable,'-B',str(PROJECT/'joint-control'/name),'--check']
        if name=='evolution_model.py':command+=['--lean',str(args.lean)]
        commands['joint-control/'+name]=command
    optimization={};checks={}
    for name,command in commands.items():
        probe=subprocess.run([sys.executable,'-O','-B',command[2],'--check'],
            cwd=HERE,text=True,encoding='utf-8',capture_output=True)
        require(probe.returncode!=0 and 'Unoptimized' in probe.stderr,
                'Component may execute with assertions disabled: '+name)
        optimization[name]=True
        print('Reproducing '+name,flush=True)
        output=run(command)
        checks[name]={'passed':True,'stdout_sha256':hashlib.sha256(output.encode()).hexdigest()}
    require(before==inputs(),'Sources changed during verification')
    actual={'schema':'byzantine-recurring-verification-v1','verification_passed':True,
        'scope':'Strict selected proofs, retained unchanged evidence and executable reproduction. Independent full-program and intent verdict remains AUDIT.md.',
        'python_major_minor':list(sys.version_info[:2]),'lean_version':version,
        'sources_sha256_lf':before,'current_axiom_dependencies':proofs,
        'current_declaration_count':sum(map(len,proofs.values())),
        'retained_joint_axiom_dependencies':old_proofs,
        'verifier_guard_checks':guards,'component_optimization_guards':optimization,
        'executable_checks':checks,'retained_evidence_binding':retained}
    if args.write:path.write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(actual==expected,'Reproduction differs from frozen record')
    print('PASS source-bound proof/executable checks; completion is separately audited',flush=True)


if __name__=='__main__':main()
