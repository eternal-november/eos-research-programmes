#!/usr/bin/env python3
"""Replay baseline and optimization-safe semantic mutations, recording hashes."""
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys


HERE=Path(__file__).resolve().parent
SCRIPT=HERE/'verify_i3.py'


def require(ok,message):
    if not ok:
        raise RuntimeError(message)


def run(options,env=None):
    return subprocess.run([sys.executable,*options],cwd=HERE,env=env,
                          capture_output=True,text=True,timeout=300)


def main():
    require(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(SCRIPT.read_text()))),
            'verification depends on removable assert statements')
    receipts=[]
    canonical=None
    for mode,prefix,env in (
        ('normal',[],None),
        ('python_-O',['-O'],None),
        ('PYTHONOPTIMIZE_1',[],dict(os.environ,PYTHONOPTIMIZE='1')),
    ):
        result=run([*prefix,str(SCRIPT)],env)
        require(result.returncode==0,f'{mode} baseline failed: {result.stderr}')
        payload=json.loads(result.stdout)
        require(payload['status']=='PASS',f'{mode} baseline did not pass')
        if canonical is None:
            canonical=payload
            (HERE/'results.json').write_text(result.stdout)
        require(payload==canonical,f'{mode} changed finite mathematical results')
        (HERE/f'{mode}.stdout.json').write_text(result.stdout)
        receipts.append({'mode':mode,'kind':'positive','returncode':result.returncode,
                         'sha256_stdout':sha256(result.stdout.encode()).hexdigest()})
    for mutation in ('collapse_lifts','unit_coefficients','wrong_factorial','ignore_empty_grade'):
        for mode,prefix in (('normal',[]),('python_-O',['-O'])):
            result=run([*prefix,str(SCRIPT),'--mutate',mutation])
            require(result.returncode==1,f'{mode} {mutation} was not rejected')
            require(result.stderr.startswith('FAIL: '),f'{mutation} did not fail a semantic check')
            receipts.append({'mode':mode,'kind':'negative_mutation','mutation':mutation,
                             'returncode':result.returncode,'diagnostic':result.stderr.strip()})
    output={'status':'PASS','baseline_modes':3,'semantic_mutations':8,
            'uses_assert':False,'same_results_under_optimization':True,
            'verifier_sha256':sha256(SCRIPT.read_bytes()).hexdigest(),
            'runner_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'receipts':receipts}
    (HERE/'guard_results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))


if __name__=='__main__':
    main()
