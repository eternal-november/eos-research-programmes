#!/usr/bin/env python3
"""Reproduce exact harder-test regression outputs; no external dependencies."""
from pathlib import Path
import ast
import hashlib
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
CASES=(('check_open_higher_order.py','open_higher_order_results.txt'),
       ('check_nonthin_categorical.py','nonthin_categorical_results.json'))

def main():
    records=[]
    for script_name,output_name in CASES:
        script=ROOT/'checks'/script_name
        expected=(ROOT/'expected'/output_name).read_bytes()
        if any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(script.read_text()))):
            raise RuntimeError('Removable assertion in '+script_name)
        for flags in ([],['-O']):
            result=subprocess.run([sys.executable,*flags,str(script)],capture_output=True)
            if result.returncode:
                raise RuntimeError(script_name+' failed: '+result.stderr.decode())
            if result.stdout!=expected:
                raise RuntimeError(script_name+' output mismatch under '+str(flags))
        records.append({'script':script_name,'normal_and_optimized_match_expected':True,
                        'script_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),
                        'output_sha256':hashlib.sha256(expected).hexdigest()})
    print(json.dumps({'status':'PASS','python':sys.version.split()[0],
                      'scope':'Regression evidence supporting written structural proofs, not an exhaustive all-family or all-client test',
                      'checks':records},indent=2))

if __name__=='__main__': main()
