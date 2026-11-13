#!/usr/bin/env python3
"""Run the archived checks in a disposable copy; never overwrite evidence."""
from pathlib import Path
import argparse, hashlib, json, os, platform, shutil, subprocess, sys, tempfile, time
ROOT=Path(__file__).resolve().parent
TIMING_KEYS={'seconds','elapsed_seconds','growing_engine_smoke_seconds'}
def normalized(x):
    if isinstance(x,dict):return {k:normalized(v) for k,v in x.items() if k not in TIMING_KEYS}
    if isinstance(x,list):return [normalized(v) for v in x]
    return x

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',default='reproduction_outcomes.json')
    args=parser.parse_args()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for name,record in manifest['files'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==record['sha256'],name
    steps=[
      ['theory/check_relational_discovery.py'],
      ['theory/check_selective_completion.py'],
      ['review/independent_theory_tests.py'],
      ['example/test_relational_engine.py'],
      ['example/reproduce_engine_smoke.py'],
      # Its frozen config hashes the retained root record, including timing metadata.
      ['example/sequential_mission_cost_diagnostic.py'],
      ['example/run_constructed_missions.py'],
      ['example/partial_acquisition_probe.py'],
      ['example/partial_acquisition_reference_check.py'],
      ['example/sequential_mission_compiler_v1.py'],
      ['example/sequential_mission_compiler.py','--config','sequential_mission_corrected_config.json','--output-prefix','sequential_mission_corrected'],
      ['example/sequential_mission_negative_check.py'],
      ['review/independent_execution_check.py'],
      ['review/independent_sequential_check.py','example/sequential_mission_results.json'],
      ['review/independent_sequential_check.py','example/sequential_mission_corrected_results.json'],
      ['review/independent_frontier_check.py'],
    ]
    result={'python':platform.python_version(),'numpy':__import__('numpy').__version__,
      'manifest_verified':True,'timing_keys_ignored_for_semantic_comparison':sorted(TIMING_KEYS),
      'source_path_adapters':None,'steps':[]}
    with tempfile.TemporaryDirectory(prefix='safe-mission-portable-') as tmp:
        work=Path(tmp)/'source';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc','.venv'))
        before={p.relative_to(work).as_posix():json.loads(p.read_text()) for p in work.rglob('*.json') if p.name!='MANIFEST.json'}
        environment=os.environ.copy();environment['PYTHONDONTWRITEBYTECODE']='1';environment.pop('PYTHONPATH',None)
        for cmd in steps:
            start=time.perf_counter()
            proc=subprocess.run([sys.executable,*cmd],cwd=work,env=environment,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            result['steps'].append({'command':'python '+ ' '.join(cmd),'exit_code':proc.returncode,'elapsed_seconds':time.perf_counter()-start,'output':proc.stdout})
            print(result['steps'][-1]['command'], 'PASS' if proc.returncode==0 else 'FAIL',flush=True)
            if proc.returncode:break
        comparisons=[]
        for p in sorted(work.rglob('*.json')):
            name=p.relative_to(work).as_posix()
            if name not in before:continue
            after=json.loads(p.read_text())
            if p.read_bytes()!=(ROOT/name).read_bytes():
                old=before[name]
                hash_verifications=[]
                hash_inputs={}
                if name.startswith('review/independent_sequential_') and 'input' in after:
                    hash_inputs={'sha256':after['input']}
                if name=='review/independent_frontier_results.json':
                    hash_inputs={'cost_result_sha256':'sequential_mission_cost_diagnostic_results.json',
                                 'corrected_roots_sha256':'sequential_mission_corrected_results.json'}
                for field,input_name in hash_inputs.items():
                    inp=Path('example')/input_name
                    verified=(after[field]==hashlib.sha256((work/inp).read_bytes()).hexdigest()
                        and old[field]==hashlib.sha256((ROOT/inp).read_bytes()).hexdigest()
                        and normalized(json.loads((work/inp).read_text()))==normalized(json.loads((ROOT/inp).read_text())))
                    hash_verifications.append({'field':field,'input':str(inp),'verified':verified})
                    if verified:after=dict(after,**{field:old[field]})
                comparisons.append({'file':name,'semantic_match':normalized(after)==normalized(old),
                    'raw_input_hash_checks':hash_verifications})
        result['changed_json_comparisons']=comparisons
        result['all_steps_passed']=len(result['steps'])==len(steps) and all(s['exit_code']==0 for s in result['steps'])
        result['all_changed_json_semantically_match']=all(c['semantic_match'] for c in comparisons)
        for name in ['example/sequential_mission_corrected_summary.json','example/sequential_mission_negative_results.json','example/safe_abstention_results.json','example/sequential_mission_cost_diagnostic_summary.json']:
            if (work/name).exists():result.setdefault('key_outcomes',{})[name]=json.loads((work/name).read_text())
    Path(args.output).resolve().write_text(json.dumps(result,indent=2)+'\n')
    assert result['all_steps_passed'] and result['all_changed_json_semantically_match'], 'See reproduction outcomes for failures or differences'

if __name__=='__main__':main()
