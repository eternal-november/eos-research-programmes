#!/usr/bin/env python3
"""Reproduce deterministic outcomes in fresh subprocesses, then check proofs."""
import json,pathlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
py=sys.executable
subprocess.run([py,'-m','unittest','test_kernel','-v'],cwd=P,check=True)
for budget in [100000,1000000,10000000]:
 subprocess.run([py,'experiment.py','--method','all','--budget',str(budget)],cwd=P,check=True,stdout=subprocess.DEVNULL)
for seed in [11,23,47]:
 subprocess.run([py,'experiment.py','--method','random','--seed',str(seed),'--budget','10000000'],cwd=P,check=True,stdout=subprocess.DEVNULL)
expected={'definitions':(3871,0),'training_cache':(744632,0),'generic':(749756,3),'guided':(770369,3),'full_completion':(763527,8),'guided_full_completion':(782685,8),'cold':(9695041,8),'oracle':(6643,8)}
for r in json.loads((P/'results'/'summary_all_10000000.json').read_text()):
 assert (r['cost']['total'],r['compositional_transfer_solved'])==expected[r['method']],r['method']
subprocess.run([py,'audit_results.py'],cwd=P,check=True)
print('PASS: deterministic counts, fixed workload, and all saved proof bundles reproduced.')
