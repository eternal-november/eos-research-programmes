"""Secondary timing study, declared as exploratory amendment v3."""
import json,statistics
from pathlib import Path
from experiment import run_method,summarize
p=Path(__file__).parent/'results'
methods=['generic','guided','full_completion','guided_full_completion']
runs=[]
for repetition in range(5):
 for method in methods:
  r=run_method(method,10**7);s=summarize(r);s['repetition']=repetition;runs.append(s)
(p/'timing_repeated.json').write_text(json.dumps(runs,indent=2)+'\n')
caps=[]
for limit in [0.05,0.25,0.5]:
 for repetition in range(3):
  for method in methods:
   r=run_method(method,10**9,cpu_limit=limit);s=summarize(r);s['repetition']=repetition;caps.append(s)
(p/'timing_capped.json').write_text(json.dumps(caps,indent=2)+'\n')
for method in methods:
 rs=[r for r in runs if r['method']==method]
 print(method,'cpu median',statistics.median(r['cpu_seconds'] for r in rs),'wall median',statistics.median(r['elapsed_seconds'] for r in rs),'score',rs[0]['compositional_transfer_solved'],'proxy',rs[0]['cost']['total'])
