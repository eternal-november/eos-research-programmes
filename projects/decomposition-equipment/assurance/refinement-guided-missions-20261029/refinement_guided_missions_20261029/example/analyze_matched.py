"""Read-only matched comparison; missing service is never counted as efficiency."""
import json, sys
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parent
x=json.loads((P/(sys.argv[1] if len(sys.argv)>1 else 'final_results.json')).read_text());R=x['results'];out={}
key=lambda r:tuple(r[k] for k in ('n','L','s','seed','regime'))
for other in ('dense_column','cached_column','cached_rehearsal','oracle'):
 counts=Counter();pairs=[];prefixes=[]
 for a in R:
  if a['method']!='local_column':continue
  b=next(r for r in R if r['method']==other and key(r)==key(a))
  cum_a=cum_b=0;mask_a=[];mask_b=[]
  for aa,bb in zip(a['batches'],b['batches']):
   ca,cb=aa['completed'],bb['completed'];counts[f'{int(ca)}{int(cb)}']+=1
   cum_a+=aa['elapsed_ticks'];cum_b+=bb['elapsed_ticks'];mask_a.append(ca);mask_b.append(cb)
   prefixes.append(dict(key=key(a),through_batch=aa['index'],same_completion_mask=mask_a==mask_b,local_completed=sum(mask_a),other_completed=sum(mask_b),local_ticks=cum_a,other_ticks=cum_b))
   if ca and cb:pairs.append(dict(key=key(a),batch=aa['index'],local_ticks=aa['elapsed_ticks'],other_ticks=bb['elapsed_ticks']))
 out[other]={'joint_completion_counts_local_other':dict(counts),'joint_completed_batch_costs':pairs,'prefixes':prefixes}
by=[]
for method in dict.fromkeys(r['method'] for r in R):
 for n in (6,10,14):
  for regime in ('roomy','tight'):
   rr=[r for r in R if r['method']==method and r['n']==n and r['regime']==regime]
   bb=[b for r in rr for b in r['batches']]
   by.append(dict(method=method,n=n,regime=regime,completed=sum(b['completed'] for b in bb),offered=len(bb),first_completed=sum(r['batches'][0]['completed'] for r in rr),later_completed=sum(b['completed'] for r in rr for b in r['batches'][1:]),statuses=dict(Counter(b['status'] for b in bb))))
(P/'matched_analysis.json').write_text(json.dumps({'comparisons':out,'by_dimension_regime':by},indent=2))
for name,v in out.items():print(name,v['joint_completion_counts_local_other'])
