"""Independent exact checks of interface invalidation and negative transfer."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
seq=[-1,-1,1,-1,0,0,3,2,1,-1]
old=[[],[],[0],[]];new=[[],[],[0,3],[]]
traces=[]
for parents in (old,new):
 prev=[0]*4;obs=[]
 for a in seq:
  u=[2 if i==a else 0 for i in range(4)]
  x=[u[i]+sum(prev[j] for j in parents[i]) for i in range(4)]
  obs.append(x);prev=u
 traces.append(obs)
assert traces[0][:7]==traces[1][:7]
assert max(traces[0][7])<=3 and traces[1][7][2]==4
abstract={'good','bad'};concrete={'good'}
assert concrete<=abstract
assert not all(s=='good' for s in abstract)
assert all(s=='good' for s in concrete)
result={'status':'PASS','identical_records_through_slot':6,'old_slot7':traces[0][7],'enlarged_slot7':traces[1][7],'forward_refinement_negative_transfer_counterexample':True}
(ROOT/'review/programmable_interface_counterexamples.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
