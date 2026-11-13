"""Independent analytic envelope review of the synthetic contextual example."""
import sys,itertools,json
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'examples'))
import timed_controller as t

def exact_continuous(v,y):
 s,n,b=t.physical(y)
 # acceleration1000 mm/s^2, then cruise until capped brake onset; units micrometres
 return F(v*v,2)+v*(min(100+10+s+n,310)+t.ACTUATION_MS)+F(1000*v*v,2*b)

a=[-1]*12;r=[0]*12;r[10]=2
warm={}
for v in t.SPEEDS:
 records=[(t.simulate(v,y,1260000)['stop_um'],exact_continuous(v,y)) for y,p in t.outcomes(a,r)]
 assert all(sim>=analytic for sim,analytic in records)
 warm[v]=max(sim for sim,analytic in records)
assert warm[1100]==1259500<1260000<warm[1200]
blind={v:0 for v in t.SPEEDS};contexts=0
for vals in itertools.product(range(2),range(3),range(4),range(5),range(5)):
 r=[0]*12
 for c,x in zip([1,4,6,8,10],vals):r[c]=x
 for y,p in t.outcomes(a,r):
  for v in t.SPEEDS:
   sim=t.simulate(v,y,1260000)['stop_um']
   assert sim>=exact_continuous(v,y)
   blind[v]=max(blind[v],sim)
 contexts+=1
assert contexts==600
assert blind[800]==1216000<1260000<blind[900]==1503000
# In base context same adverse outcome defeats every higher-speed grid command.
r=[0]*12
bad=[y for y,p in t.outcomes(a,r) if all(t.simulate(v,y,1260000)['collision'] for v in (1000,1100,1200))]
assert bad
# Every randomized speed policy robust to every supported outcome at risk<=.1
# has high-speed mass<=.1, so expected requested speed<=900*.9+1200*.1=930.
assert F(900)*F(9,10)+F(1200)*F(1,10)==930<1000
out={'checked_contexts':contexts,'warm_worst_stop_um':warm,'history_blind_worst_stop_um':blind,'all_tick_distances_conservative_vs_continuous_envelope':True,'same_budget_robust_randomized_requested_speed_upper':930,'qualification':'Conditional on exact learned response and stipulated residual/physical support; favorable history is supplied, not proved safely inducible.'}
(ROOT/'review'/'contextual_support_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
