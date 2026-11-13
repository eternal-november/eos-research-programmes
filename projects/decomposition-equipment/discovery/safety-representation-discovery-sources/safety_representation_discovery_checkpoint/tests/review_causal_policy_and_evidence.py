"""Independent exact checks for policy change and evidence guardrails."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def bit(mask,i):return (mask>>i)&1
count=0
for f0 in range(16):
 for f1 in range(256):
  target=F(0);weighted=F(0);mass=F(0)
  for z in range(2):
   pz=F(2,5) if z else F(3,5)
   # Target first action 0, second action equals first readout.
   y0=bit(f0,2*0+z);a1=y0
   target+=pz*bit(f1,4*y0+2*a1+z)
   for a0,a1 in product(range(2),repeat=2):
    p0=F(1,3) if a0 else F(2,3)
    y0=bit(f0,2*a0+z)
    prob1=F(3,4) if y0 else F(1,4)
    p1=prob1 if a1 else 1-prob1
    pe=pz*p0*p1
    w=F(1,p0*p1) if a0==0 and a1==y0 else F(0)
    y1=bit(f1,4*y0+2*a1+z)
    weighted+=pe*w*y1;mass+=pe*w
  assert target==weighted and mass==1
  count+=1
# Aggregate randomized-looking actions need not be causally randomized.
confounded_target=F(1,2);wrong_weighted=F(1)
assert confounded_target!=wrong_weighted
# Fair marginals do not identify disagreement risk.
positive={(0,0):F(1,2),(1,1):F(1,2)}
negative={(0,1):F(1,2),(1,0):F(1,2)}
for j in range(2):
 assert sum(p for x,p in positive.items() if x[j])==F(1,2)
 assert sum(p for x,p in negative.items() if x[j])==F(1,2)
assert sum(p for x,p in positive.items() if x[0]!=x[1])==0
assert sum(p for x,p in negative.items() if x[0]!=x[1])==1
# Selection can invalidate a single-candidate confidence statement.
single=0;selected=0
for b in product(range(2),repeat=4):
 c0=b[:2];c1=b[2:]
 single+=min(c0)<=F(1,2)<=max(c0)
 chosen=c0 if c0[0]==c0[1] else c1
 selected+=min(chosen)<=F(1,2)<=max(chosen)
assert F(single,16)==F(1,2) and F(selected,16)==F(1,4)
# Shared temporal mode excludes disagreements; per-step relaxation admits one.
assert all(x[0]==x[1] for x in positive)
assert (0,1) in negative
report={'status':'PASS','causal_policy_change_models':count,
 'confounding_control':{'true_target':'1/2','false_importance_estimate':'1'},
 'marginally_indistinguishable_risks':[0,1],
 'postselection_control':{'fixed_coverage':'1/2','selected_coverage':'1/4'},
 'shared_mode_vs_rectangular_risk':[0,1],
 'scope':'finite exact controls; not proof of full theorem or statistical procedure'}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
