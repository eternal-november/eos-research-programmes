"""Independent rational controls for risk certificates and acquisition scope."""
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
import json
B=list(product(range(2),repeat=3))
checks=0
for x in B:
 h=int(sum(x)>=2)
 rhs=x[0]*x[1]+x[0]*x[2]+x[1]*x[2]-2*x[0]*x[1]*x[2]
 assert h==rhs;checks+=1

def law(q):
 return {x: q if sum(x)==3 else F(1,100)-q if sum(x)==2 else F(2,25)+q if sum(x)==1 else F(73,100)-q for x in B}
for q in [F(0),F(7,1000),F(1,100)]:
 p=law(q);assert sum(p.values())==1 and min(p.values())>=0
 for j in range(3):assert sum(v*x[j] for x,v in p.items())==F(1,10);checks+=1
 for i,j in combinations(range(3),2):assert sum(v*x[i]*x[j] for x,v in p.items())==F(1,100);checks+=1
 assert sum(v for x,v in p.items() if sum(x)>=2)==F(3,100)-2*q;checks+=1
assert F(2,125)+5*F(1,2000)==F(37,2000)<F(1,50)
# Entire fixed-subset histories agree, but switching patches can reveal parity.
def pathlaw(parity,rho):
 C=[x for x in B if sum(x)%2==parity]
 return {(x,y):F(1,4)*((rho if x==y else 0)+(1-rho)*F(1,4)) for x in C for y in C}
def marginal(p,key):
 out={}
 for xy,v in p.items():out[key(xy)]=out.get(key(xy),0)+v
 return out
fixed=0
for rho in [F(0),F(1,2),F(3,4)]:
 p0,p1=pathlaw(0,rho),pathlaw(1,rho)
 for k in [1,2]:
  for S in combinations(range(3),k):
   key=lambda xy,S=S:tuple(tuple(x[j] for j in S) for x in xy)
   assert marginal(p0,key)==marginal(p1,key);fixed+=1
 switched=lambda xy:(xy[0][0],xy[0][1],xy[1][2])
 d0,d1=marginal(p0,switched),marginal(p1,switched)
 assert (d0==d1)==(rho==0)
 if rho==F(1,2):
  assert d0[(0,0,0)]==F(3,16) and d1[(0,0,0)]==F(1,16)
report={'status':'PASS','risk_identity_and_moment_cases':checks,
 'risk_band_certificate':'37/2000 < 1/50',
 'fixed_patch_history_comparisons':fixed,
 'switching_patch_scope_control':{'rho':'1/2','even_event_probability':'3/16','odd_event_probability':'1/16'},
 'fresh_coset_patch_control':'rho=0 gives equality for the tested switching pattern',
 'scope':'rational calibration; does not establish deployment assumptions'}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
