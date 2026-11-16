from fractions import Fraction as F
from functools import lru_cache
import json
@lru_cache(None)
def trees(n):
 if n==1:return (None,)
 return tuple((l,r) for k in range(1,n) for l in trees(k) for r in trees(n-k))
def nodes(t):return 1 if t is None else 1+nodes(t[0])+nodes(t[1])
def shared(t):
 frontier=[t];p=F(1)
 while frontier:
  choices=[x is not None for x in frontier]
  p*=F(1,2) if all(x==choices[0] for x in choices) else F(0)
  frontier=[c for x in frontier if x is not None for c in x]
 return p
rows={}
for n in range(1,5):
 ts=trees(n);ind=sum(F(1,2)**nodes(t) for t in ts);shr=sum(shared(t) for t in ts)
 rows[n]={'raw_trees':len(ts),'independent_mass':str(ind),'shared_mass':str(shr),'shared_raw_zeros':sum(shared(t)==0 for t in ts)}
assert rows[3]['independent_mass']=='1/16' and rows[3]['shared_mass']=='0'
assert rows[4]['shared_mass']=='1/8'
print(json.dumps({'status':'passed','leaf_count_layers':rows,'scope':'fixed-primitive independent/shared separation, not arbitrary nondefinability'},indent=2))
