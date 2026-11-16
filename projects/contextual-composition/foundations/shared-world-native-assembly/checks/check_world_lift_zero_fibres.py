from fractions import Fraction as F
from itertools import product
import json

def push(mu,r):
 d={y:F(0) for y in r.values()}
 for x,p in mu.items(): d[r[x]]+=p
 return d

def lift(q, mus, targets, maps):
 ans={}
 for z in product(*(m.keys() for m in mus)):
  y=tuple(r[x] for r,x in zip(maps,z))
  ds=[m[t] for m,t in zip(targets,y)]
  v=q.get(y,F(0))
  if any(d==0 for d in ds): v=F(0)
  else:
   for m,x,d in zip(mus,z,ds): v*=m[x]/d
  ans[z]=v
 return ans
# Zero intermediate and final marginal coordinates, noninjective fibres,
# and retained unmatched zero raw tuples. Enumerate rational 2x2 couplings.
mu={0:F(1,4),1:F(1,4),2:F(1,2),3:F(0),4:F(0)}
r={0:0,1:0,2:1,3:2,4:2}; s={0:0,1:1,2:2}
mid=push(mu,r); final=push(mid,s); sr={x:s[r[x]] for x in mu}
count=0
for t in (F(0),F(1,8),F(1,4),F(3,8),F(1,2)):
 q={(a,b):F(0) for a,b in product(final,repeat=2)}
 q.update({(0,0):t,(1,1):t,(0,1):F(1,2)-t,(1,0):F(1,2)-t})
 qm=lift(q,[mid]*2,[final]*2,[s]*2)
 qs=lift(qm,[mu]*2,[mid]*2,[r]*2)
 direct=lift(q,[mu]*2,[final]*2,[sr]*2)
 assert qs==direct
 for i in range(2):
  for x,p in mu.items(): assert sum(v for z,v in qs.items() if z[i]==x)==p
 for y,p in q.items(): assert sum(v for z,v in qs.items() if tuple(sr[x] for x in z)==y)==p
 assert lift(qs,[mu]*2,[mu]*2,[dict((x,x) for x in mu)]*2)==qs
 count+=1
# Writer horizon restriction: lower-length stopped word is not shortened.
for n in range(5):
 for m in range(n+2):
  word=tuple(range(m)); trunc=word[:-1] if m==n+1 else word
  assert len(trunc)==min(m,n)
  if m<=n: assert trunc==word
print(json.dumps({'status':'passed','rational_couplings':count,'zero_denominators':'explicit intermediate and target zeros','checks':['identity on full zero-containing carriers','two-stage composition','both marginals','exact pushforward','writer horizon deletion']},indent=2))
