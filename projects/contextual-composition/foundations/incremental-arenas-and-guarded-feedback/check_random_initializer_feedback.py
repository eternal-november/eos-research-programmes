from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import json
# Each seed carries its own formal coefficient-factor name, even at weight zero.
rows={0:[('a',F(1,2),()),('b',F(1,2),()),('ghost',F(0),())],
      1:[('leaf',F(1,3),()),('one',F(2,3),(0,)),('ghost2',F(0),(0,0))],
      2:[('leaf',F(1,2),()),('fork',F(1,2),(1,0)),('ghost2',F(0),(1,1))]}
def mul(xs):
 v=F(1)
 for x in xs:v*=x
 return v
@lru_cache(None)
def trees(x):
 out=[]
 for z,p,labels in rows[x]:
  for cs in product(*(trees(y) for y in labels)):
   out.append(((x,z,tuple(c[0] for c in cs)),p*mul(c[1] for c in cs)))
 return tuple(out)
def factors(t):return ((t[0],t[1]),)+sum((factors(c) for c in t[2]),())
def depth(t):return 1+max((depth(c) for c in t[2]),default=0)
for x in rows:assert sum(p for _,p in trees(x))==1
# Retain maximal U components as a nested structural encoding and reconstruct.
# Label1 is V; all other invocation labels are U. Every cut retains child order.
def nested(t):
 local=[];boundary=[]
 def scan(s,path):
  local.append((path,s[0],s[1],len(s[2])))
  for j,c in enumerate(s[2]):
   if c[0]==1:boundary.append((path+(j,),nested(c)))
   else:scan(c,path+(j,))
 scan(t,())
 return (tuple(local),tuple(boundary))
def unnest(n):
 local,boundary=n;D={p:(x,z,k) for p,x,z,k in local};B=dict(boundary)
 def build(p):
  if p in B:return unnest(B[p])
  x,z,k=D[p];return(x,z,tuple(build(p+(j,)) for j in range(k)))
 return build(())
for t,p in trees(2):
 assert unnest(nested(t))==t
 assert factors(unnest(nested(t)))==factors(t)
# A one-paid-event parent initializes label2. Its expanded row is normalized,
# keeps seed factors, and macro total paid cost remains one, not tree size.
parent=[('plain',F(1,2),None),('spawn',F(1,2),2),('zero_spawn',F(0),1)]
expanded=[]
for w,p,label in parent:
 if label is None:expanded.append((w,None,p))
 else:
  expanded.extend((w,t,p*q) for t,q in trees(label))
assert sum(p for _,_,p in expanded)==1
assert any(p==0 for _,_,p in expanded)
assert max(depth(t) for t,_ in trees(2))==3
# Zero-paid source initializer closure already includes nontrivial tensors.
assert max(len(factors(t)) for t,_ in trees(2))>1
print(json.dumps({'status':'passed','initializer_rows':{str(x):len(trees(x)) for x in rows},
 'raw_zero_trees_at_2':sum(p==0 for _,p in trees(2)),
 'expanded_event_row_atoms':len(expanded),'nesting_roundtrips':len(trees(2)),
 'checks':['all-raw-normalization','maximal-component-reconstruction','seed-factor-once','zero-cost-nonunit-factors','normalized-paid-birth-expansion']},indent=2))
