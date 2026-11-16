from fractions import Fraction as F
from itertools import product
sets=[set(),{0},{1},{0,1}];n=0
for r,s in product(list(product(range(2),repeat=2)),repeat=2):
 for T,U,V in product(sets,repeat=3):
  if {i for i in range(2) if r[i] in U}<=T and {j for j in range(2) if s[j] in V}<=U:
   assert {i for i in range(2) if s[r[i]] in V}<=T;n+=1
rows=[{('terminal',):F(1,3),('active',):F(2,3),('zero-terminal',):F(0)}]
def term(h):return h[0]!='active' or h[-1]=='stop'
layers=[{h:p for h,p in rows[0].items() if term(h)}]
for k in range(4):
 nxt={};new={}
 for h,p in rows[-1].items():
  if term(h):nxt[h]=p
  else:
   for x in ('stop','continue'):
    nxt[h+(x,)]=p/2
    if x=='stop':new[h+(x,)]=p/2
 rows.append(nxt);layers.append(new)
 assert sum(nxt.values())==1
 assert sum(sum(l.values()) for l in layers)==sum(p for h,p in nxt.items() if term(h))
assert ('zero-terminal',) in layers[0] and sum(layers[0].values())==F(1,3)
print('PASS',n,'partial-domain composites; nonempty and zero T0 absorption')
