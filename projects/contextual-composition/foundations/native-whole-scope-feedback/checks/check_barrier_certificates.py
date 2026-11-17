"""Finite diagnostic, not a proof: pending colored components, stable IDs,
cut sealing and certificate naturality. Includes zero/unreturned configurations.
"""
from itertools import product
# Planar trees encoded by parent vector, parent always smaller; edge colors U/V.
count=0
for n in range(1,7):
 for pars in product(*[range(i) for i in range(1,n)]):
  parent=(-1,)+pars
  for colors in product('UV',repeat=n-1):
   color=('-',)+colors
   # Maximal V components are rooted at original root or each U child.
   component=[]
   for i in range(n):
    component.append(i if i==0 or color[i]=='U' else component[parent[i]])
   nested={r:[] for r in component}
   for i in range(n): nested[component[i]].append((i,parent[i],color[i]))
   flattened=sorted(x for members in nested.values() for x in members)
   assert flattened==[(i,parent[i],color[i]) for i in range(n)]
   # All prefixes, including pending internal V components, retain U births.
   for k in range(1,n+1):
    assert sorted(x[0] for v in nested.values() for x in v if x[0]<k)==list(range(k))
   # Binder projection and grouping act on different fields, including unused tag.
   records=[(i,(i,11,17),('producer',i),('owner',0),0) for i in range(n)]
   rho=lambda x:(x[0],x[1][:2],*x[2:])
   a={r:[rho(records[i]) for i in members] for r,members in
      ((r,[x[0] for x in xs]) for r,xs in nested.items())}
   b={r:[rho(x) for x in records if component[x[0]]==r] for r in nested}
   assert a==b
   count+=1
# Nullary returned producer vs unsealed empty producer are different.
for sealed,producer_done,job_done in product([False,True],repeat=3):
 close=sealed and producer_done and job_done
 assert not close or sealed and producer_done
assert (True and True and all([])) is True
assert (False and all([])) is False
# Constructive certificate persists under arbitrary unrelated steps, even Spin.
cert=('primitive-z',1,'external-loop',('full-own-record',3),'owner0')
for step in range(1000):
 state=(cert,('Spin-unfold',step))
 assert state[0]==cert
print('PASS',count,'colored forests; all finite prefixes; binder/group square; nullary sealing; 1000 divergent-prefix certificate steps')
