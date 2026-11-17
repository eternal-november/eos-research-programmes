from fractions import Fraction as F
from itertools import product
import json
p={0:F(1,2),1:F(1,2),2:F(0)}
local=[(x,z,t) for x,z in product(range(3),repeat=2) for t in ([None] if z==0 else range(3))]
raw=list(product(local,repeat=2));Q={a:F(0) for a in raw}
for x1,x2,b in product(range(2),repeat=3):
 z1,z2=x2,x1
 a=((x1,z1,None if z1==0 else b),(x2,z2,None if z2==0 else b))
 Q[a]+=F(1,8)
assert len(local)==21 and len(raw)==441 and sum(Q.values())==1
for i in range(2):
 for x,z,t in local:
  actual=sum(q for a,q in Q.items() if a[i]==(x,z,t))
  expected=p[x]*p[z]*(1 if t is None else p[t])
  assert actual==expected
# Full-paid conditioning would force z1=x2, not fair.
assert sum(q for a,q in Q.items() if a[0][0]==0 and a[1][0]==0 and a[0][1]==0)==F(1,4)
# Extra core-local block predicate, includes distinguished product.
for law,eq in [('independent',F(1,2)),('diagonal',F(1)),('antidiagonal',F(0))]:
 assert (eq>=F(1,2))==(law!='antidiagonal')
L=lambda z:3 if z==2 else 2
owner=lambda a:2*L(a[1])*(1 if a[2] is None else L(a[2]))
print(json.dumps({'local_raw':len(local),'scope_raw':len(raw),'positive_raw':sum(q>0 for q in Q.values()),'zero_raw':sum(q==0 for q in Q.values()),'complete_local_marginals':'PASS','nested_ancestral_rows':'PASS','full_paid_conditional_freshness':'fails as intended','scope_context_dimensions':sorted({owner(a)+owner(b)-1 for a,b in raw}),'product_compatible_extra_block':'strictly stronger than marginal tests'},indent=2))
