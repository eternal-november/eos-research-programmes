from fractions import Fraction as F
from itertools import product
import json

def laws(n,d=3):
    return [tuple(F(a,d) for a in v) for v in product(range(d+1),repeat=n) if sum(v)==d]
def push(p,r,m):
    return tuple(sum((p[i] for i in range(len(p)) if r[i]==j),F(0)) for j in range(m))
checks=0
for n,m in product(range(1,4),repeat=2):
    for p,q in product(laws(n),laws(m)):
        for r,s in product(product(range(2),repeat=n),product(range(2),repeat=m)):
            target={(a,b):F(0) for a,b in product(range(2),repeat=2)}
            for i,j in product(range(n),range(m)):
                target[r[i],s[j]]+=p[i]*q[j]
            pp,qq=push(p,r,2),push(q,s,2)
            assert all(target[a,b]==pp[a]*qq[b] for a,b in target)
            checks+=1
assert min(F(3,5),F(1,2)) != min(F(3,10),F(1,2))*2
# Same marginal laws, independent first-coordinate swap destroys diagonal.
diag={(0,0):F(1,2),(1,1):F(1,2)}
flipped={(1-a,b):v for (a,b),v in diag.items()}
assert flipped!=diag
# Zero raw elements remain in full product, not its positive support.
p=(F(1),F(0)); q=(F(1,2),F(1,2),F(0))
full={(i,j):p[i]*q[j] for i,j in product(range(2),range(3))}
assert len(full)==6 and sum(v>0 for v in full.values())==2
result={'status':'passed','product_naturality_cases':checks,'additional_cases':['three-atom-min-selector-obstruction','independent-map-diagonal-obstruction','retained-zero-raw-tuples'],'scope':'bounded exact rational diagnostics, not proof of universal uniqueness'}
print(json.dumps(result,indent=2))
