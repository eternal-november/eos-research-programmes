from fractions import Fraction as Q
from itertools import product
import json
raw=list(product(range(2),repeat=2))
ind={z:Q(1,4) for z in raw}; diagonal={z:Q(int(z[0]==z[1]),2) for z in raw}
for law in [ind,diagonal]:
 assert sum(law.values())==1
 for i in [0,1]:
  assert all(sum(p for z,p in law.items() if z[i]==v)==Q(1,2) for v in [0,1])
assert set(ind)==set(diagonal) and sum(p==0 for p in diagonal.values())==2
assert diagonal != ind
for y in [0,1]:
 m=sum(p for (a,b),p in diagonal.items() if a==y)
 conditional=[diagonal[(y,z)]/m for z in [0,1]]
 assert conditional != [Q(1,2),Q(1,2)]
# Finite augmented vector spaces, surjective augmentations: dim(K x_I L)=dimK+dimL-1.
payX=payY=seed=2
scope_then_seed=(payX+payY-1)*seed
owner_then_scope=payX*seed+payY-1
assert (scope_then_seed,owner_then_scope)==(6,5)
print(json.dumps({'full_raw_atoms':len(raw),'diagonal_zero_atoms':2,'fair_coordinate_marginals':True,'diagonal_excluded_by_fresh_fair_kernel_given_Y':True,'coefficient_dimensions':[scope_then_seed,owner_then_scope],'scope':'Exact boundary diagnostics only; not a proof of family-valued response coherence.'},indent=2))
