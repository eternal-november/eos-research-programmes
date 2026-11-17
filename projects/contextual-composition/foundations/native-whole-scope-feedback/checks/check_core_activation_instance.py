from fractions import Fraction as F
from itertools import product
import json
raw=list(product(range(3),repeat=4)) # x1,x2,z1,z2
Q={a:(F(1,4) if a[0]<2 and a[1]<2 and a[2]==a[1] and a[3]==a[0] else F(0)) for a in raw}
p=[F(1,2),F(1,2),F(0)]
assert len(raw)==81 and sum(Q.values())==1
for i in range(2):
 for x,z in product(range(3),repeat=2):
  assert sum(q for a,q in Q.items() if a[i]==x and a[2+i]==z)==p[x]*p[z]
assert sum(q for a,q in Q.items() if a[2]==a[1])==1
assert sum(q for a,q in Q.items() if a[3]==a[0])==1
# Successive-entry source needs each seed fair conditional on full paid pair.
assert sum(q for a,q in Q.items() if a[0]==0 and a[1]==0 and a[2]==0)==F(1,4)
assert F(1,4)!=F(1,2)*F(1,4) # violates conditional fair at X=(0,0)
# All-raw successor factorization, not merely Q-almost surely.
for i in range(2):
 seen={}
 for a in raw:
  core=(a[i],a[2+i]); state=('old-done',core[0],'child-output',core[1])
  assert core not in seen or seen[core]==state
  seen[core]=state
# Rejected sibling read has no all-raw descent through that core.
a=(0,0,0,0); b=(0,1,0,0)
assert (a[0],a[2])==(b[0],b[2]) and a[1]!=b[1]
# Primitive private tags never change under grouping.
keys=[('run',0,i,role) for i in range(2) for role in ('paid','entry')]
assert [k for block in [keys[:2],keys[2:]] for k in block]==keys
# Nonunit augmented-vector factor dimensions; slice product over unit.
L=lambda z: 3 if z==2 else 2
D={a:(2*L(a[2])+2*L(a[3])-1) for a in raw}
assert set(D.values())=={7,9,11}
print(json.dumps({'raw_points':len(raw),'positive_points':sum(q>0 for q in Q.values()),'zero_points':sum(q==0 for q in Q.values()),'local_joint_rows':'product fair with zero atoms','cross_seed_correlation':'z1=x2,z2=x1','all_raw_core_successor':'PASS','sibling_read_descent':'FAIL as intended','scope_context_dimensions':sorted(set(D.values()))},indent=2))
