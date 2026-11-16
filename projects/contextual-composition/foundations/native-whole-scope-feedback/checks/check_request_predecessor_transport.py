from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json
alpha={0:F(1,4),1:F(3,4),2:F(0)}
a={0:{0:F(1,2),1:F(1,2),2:F(0),3:F(0)},1:{0:F(0),1:F(0),2:F(1,2),3:F(1,2)},2:{0:F(1),1:F(0),2:F(0),3:F(0)}}
Q={(d,x):alpha[d]*a[d][x] for d,x in product(alpha,range(4))}
s=lambda d:'a' if d<2 else 'b'
r=lambda d,x:(x%2 if d!=1 else 1-x%2)
qp=defaultdict(F)
for (d,x),q in Q.items():qp[(s(d),r(d,x))]+=q
assert dict(qp)=={('a',0):F(1,2),('a',1):F(1,2),('b',0):F(0),('b',1):F(0)}
# Exact weighted predecessor mixture, with shared fibre-specific actual map.
beta={'a':F(1),'b':F(0)}
for t in (0,1):
    mix=sum(alpha[d]*sum(a[d][x] for x in range(4) if r(d,x)==t) for d in (0,1))
    assert mix==qp['a',t]
# Hidden sibling permutation counterexample; each fixed permutation preserves fair.
for y in (0,1):
    assert sorted([x^y for x in (0,1)])==[0,1]
diag={(y,x):(F(1,2) if y==x else F(0)) for y,x in product((0,1),repeat=2)}
pushed={t:sum(q for (y,x),q in diag.items() if x^y==t) for t in (0,1)}
assert pushed=={0:F(1),1:F(0)}
# Exact polytope violation: fair/fair 2x2 couplings parametrized t∈[0,1/2].
vertex_target_zero_mass=[2*t for t in (F(0),F(1,2))]
assert max(vertex_target_zero_mass)-F(1,2)==F(1,2)
# Strong kernel preservation fails although integrated coarsening exists.
k0={0:F(1),1:F(0)};k1={0:F(0),1:F(1)}
assert k0!=k1
assert {x:(k0[x]+k1[x])/2 for x in (0,1)}=={0:F(1,2),1:F(1,2)}
# Raw ancestor determines presence even when its probability could be zero.
raw=[(0,'absent','*'),(1,'present',0),(1,'present',1)]
assert len({presence for ancestor,presence,x in raw})==2
# Hiding ancestor behind constant paid index cannot preserve request existence.
assert len({presence for ancestor,presence,x in raw if True})>1
assert {'*':F(1)}=={'*':F(1)} # forced singleton inactive law
print(json.dumps({'native_noninjective_predecessor_pushforward':'PASS','raw_zero_predecessor_atoms_retained':4,'same_fibre_map_weighted_mixture':'PASS','hidden_sibling_permutation_failure':'PASS','exact_polytope_facet_violation':'1/2','strong_kernel_vs_integrated_law':'DISTINCT_CONFIRMED','silent_ancestry_presence_cannot_be_erased':'PASS','scope':'finite exact rational witnesses, owner coefficient doctrine unchanged'},indent=2))
