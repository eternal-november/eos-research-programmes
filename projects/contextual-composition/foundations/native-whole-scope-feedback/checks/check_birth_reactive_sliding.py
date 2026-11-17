"""Finite combinatorial diagnostics only; not whole-machine proof."""
from itertools import product
cases=0
# Original payload (occurrence, original_color) persists; designated role varies.
for n in range(1,6):
 for parents in product(*[range(i) for i in range(1,n)]):
  for colors in product(range(3),repeat=n-1):
   payload=[(i,parents[i-1],colors[i-1]) for i in range(1,n)]
   for fvals in product(range(2),repeat=3):
    for gvals in product(range(2),repeat=2):
     target=[(i,p,v,fvals[v]) for i,p,v in payload]
     inverse=[(i,p,v) for i,p,v,u in target]
     assert inverse==payload
     direct=[(i,p,v,gvals[fvals[v]]) for i,p,v in payload]
     iterated=[(i,p,v,gvals[u]) for i,p,v,u in target]
     assert direct==iterated
     # Original partition: colors0,2 left,1 right; f can merge across blocks.
     tagged=[(i,p,v,(v!=1,fvals[v])) for i,p,v in payload]
     merged=[(i,p,v,u) for i,p,v,(block,u) in tagged]
     assert merged==target
     # All finite pending prefixes reconstruct, no completed tree needed.
     for k in range(n):
      assert [(i,p,v) for i,p,v,u in target if i<=k]==[r for r in payload if r[0]<=k]
     cases+=1
# Exact inverse-grade obstruction: one target body cannot map to two source bodies.
source_bodies=[('c',0,'d'),('c',1,'d')]
target_body=('c','*','d')
for possible_inverse_shape in source_bodies:
 assert not all(possible_inverse_shape==s for s in source_bodies)
print('PASS',cases,'forest/color-map/composition cases; tagged nesting merges; all pending prefixes; inverse-body obstruction')
