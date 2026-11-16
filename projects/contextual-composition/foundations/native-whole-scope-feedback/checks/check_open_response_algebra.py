from itertools import product
from fractions import Fraction as F
import json
cases=0
for r in range(3):
  for ns in product(range(1,4),repeat=r):
    for cs in product(range(3),repeat=r):
      for m in range(3):
        n=1+sum(ns);c=m+sum(cs)
        for root_active in (0,1):
          for ks in product(*[range(nj+1) for nj in ns]):
            k=root_active+sum(ks)
            if not k:continue
            assert k<=n
            for bits in product((0,1),repeat=k):
              rootbit=bits[0] if root_active else 0
              start=root_active
              childbits=[]
              for kj in ks:
                childbits.append(bits[start:start+kj]);start+=kj
              for g in (0,1):
                # All OLD actors consume broadcast; newborn seeds have memory zero.
                child_posts=[(nj+sum(bs),cj+nj*g) for nj,cj,bs in zip(ns,cs,childbits)]
                if rootbit: child_posts.append((1,0))
                assembled=(1+sum(x for x,y in child_posts),m+g+sum(y for x,y in child_posts))
                opaque=(n+sum(bits),c+n*g)
                assert assembled==opaque
                assert sum(bits)%2==(sum(childbit for bs in childbits for childbit in bs)+rootbit)%2
                cases+=1
# Closed posts can differ with g: demonstrates why no generic erase-g functor was claimed.
assert (2,3+2*0)!=(2,3+2*1)
# Passive signal-word action.
for n,c in product(range(1,4),range(4)):
  for a,b in product((0,1),repeat=2):
    assert (c+n*a)+n*b==c+n*(a+b)
print(json.dumps({'opaque_birth_memory_algebra':'PASS','successor_cases':cases,'parity_protocol_square':'PASS','passive_word_action':'PASS','erase_g_not_single_post':'PASS','scope':'finite integer exhaustive diagnostics, unit coefficients; proof remains written'},indent=2))
