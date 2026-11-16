from itertools import product
from random import Random
rng=Random(20261116)
checks=0
for n in range(1,6):
 for repeat in range(100):
  # Profiles carry all boundary bits. Private witness multiplicities differ.
  A=[list(range(rng.randint(1,3))) for _ in range(n)]
  Ws=[[(p,k) for p in a for k in range(rng.randint(1,3))] for a in A]
  Wt=[[(p,k) for p in a for k in range(rng.randint(1,3))] for a in A]
  allD=list(product(*A))
  # Arbitrary global profile constraints, including non-tree relations.
  D={d for d in allD if rng.randrange(3)}
  def observed(d): return (sum(d)%2, frozenset(i for i,x in enumerate(d) if x%2))
  goal={observed(d) for d in D}
  for W in (Ws,Wt):
   got={observed(tuple(w[0] for w in z)) for z in product(*W) if tuple(w[0] for w in z) in D}
   assert got==goal
   checks+=1
# Failure: identical local images, different hidden joint admission.
Dsource={(0,0),(1,1)}; Dtarget=set(product((0,1),repeat=2))
assert not any(x!=y for x,y in Dsource)
assert any(x!=y for x,y in Dtarget)
# Local observer square: source parity, target complete observed bit history.
for bits in product((0,1),repeat=8):
 m=0; mt=()
 for b in bits:
  m^=b; mt+= (b,)
  assert m==sum(mt)%2
  checks+=1
print(f'{checks} exact finite checks passed; not a proof-assistant certification.')
