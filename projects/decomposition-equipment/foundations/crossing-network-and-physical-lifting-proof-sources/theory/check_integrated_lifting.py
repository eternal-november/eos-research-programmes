"""Small exact bridge checks: bounded invisible sectors and physical record comparison."""
from itertools import permutations,product
import json
def partitions(n):
 def go(a):
  if len(a)==n:
   yield tuple(a)
   return
  for k in range(max(a,default=-1)+2):
   yield from go(a+[k])
 yield from go([])

# Two actual sensor modes, same source/observable output: NOT disposable decoration.
core=(('mode0',0),('mode1',0))
N=len(core)
fibres=((0,1),(2,3),(4,5)) # one ordinary chart, one chart with two interface lifts
Ks=[]
for K in partitions(6):
 classes=set(K)
 if all(len({K[x] for x in f})==len(f) and {K[x] for x in f}==classes for f in fibres):
  Ks.append(K)
assert len(Ks)==4
structural=set()
for K in Ks:
 for ordering in permutations(range(N)):
  structural.add(tuple(ordering[K[x]] for x in range(6)))
# Hardware-first: independently assign each exact local fibre to actual physical modes.
hardware=set()
for maps in product(tuple(permutations(range(N))), repeat=3):
 hardware.add(tuple(v for m in maps for v in m))
assert structural==hardware and len(hardware)==8
assert 4==2*N # duplicated interface doubles local records without increasing global records

def exact_wrapper(records,lifts):
 image=[(z,t) for z,t,hidden in records]
 target=set(product(lifts,range(N)))
 return len(image)==len(set(image)) and set(image)==target
# Invisible independent adapter call doubles every core record, hence fails exact restriction.
extra=[(0,t,h) for t in range(N) for h in range(2)]
assert not exact_wrapper(extra,(0,))
# If the real boundary lift records that choice, every demanded pair appears exactly once.
exposed=[(h,t,h) for t in range(N) for h in range(2)]
assert exact_wrapper(exposed,(0,1))
# Same visible output, different actual executions: output-only pruning changes the target.
one_mode={(0,0)}
two_modes={(0,0),(1,0)}
assert {out for _,out in one_mode}=={out for _,out in two_modes}
assert len(one_mode)!=len(two_modes)
print(json.dumps({'structural_first_identifications':len(structural),
 'hardware_first_identifications':len(hardware),'same_identifications':structural==hardware,
 'hidden_adapter_multiplicity_rejected':True,'exposed_boundary_lifts_accepted':True,
 'output_only_pruning_unsound':True},indent=2))
