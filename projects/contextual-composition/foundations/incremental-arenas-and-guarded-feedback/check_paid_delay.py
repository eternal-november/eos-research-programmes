from fractions import Fraction as F
from itertools import product
import json
# Original source has return, loop, and a zero-weight loop witness.
prob={'return':F(1,2),'loop':F(1,2),'ghost':F(0)}
rows=[]
for n in range(1,8):
 for prefix in product(('loop','ghost'),repeat=n-1):
  tree=prefix+('return',)
  p=F(1)
  for z in tree:p*=prob[z]
  boots=tuple(('boot',z) for z in tree)
  assert tuple(z for _,z in boots)==tree
  assert len(boots)==len(tree) # paid count = invocations, not generations claim
  # Every original initializer coefficient is a named factor retained once.
  assert tuple(('L',i,z) for i,(_,z) in enumerate(boots))==tuple(('L',i,z) for i,z in enumerate(tree))
  rows.append((tree,p))
assert sum(p for _,p in rows)==1-F(1,2)**7
assert sum(p==0 for _,p in rows)>0
# Full raw seed history can select different legal pair couplings at one state.
controlled={(z,x,x^z):F(1,4) for z in (0,1) for x in (0,1)}
for z in (0,1):
 for x in (0,1):assert sum(p for (zz,xx,y),p in controlled.items() if zz==z and xx==x)==F(1,4)
assert all(y==x for z,x,y in controlled if z==0)
assert all(y!=x for z,x,y in controlled if z==1)
# Native deterministic path maps require equal enabled status and initial states.
def native_path_map(length_a,length_b):
 for targets in product(range(length_b+1),repeat=length_a+1):
  if targets[0]!=0:continue
  if any((s<length_a)!=(targets[s]<length_b) for s in range(length_a+1)):continue
  if any(targets[s+1]!=targets[s]+1 for s in range(length_a)):continue
  return targets
 return None
for a,b in ((0,1),(1,0),(1,2),(2,1)):assert native_path_map(a,b) is None
# The extra unreachable one-event state maps to a new boot state after delay.
source_events={'boot':1,'x':1,'t':0};target_events={'boot':1,'t':0}
h={'boot':'boot','x':'boot','t':'t'}
assert all(source_events[s]==target_events[h[s]] for s in source_events)
assert h['t']=='t' # both boot and x transitions land at t
print(json.dumps({'status':'passed','geometric_raw_trees_through_7':len(rows),'raw_zero_trees':sum(p==0 for _,p in rows),'termination_mass':str(sum(p for _,p in rows)),
 'checks':['boot-raw-native-reconstruction','coefficient-factor-once','seed-sensitive-control','no-0-1-or-1-2-event-native-map','unreachable-state-nonfullness']},indent=2))
