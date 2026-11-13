"""Independent brute force: enumerate global maps, not generated coarsenings."""
from itertools import product, combinations
import random,json

def partitions(n):
 if n==0:
  yield ();return
 def rec(a):
  if len(a)==n:yield tuple(a);return
  for v in range(max(a)+2):yield from rec(a+[v])
 yield from rec([0])
def kernel(a):
 d={};return tuple(d.setdefault(x,len(d)) for x in a)
def static(K,types,fibres,anchors):
 if any(K[x]!=K[y] for x,y in anchors):return False
 for c in set(K):
  members=[x for x in range(len(K)) if K[x]==c]
  ts={types[x] for x in members}
  if len(ts)!=1:return False
  e=next(iter(ts))
  if any(sum(K[x]==c for x in xs)!=1 for t,xs in fibres if t==e):return False
 return True

def direct(types,fibres,anchors):
 # Label global events by their type and index, fixing event counts independently.
 n=len(types); out=set()
 bounds=[min([len(xs) for t,xs in fibres if t==e],default=0) for e in [0,1]]
 for counts in product(*(range(b+1) for b in bounds)):
  events=[(e,j) for e,c in enumerate(counts) for j in range(c)]
  choices=[[v for v in events if v[0]==t] for t in types]
  for maps in product(*choices):
   if set(maps)!=set(events):continue
   if any(maps[x]!=maps[y] for x,y in anchors):continue
   # Exact bijection from each fibre to the global fibre (including empty fibres).
   if any(sorted(maps[x] for x in xs)!=[v for v in events if v[0]==e] for e,xs in fibres):continue
   out.add(kernel(maps))
 return out

def operational(K,ops,bops,fibres):
 for c in set(K):
  ys=[x for x in range(len(K)) if K[x]==c and ops[x]>=0]
  if len({K[ops[x]] for x in ys})>1:return False
  for z,(_,xs) in enumerate(fibres):
   for x in xs:
    if K[x]==c and bops[z] and ys and ops[x]<0:return False
 return True

def direct_ops(K,ops,bops,fibres):
 # Enumerate every partial global operation table, impose exact pullback tables
 # and generated graph independently, not via O1/O2 formula.
 m=max(K,default=-1)+1
 for g in product(range(-1,m),repeat=m):
  okay=True
  for z,(_,xs) in enumerate(fibres):
   for x in xs:
    predicted=g[K[x]] if bops[z] else -1
    actual=K[ops[x]] if ops[x]>=0 else -1
    if predicted!=actual:okay=False;break
   if not okay:break
  if not okay:continue
  if any(g[c]>=0 and not any(K[x]==c and ops[x]>=0 for x in range(len(K))) for c in range(m)):continue
  return True
 return False

def main():
 rng=random.Random(20261026);static_cases=0;op_cases=0
 # Random bounded exhaustive-per-instance maps/partitions; include two global types,
 # arbitrary number and multiplicity of interface lifts, empty lifts and carriers.
 for _ in range(500):
  fibres=[];types=[]
  for i in range(rng.randrange(1,4)):
   for z in range(rng.randrange(0,4)):
    t=rng.randrange(2);count=rng.randrange(3)
    xs=list(range(len(types),len(types)+count));types += [t]*count
    fibres.append((t,xs))
  if len(types)>7:continue
  pairs=list(combinations(range(len(types)),2));anchors=[p for p in pairs if rng.random()<.12]
  ps=list(partitions(len(types)))
  by_axioms={k for k in ps if static(k,types,fibres,anchors)}
  by_maps=direct(types,fibres,anchors)
  assert by_axioms==by_maps,(types,fibres,anchors,by_axioms,by_maps)
  static_cases+=1
 # unary endomorphisms with boundary identity where enabled; local operations
 # remain in same boundary fibre, matching e_i homomorphism premise.
 for _ in range(200):
  sizes=[rng.randrange(3) for _ in range(rng.randrange(1,4))]
  fibres=[];n=0
  for s in sizes:fibres.append((0,list(range(n,n+s))));n+=s
  if n>6:continue
  bops=[rng.choice([False,True]) for _ in fibres]
  ops=[]
  for z,(_,xs) in enumerate(fibres):
   ops.extend(rng.choice([-1]+xs) if bops[z] else -1 for x in xs)
  for K in partitions(n):
   if not static(K,[0]*n,fibres,[]):continue
   assert operational(K,ops,bops,fibres)==direct_ops(K,ops,bops,fibres),(K,ops,bops)
   op_cases+=1
 # Deterministic explicit missing coverage can be repaired by optional merge.
 assert direct([0,0],[(0,[0]),(0,[1])],[])=={(0,0)}
 # Duplicated interface permits noninjective map inside chart, one per lift.
 assert static((0,0),[0,0],[(0,[0]),(0,[1])],[])
 # Empty lifted fibre blocks a nonempty global fibre.
 assert direct([0],[(0,[0]),(0,[])],[])==set()
 print(json.dumps({'static_instances':static_cases,'operational_partition_instances':op_cases,'result':'PASS','scope':'Exhaustive maps/partitions per randomized bounded input; not exhaustive universe or proof'},indent=2))
if __name__=='__main__':main()
