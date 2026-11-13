"""Independent small finite checks for Anchored_Network_Reconstruction.md."""
import itertools,json

def partitions(n):
 def go(a):
  if len(a)==n: yield tuple(a); return
  for k in range(max(a,default=-1)+2): yield from go(a+[k])
 yield from go([])

def solutions(fibres, forced=(), ops=None, base_enabled=None):
 # All occurrences have one global boundary type. fibres list local lifted fibres.
 n=sum(map(len,fibres))
 out=[]
 for a in partitions(n):
  if any(a[x]!=a[y] for x,y in forced):continue
  classes=set(a)
  if any(len({a[x] for x in f})!=len(f) or {a[x] for x in f}!=classes for f in fibres):continue
  if ops is not None:
   good=True
   table={}
   for x,y in ops.items():
    if a[x] in table and table[a[x]]!=a[y]:good=False;break
    table[a[x]]=a[y]
   if not good:continue
   if any(base_enabled[x] and a[x] in table and x not in ops for x in range(n)):continue
  out.append(a)
 return out

pairs=[]
for i,j in itertools.combinations(range(3),2):
 # One shared actual whole event determines one matching; other sheets forced by coverage.
 pairs.append(len(solutions([[0,1],[2,3]],[(0,2)])))
triple=solutions([[0,1],[2,3],[4,5]],[(0,2),(2,4),(4,1)])
assert pairs==[1,1,1] and not triple
assert len(solutions([[0,1],[2,3],[4,5]]))==4
# A noninjective boundary duplicates one event at two local lifts: do NOT demand chart injection.
assert solutions([[0],[1],[2]])==[(0,0,0)]
assert solutions([[0],[]])==[]
# O2 blocks imported operation despite congruence being vacuous.
assert len(solutions([[0],[1]],[(0,1)]))==1
assert not solutions([[0],[1]],[(0,1)],{0:0},[True,True])
# If the second interface disables it, exact cartesian restriction allows its absence.
assert len(solutions([[0],[1]],[(0,1)],{0:0},[True,False]))==1
# O1 forces collision when same abstract state has incompatible successor requirements.
assert len(solutions([[0,1],[2,3]],[(0,2)]))==1
assert not solutions([[0,1],[2,3]],[(0,2)],{0:0,2:3},[True,False,True,False])
print(json.dumps({'pair_solution_counts':pairs,'triple_solution_count':len(triple),'checks_passed':True},indent=2))
