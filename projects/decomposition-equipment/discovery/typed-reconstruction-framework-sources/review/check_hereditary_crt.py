from itertools import product, combinations
import json

def parts(n):
 def go(t):
  if len(t)==n: yield t; return
  for v in range(max(t,default=-1)+2): yield from go(t+(v,))
 return list(go(()))
def eq(p): return {(a,b) for a in range(len(p)) for b in range(len(p)) if p[a]==p[b]}
def join(a,b,n):
 labels=list(range(n))
 for x,y in a|b:
  old,new=labels[y],labels[x]
  labels=[new if z==old else z for z in labels]
 return eq(labels)
def comp(a,b,n): return {(x,z) for x in range(n) for z in range(n) if any((x,y) in a and (y,z) in b for y in range(n))}
def lift(rs,n):
 js={(i,j):join(rs[i],rs[j],n) for i,j in combinations(range(len(rs)),2)}
 for vals in product(range(n),repeat=len(rs)):
  if all((vals[i],vals[j]) in r for (i,j),r in js.items()):
   if not any(all((x,v) in r for r,v in zip(rs,vals)) for x in range(n)): return False
 return True
n=4; relations=[eq(p) for p in parts(n)]; checked=0; passes=0
for rs in product(relations,repeat=3):
 hereditary=all(lift([rs[i] for i in s],n) for k in (2,3) for s in combinations(range(3),k))
 cr=True
 for j in range(3):
  rem=[i for i in range(3) if i!=j]
  for k in (1,2):
   for s in combinations(rem,k):
    meet=set.intersection(*(rs[i] for i in s))
    rhs=set.intersection(*(join(rs[i],rs[j],n) for i in s))
    cr &= comp(meet,rs[j],n)==rhs
 assert cr==hereditary
 checked+=1; passes+=cr
# Actual failure after context restriction, with overlaps recomputed.
points=[(0,0),(0,1),(1,0)]
a=eq([x for x,y in points]); b=eq([y for x,y in points])
assert len(join(a,b,3))==9 and not lift([a,b],3)
print(json.dumps({'status':'PASS','all_equivalence_triples_on_four_points':checked,'hereditary_successes':passes,'includes_nonpermutable':True,'L_shape_recomputed_overlap_failure':True},indent=2))
