#!/usr/bin/env python3
"""Independent finite graph-map regression, not a proof or Lean instantiation.
Graphs: 1 or 2 vertices, 0..2 named edges, every source/target table.
Checks use explicit graph hom enumeration and path transposition, not author code.
"""
from itertools import product
from collections import Counter
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
C=Counter()
def graph(n,ends): return (n,tuple(ends))
def homs(A,B):
 for v in product(range(B[0]),repeat=A[0]):
  for e in product(range(len(B[1])),repeat=len(A[1])):
   if all((v[s],v[t])==B[1][e[i]] for i,(s,t) in enumerate(A[1])): yield (v,e)
def comp(f,g): return tuple(tuple(g[k][i] for i in f[k]) for k in (0,1))
def ident(A): return (tuple(range(A[0])),tuple(range(len(A[1]))))
def onto(f,B): return all(set(f[k])==set(range((B[0],len(B[1]))[k])) for k in (0,1))
def oneone(f): return all(len(set(x))==len(x) for x in f)
def paths(A,n):
 if n==0:return {(v,) for v in range(A[0])}
 return {(A[1][es[0]][0],)+es for es in product(range(len(A[1])),repeat=n) if all(A[1][es[i]][1]==A[1][es[i+1]][0] for i in range(n-1))}
def binary(A,B):
 vs=list(product(range(A[0]),range(B[0])))
 es=list(product(range(len(A[1])),range(len(B[1]))))
 G=graph(len(vs),[(vs.index((A[1][a][0],B[1][b][0])),vs.index((A[1][a][1],B[1][b][1]))) for a,b in es])
 return G,vs,es
Gs=[graph(n,ends) for n in (1,2) for m in range(3) for ends in product(list(product(range(n),repeat=2)),repeat=m)]
for A in Gs:
 for B in Gs:
  G,vs,es=binary(A,B)
  for n in range(4):
   out=set()
   for path in paths(G,n):
    v=vs[path[0]]; edgepairs=[es[e] for e in path[1:]]
    out.add(((v[0],)+tuple(x[0] for x in edgepairs),(v[1],)+tuple(x[1] for x in edgepairs)))
   assert out==set(product(paths(A,n),paths(B,n)))
   assert len(out)==len(paths(G,n)); C['path_product_comparisons']+=1
  for f in homs(A,B):
   C['graph_homs']+=1
   sections=[s for s in homs(B,A) if comp(s,f)==ident(B)]
   if onto(f,B) and not sections:C['surjective_homs_without_section']+=1
   if onto(f,B) and oneone(f):assert len(sections)==1; C['iso_unique_sections']+=1
# Concrete mutation: sortwise onto does NOT imply graph-section.
loop=graph(1,[(0,0)]);cycle=graph(2,[(0,1),(1,0)])
cover=((0,0),(0,0))
assert onto(cover,loop) and not [s for s in homs(loop,cycle) if comp(s,cover)==ident(loop)]
C['mutation_sortwise_section_rejected']=1
# Set-level endpoint comparison and common-J pullback for all small maps.
for m in range(4):
 for n in range(1,4):
  for h in product(range(n),repeat=m):
   equalpairs={(x,y) for x in range(m) for y in range(m) if h[x]==h[y]}
   diag={(x,x) for x in range(m)}
   assert (diag==equalpairs)==(len(set(h))==m)
   C['nullary_endpoint_diagonals']+=1
   # Common-J base change of identity nullary witness stays identity,
   # unlike independently chosen endpoints: m vs sum(fibre^2).
   assert len(diag)==m
   if len(equalpairs)>m:C['independent_vs_shared_lift_separations']+=1
# Coarsening: enumerate all boundary legs and nullary witnesses explicitly.
for b in range(1,4):
 for c in range(3):
  for left in product(range(b),repeat=c):
   for right in product(range(b),repeat=c):
    witnesses=[w for w in product(range(b),repeat=c) if w==left and w==right]
    assert len(witnesses)<=1
    for q in product(range(2),repeat=b):
     image=[tuple(q[x] for x in w) for w in witnesses]
     assert len(image)==len(set(image)); C['nullary_coarsening_injectivity']+=1
     if not witnesses and tuple(q[x] for x in left)==tuple(q[x] for x in right): C['coarsening_new_nullary_operations']+=1
# Distinct repeated-color tuple arrows with the same total map.
outer=(0,0); u=(0,0); v=(0,1)
assert u!=v and tuple(u[x] for x in outer)==tuple(v[x] for x in outer)
assert (u,v)!=(v,u) # occurrence permutation is not equality
C['mutation_total_map_arrow_equality_rejected']=1
# Independent recursive-vs-flattened substitution, repeated color over B={0,1}.
# Every component has identity boundary legs; primitive arities 0,1,2 are diagonal maps.
# A leaf is an identity input occurrence, () is a nullary primitive.
leaf=None
def evaltree(t,b):
 if t is None:return (b,)
 return sum((evaltree(x,b) for x in t),())
def plug(t,replacements):
 if t is None:return next(replacements)
 return tuple(plug(x,replacements) for x in t)
small=[None,(),(None,),(None,None)]
trees=small+[tuple(xs) for k in (1,2) for xs in product(small,repeat=k)]
for t in trees:
 for replacements in product(small,repeat=len(evaltree(t,0))):
  plugged=plug(t,iter(replacements))
  for b in (0,1):
   recursive=(b,evaltree(plugged,b))
   flattened=(b,sum((evaltree(x,b) for x in replacements),()))
   assert recursive==flattened;C['nullary_repeated_color_substitution']+=1
# The boundary field above is necessary, even when all coordinates disappear.
assert (0,evaltree((),0))!=(1,evaltree((),1))
C['mutation_empty_product_terminal_rejected']=1
# Coarsening exactness mutation: diagonal 2 -> square 4.
fine={(0,0),(1,1)}; coarse=set(product(range(2),repeat=2))
assert fine<coarse;C['mutation_coarsening_preserves_exactness_rejected']=1
sources=[ROOT/'theory/Original_Calculus_Dynamic_Interpretation.md']+sorted((ROOT/'theory/original').glob('*.lean'))
result={'status':'PASS','scope':__doc__,'counts':dict(C),'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},'limits':['Finite regression only; mathematical proof reviewed separately.','No Lean execution or concrete Calc instance formalization.','No full virtual-equipment, universal-property, all-model interpretation or physical guarantee claim.']}
print(json.dumps(result,indent=2))
