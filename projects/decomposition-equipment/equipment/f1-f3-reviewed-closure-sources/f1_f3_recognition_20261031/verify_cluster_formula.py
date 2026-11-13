#!/usr/bin/env python3
if not __debug__: raise RuntimeError("Assertions required")
from pathlib import Path
import hashlib
# Load definitions only; this is a supplementary formula/fixture check.
source=Path(__file__).with_name('verify_cluster.py').read_text()
exec(source.split('# Heredity,')[0])
def subst(A,children,ks):
 out=[[] for _ in A]
 for k,(B,width) in enumerate(zip(children,ks)):
  j=0
  for b,row in enumerate(A):
   if row[k]: out[b].extend(B[j]); j+=1
   else: out[b].extend([0]*width)
  assert j==len(B)
 return tuple(map(tuple,out))
for v in range(5):
 for s in comps(v):
  for n in range(1,5):
   for ks in (k for m in range(5) for k in weak(m,n)):
    for p in assignments(v,n):
     blocks=[tuple(x for x in range(v) if p[x]==j) for j in range(n)]
     for qs in I.product(*(tuple(assignments(len(U),k)) for U,k in zip(blocks,ks))):
      flat=[None]*v; off=0; children=[]
      for U,k,q in zip(blocks,ks,qs):
       children.append(matrix(typ(s,set(U)),q,k))
       for x,c in zip(U,q): flat[x]=off+c
       off+=k
      assert subst(matrix(s,p,n),children,ks)==matrix(s,flat,sum(ks))
      C['direct_matrix_substitution_tests']+=1
# Six-vertex heterogeneous cluster fixture: actual full orbits in degree four.
s=(3,2,1); n=4; G=group(s); by=collections.defaultdict(set)
for p in assignments(6,n): by[matrix(s,p,n)].add(p)
for A,orb in by.items():
 assert {act(min(orb),g) for g in G}==orb
 C['six_vertex_exact_orbits']+=1
 for a in maps(3,4):
  t,q=actualpull(s,min(orb),n,a)
  assert matrix(t,q,3)==pull(A,a)
  C['six_vertex_map_tests']+=1
arrows=tuple((a,b,e) for a in range(2) for b in range(a,2) for e in range(2))
for n in range(5):
 paths=[p for p in I.product(arrows,repeat=n) if all(p[j][1]==p[j+1][0] for j in range(n-1))] if n else [(),()]
 assert len(paths)==(n+2)*2**n
 if n>=2: assert len(paths)<len(arrows)**n
 C['nonthin_composable_paths']+=len(paths)
assert pull(((1,0),(0,1),(1,0)),(0,1))==((1,),(1,)) # NEVER merge surviving rows
print(json.dumps({'status':'PASS','checks':dict(sorted(C.items())),'six_vertex_fixture':[3,2,1],'scope':'Direct matrix substitution v<=4 degrees<=4; fixture degree4; K nerve is composable paths, not independent arrows'},sort_keys=True,indent=2))
