#!/usr/bin/env python3
"""Independent bounded enumeration; no object-NF => morphism-coherence inference."""
import itertools as I, math, json, collections, functools
if not __debug__:
    raise RuntimeError('Assertions are essential; do not run with -O')
C=collections.Counter()
def comps(v):
    if v==0: yield (); return
    for first in range(1,v+1):
        for tail in comps(v-first): yield (first,)+tail
def weak(v,k):
    if k==0:
        if v==0: yield ()
        return
    for first in range(v+1):
        for tail in weak(v-first,k-1): yield (first,)+tail
def rows(s):
    out=[]; start=0
    for z in s: out.append(tuple(range(start,start+z))); start+=z
    return out
def assignments(v,n): return I.product(range(n),repeat=v)
def matrix(s,p,n): return tuple(tuple(sum(p[x]==j for x in row) for j in range(n)) for row in rows(s))
def mats(s,n): return I.product(*(tuple(weak(z,n)) for z in s))
def typ(s,U): return tuple(z for row in rows(s) if (z:=sum(x in U for x in row)))
def group(s):
    return [tuple(x for part in parts for x in part) for parts in I.product(*(tuple(I.permutations(r)) for r in rows(s)))]
def act(p,g): return tuple(p[g[i]] for i in range(len(p)))
@functools.lru_cache(maxsize=None)
def pull(A,a):
    B=tuple(tuple(sum(row[a[j]:a[j+1]]) for j in range(len(a)-1)) for row in A)
    return tuple(row for row in B if sum(row))
@functools.lru_cache(maxsize=None)
def maps(m,n): return tuple(I.combinations_with_replacement(range(n+1),m+1))
def actualpull(s,p,n,a):
    U=tuple(x for x in range(sum(s)) if a[0]<=p[x]<a[-1])
    q=tuple(next(j for j in range(len(a)-1) if a[j]<=p[x]<a[j+1]) for x in U)
    return typ(s,set(U)),q
# Heredity, type-preserving restriction and extension, including empty.
for v in range(5):
 for s in comps(v):
  G=group(s)
  for bits in I.product((0,1),repeat=v):
   U=tuple(i for i,b in enumerate(bits) if b)
   t=typ(s,set(U))
   assert sum(t)==len(U)
   for g in G:
    V=tuple(sorted(g[u] for u in U))
    assert typ(s,set(V))==t
    h=tuple(V.index(g[u]) for u in U)
    assert h in group(t)
    C['restriction_type_tests']+=1
   for h in group(t):
    ext=list(range(v))
    for i,u in enumerate(U): ext[u]=U[h[i]]
    assert tuple(ext) in G and all(ext[x]==x for x in range(v) if x not in U)
    C['identity_extension_tests']+=1
  for n in range(5):
   ps=list(assignments(v,n)); by=collections.defaultdict(set)
   for p in ps: by[matrix(s,p,n)].add(p)
   assert set(by)==set(mats(s,n))
   for A,orbit in by.items():
    p=min(orbit)
    assert {act(p,g) for g in G}==orbit
    C['exact_orbits']+=1
   C['actual_partitions']+=len(ps)
   # All simplicial maps, including outer faces and nullary domains.
   for p in ps:
    A=matrix(s,p,n)
    for m in range(5):
     for a in maps(m,n):
      t,q=actualpull(s,p,n,a)
      assert matrix(t,q,m)==pull(A,a)
      C['all_map_representative_tests']+=1
   for A in by:
    for m in range(5):
     for a in maps(m,n):
      B=pull(A,a)
      for l in range(5):
       for b in maps(l,m):
        assert pull(B,b)==pull(A,tuple(a[j] for j in b))
        C['simplicial_composition_tests']+=1
# Actual nested partitions: each child row is normalized after zero-row deletion.
for v in range(5):
 for s in comps(v):
  for n in range(1,5):
   for ks in (k for m in range(5) for k in weak(m,n)):
    seen={}
    for p in assignments(v,n):
     blocks=[tuple(x for x in range(v) if p[x]==j) for j in range(n)]
     for qs in I.product(*(tuple(assignments(len(U),k)) for U,k in zip(blocks,ks))):
      flat=[None]*v; off=0; child=[]
      for U,k,q in zip(blocks,ks,qs):
       child.append(matrix(typ(s,set(U)),q,k))
       for x,c in zip(U,q): flat[x]=off+c
       off+=k
      key=(matrix(s,p,n),tuple(child))
      B=matrix(s,flat,sum(ks))
      assert key not in seen or seen[key]==B
      seen[key]=B
      C['nested_actual_partitions']+=1
    C['nested_quotient_pairs']+=len(seen)
  # Exhaustive interval factors, incl empty insertion, unary and entire path.
  for n in range(5):
   expected=set(mats(s,n))
   for lo in range(n+1):
    for hi in range(lo,n+1):
     length=hi-lo; arity=n-length+1; factors={}; inverse={}
     for p in assignments(v,arity):
      U=tuple(x for x in range(v) if p[x]==lo)
      for q in assignments(len(U),length):
       flat=list(p)
       for x in range(v):
        if p[x]>lo: flat[x]=p[x]+length-1
       for x,j in zip(U,q): flat[x]=lo+j
       A=matrix(s,flat,n)
       factor=(matrix(s,p,arity),typ(s,set(U)),matrix(typ(s,set(U)),q,length))
       assert factor not in factors or factors[factor]==A
       assert A not in inverse or inverse[A]==factor
       factors[factor]=A; inverse[A]=factor
       C['actual_interval_factor_pairs']+=1
     assert set(inverse)==expected and len(factors)==len(expected)
     C['interval_bijections']+=1
# Active quotient lift fibres, enumerated as actual fine partitions.
for v in range(5):
 for s in comps(v):
  for m in range(5):
   fine=collections.defaultdict(list)
   for p in assignments(v,m): fine[matrix(s,p,m)].append(p)
   for n in range(5):
    for a in maps(n,m):
     if a[0]!=0 or a[-1]!=m: continue
     for B,ps in fine.items():
      A=pull(B,a)
      counts=collections.Counter(actualpull(s,p,m,a)[1] for p in ps)
      coarse={p for p in assignments(v,n) if matrix(s,p,n)==A}
      assert set(counts)==coarse
      predicted=math.prod(math.factorial(z) for row in A for z in row)//math.prod(math.factorial(z) for row in B for z in row)
      assert set(counts.values())=={predicted}
      C['active_lift_fibres']+=len(counts)
# C2 x [1]: parallel arrows carry bit; compose by xor, not independently chosen endpoints.
arrows=tuple((a,b,e) for a in range(2) for b in range(a,2) for e in range(2))
def compose(f,g):
 assert f[1]==g[0]
 return (f[0],g[1],f[2]^g[2])
for n in range(5):
 paths=[p for p in I.product(arrows,repeat=n) if all(p[j][1]==p[j+1][0] for j in range(n-1))]
 if n==0: paths=[(),()] # two marked vertices
 for p in paths:
  if not p: continue
  for lo in range(n+1):
   for hi in range(lo,n+1):
    start=p[lo][0] if lo<n else p[-1][1]
    f=(start,start,0)
    for g in p[lo:hi]: f=compose(f,g)
    collapsed=p[:lo]+(f,)+p[hi:]
    assert all(collapsed[j][1]==collapsed[j+1][0] for j in range(len(collapsed)-1))
    C['nonthin_grade_intervals']+=1
assert compose((0,1,0),(1,1,1))==(0,1,1)
assert (0,1,0)!=(0,1,1)
C['nonthin_arrows']=len(arrows)
# Same two singleton inputs, retained empty graph vs retained K2: multivalued output.
assert typ((1,1),{0})==typ((2,),{0})==(1,)
assert typ((1,1),{1})==typ((2,),{1})==(1,)
result={'status':'PASS','bounds':{'vertices_max':4,'degrees_max':4,'cluster_types':'all ordered compositions, including empty','K':'C2 x [1]'},'checks':dict(sorted(C.items())),'exclusions':['No B3 morphism coherence or presentation critical-pair proof','No all-graph partition-erasure recognition','No all-degree theorem inferred from finite checks']}
print(json.dumps(result,sort_keys=True,indent=2))
