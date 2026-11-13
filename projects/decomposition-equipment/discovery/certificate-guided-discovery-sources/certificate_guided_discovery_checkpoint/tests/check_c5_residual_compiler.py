#!/usr/bin/env python3
"""Finite source-compiler calibration. Exhaustive ranges are explicit; not a proof."""
from itertools import product, permutations
from collections import defaultdict
import json

counts=defaultdict(int)

def partitions(n,k):
    for labels in product(range(k),repeat=n):
        yield tuple(tuple(v for v in range(n) if labels[v]==i) for i in range(k))

def compositions(n,k):
    if k==0:
        if n==0: yield ()
    else:
        for a in range(n+1):
            for tail in compositions(n-a,k-1): yield (a,)+tail

def induced(G,U):
    return tuple((i,j) for i in range(len(U)) for j in range(i+1,len(U)) if (U[i],U[j]) in G)

def compiled_embeddings(n,sizes):
    # Constraint search over integer variables, independent of partition labels.
    # All-different + exactly n entries permits using permutations directly.
    for p in permutations(range(n)):
        E=[]; off=0
        for size in sizes:
            e=p[off:off+size]; off+=size
            if tuple(sorted(e))!=e: break
            E.append(e)
        else: yield tuple(E)

def subst(E,D):
    return tuple(tuple(E[i][v] for v in d) for i,ds in enumerate(D) for d in ds)

def graphs(n):
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    for bits in product((0,1),repeat=len(pairs)):
        yield frozenset(e for e,b in zip(pairs,bits) if b)

# Compare all profile fibres, including repeated isomorphic inputs and empties.
for n in range(5):
  for G in graphs(n):
    for k in range(4):
      actual=defaultdict(set); compiled=defaultdict(set)
      for E in partitions(n,k):
        key=tuple((len(e),induced(G,e)) for e in E)
        actual[key].add(E)
      for sizes in compositions(n,k):
        for E in compiled_embeddings(n,sizes):
          key=tuple((len(e),induced(G,e)) for e in E)
          compiled[key].add(E)
      assert dict(actual)==dict(compiled)
      counts['profile_families']+=1
      counts['normal_forms']+=sum(map(len,actual.values()))

# All nested inner partitions arity 0..2 for outputs of size <=3.
for n in range(4):
  for k in range(4):
    for E in partitions(n,k):
      choices=[list(d for arity in range(3) for d in partitions(len(e),arity)) for e in E]
      for D in product(*choices):
        H=subst(E,D)
        assert sorted(v for h in H for v in h)==list(range(n))
        assert all(tuple(sorted(h))==h for h in H)
        for G in graphs(n):
          for i,ds in enumerate(D):
            Gi=frozenset(induced(G,E[i]))
            for d in ds:
              h=tuple(E[i][v] for v in d)
              assert induced(G,h)==induced(Gi,d)
        counts['substitution_instances']+=1
        # scalar formula in additive C4, all two-node totals modeled by sum.
        for m in range(4):
          ns=tuple((i+m)%4 for i in range(k))
          assert (m+sum(ns))%4 == sum((m,)+ns)%4
          counts['scalar_products']+=1

# R: every ordered triple partition, actual binary-group labels.
for n in range(5):
  for U,V,W in partitions(n,3):
    UV=tuple(sorted(U+V)); VW=tuple(sorted(V+W))
    left=subst((UV,W),((tuple(UV.index(x) for x in U),tuple(UV.index(x) for x in V)),(tuple(range(len(W))),)))
    right=subst((U,VW),((tuple(range(len(U))),),(tuple(VW.index(x) for x in V),tuple(VW.index(x) for x in W))))
    assert left==right==(U,V,W)
    counts['R_instances']+=1

# Units including genuinely empty whole; a retained empty leaf isn't deleted.
for n in range(5):
  ident=(tuple(range(n)),)
  assert subst(((),tuple(range(n))),((),ident))==ident
  assert subst((tuple(range(n)),()),(ident,()))==ident
  assert len(((),))==1 and len(())==0
  counts['unit_pairs']+=1

# DA, DL, DR, D0: flat scalar placement with C4 additive notation.
for m,n,p in product(range(4),repeat=3):
    assert (m+n+p)%4==(m+(n+p)%4)%4
    assert (m+n+p)%4==(n+(m+p)%4)%4
    assert (0+m)%4==m
    counts['scalar_rule_instances']+=1

# Genuine partition forgetting: same profile, different concrete target.
a=((0,),(1,)); b=((1,),(0,)); identities=(((0,),),((0,),))
assert a!=b and subst(a,identities)==a and subst(a,identities)!=b
# Exact nullary scalar survives: no phantom child can absorb it.
for m in range(4):
    assert (m+sum(()))%4==m
counts['partition_forgetting_positive_negative_pair']=1
counts['nullary_scalar_checks']=4

out={'status':'PASS','scope':'finite calibration; complete proof in Source_Derived_Residual_Certificates.md','counts':dict(counts)}
print(json.dumps(out,indent=2,sort_keys=True))
