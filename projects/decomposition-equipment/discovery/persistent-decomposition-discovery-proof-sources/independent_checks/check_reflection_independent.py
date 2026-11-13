#!/usr/bin/env python3
"""Independent finite checks for rank reflection and exact record descent.
No author routines imported. Exact rational elimination; deterministic enumeration.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from math import gcd, lcm
import json, random
from pathlib import Path

def partitions(n):
    if n == 0: return [()]
    ans=[]
    def rec(a):
        if len(a)==n: ans.append(tuple(a)); return
        for v in range(max(a)+2): rec(a+[v])
    rec([0]); return ans

def rankone(M,m,n):
    return all(M[i*n+j]*M[k*n+l]==M[i*n+l]*M[k*n+j]
               for i in range(m) for k in range(i+1,m)
               for j in range(n) for l in range(j+1,n))

def aggregate(M,m,n,a,b,pad=0):
    am=max(a,default=-1)+1+pad; bn=max(b,default=-1)+1+pad
    out=[0]*(am*bn)
    for i in range(m):
        for j in range(n): out[a[i]*bn+b[j]]+=M[i*n+j]
    return out,am,bn

def vbasis(m,n):
    B=[]
    for i in range(max(m-1,0)):
        for j in range(max(n-1,0)):
            v=[0]*(m*n)
            for x,y,s in [(i,j,1),(i,n-1,-1),(m-1,j,-1),(m-1,n-1,1)]: v[x*n+y]+=s
            B.append(v)
    return B

def rref(A,k):
    A=[[Q(x) for x in row] for row in A]; piv=[]; r=0
    for c in range(k):
        t=next((t for t in range(r,len(A)) if A[t][c]),None)
        if t is None: continue
        A[r],A[t]=A[t],A[r]; v=A[r][c]; A[r]=[x/v for x in A[r]]
        for t in range(len(A)):
            if t!=r and A[t][c]:
                v=A[t][c]; A[t]=[x-v*y for x,y in zip(A[t],A[r])]
        piv.append(c); r+=1
        if r==len(A): break
    return A,piv

def interaction(m,n,charts):
    B=vbasis(m,n); k=len(B); rows=[]
    for a,b in charts:
        images=[aggregate(v,m,n,a,b)[0] for v in B]
        outlen=(max(a,default=-1)+1)*(max(b,default=-1)+1)
        rows.extend([[im[t] for im in images] for t in range(outlen)])
    A,piv=rref(rows,k)
    if len(piv)==k: return len(piv),None
    f=next(c for c in range(k) if c not in piv); coeff=[Q(0)]*k; coeff[f]=1
    for row,c in zip(A,piv): coeff[c]=-row[f]
    den=lcm(*(x.denominator for x in coeff))
    D=[sum(int(c*den)*v[t] for c,v in zip(coeff,B)) for t in range(m*n)]
    return len(piv),D

def check_kernel_counterexample(m,n,charts,D):
    assert any(D)
    assert all(sum(D[i*n+j] for j in range(n))==0 for i in range(m))
    assert all(sum(D[i*n+j] for i in range(m))==0 for j in range(n))
    for a,b in charts: assert not any(aggregate(D,m,n,a,b)[0])
    N=max(1,1-min(D)); M=[N+x for x in D]
    assert min(M)>0 and not rankone(M,m,n)
    for a,b in charts:
        U,u,v=aggregate(M,m,n,a,b); assert rankone(U,u,v)
    return M

stats={'exhaustive_families':0,'bounded_matrix_family_checks':0,'constructed_kernel_counterexamples':0,
       'injective_families':0,'noninjective_families':0,'padded_non_surjective_checks':0}
rng=random.Random(20261026)
for m,n,cap in [(0,0,2),(0,3,2),(3,0,2),(1,3,2),(2,2,2),(2,3,2),(3,3,1)]:
    charts=list(product(partitions(m),partitions(n)))
    if len(charts)<=10:
        families=[tuple(c for k,c in enumerate(charts) if mask>>k&1) for mask in range(1<<len(charts))]
        stats['exhaustive_families']+=len(families)
    else:
        families=[(),tuple(charts)]+[(c,) for c in charts]
        families += [tuple(c for c in charts if rng.randrange(2)) for _ in range(125)]
    matrices=list(product(range(cap+1),repeat=m*n))
    # Compute chart passes once; family evaluation uses integer bitsets.
    bad=[M for M in matrices if not rankone(M,m,n)]
    masks={}
    for c in charts:
        mask=0
        for k,M in enumerate(bad):
            U,u,v=aggregate(M,m,n,*c)
            if rankone(U,u,v): mask|=1<<k
        masks[c]=mask
    for family in families:
        rank,D=interaction(m,n,family)
        stats['bounded_matrix_family_checks']+=len(matrices)
        survives=(1<<len(bad))-1
        for c in family: survives&=masks[c]
        if D is None:
            stats['injective_families']+=1; assert survives==0
        else:
            stats['noninjective_families']+=1
            M=check_kernel_counterexample(m,n,family,D)
            stats['constructed_kernel_counterexamples']+=1
            for a,b in family:
                U,u,v=aggregate(M,m,n,a,b,pad=1)
                assert rankone(U,u,v); stats['padded_non_surjective_checks']+=1

# Actual state maps induce transition-type maps p x p.
def pairmap(p):
    q=max(p,default=-1)+1
    return tuple(p[i]*q+p[j] for i in range(len(p)) for j in range(len(p)))
state_tests=[]
for k in [2,3,4]:
    P=[p for p in partitions(k) if max(p)+1<k]
    # k=4: all pair-merge maps suffice and avoid much larger family.
    if k==4: P=[p for p in P if max(p)+1==k-1]
    maps=[pairmap(p) for p in P]
    charts=list(product(maps,maps)); m=n=k*k
    rank,D=interaction(m,n,charts)
    record={'states_per_component':k,'proper_state_maps':len(P),'charts':len(charts),
            'interaction_dimension':(m-1)*(n-1),'measurement_rank':rank,'reflects':D is None}
    if D is not None:
        M=check_kernel_counterexample(m,n,charts,D)
        record['counterexample_entry_range']=[min(M),max(M)]
    state_tests.append(record)
assert state_tests[1]['reflects'] is False
assert state_tests[2]['reflects'] is True
# Explicit 3-cycle circulation independently verifies all proper state quotients kill it.
cycle=[0,1,-1,-1,0,1,1,-1,0]
for p in partitions(3):
    if max(p)+1<3:
        pp=pairmap(p); out=[0]*(max(pp)+1)
        for a,x in zip(pp,cycle): out[a]+=x
        assert not any(out)

# A genuinely temporal blind interaction: the three-state circulation.
# Full support is nonrectangular, but all proper state views look independent.
L=[0,1,-1,-1,0,1,1,-1,0]
M=[1+x*y for x in L for y in L]
assert min(M)==0 and max(M)==2 and not rankone(M,9,9)
proper=[p for p in partitions(3) if max(p)+1<3]
for p in proper:
 for q in proper:
  U,u,v=aggregate(M,9,9,pairmap(p),pairmap(q)); assert rankone(U,u,v)
# The views nevertheless jointly distinguish every pair of component states.
assert all(any(p[x]!=p[y] for p in proper) for x in range(3) for y in range(x+1,3))
# Aggregate-only blindness is NOT blindness of event-aligned views.
state_views=list(product(proper,proper))
states=list(product(range(3),repeat=2))
signatures={tuple((p[z],q[y]) for p,q in state_views):(z,y) for z,y in states}
assert len(signatures)==len(states)
events=[(r,c,k) for r in range(9) for c in range(9) for k in range(M[r*9+c])]
rebuilt=[0]*81
for r,c,k in events:
 z,z1=divmod(r,3); y,y1=divmod(c,3)
 source_sig=tuple((p[z],q[y]) for p,q in state_views)
 target_sig=tuple((p[z1],q[y1]) for p,q in state_views)
 zz,yy=signatures[source_sig]; zz1,yy1=signatures[target_sig]
 rebuilt[(zz*3+zz1)*9+yy*3+yy1]+=1
assert rebuilt==M
for p,q in state_views:
 assert aggregate(M,9,9,pairmap(p),pairmap(q))==aggregate([1]*81,9,9,pairmap(p),pairmap(q))
assert M!=[1]*81

# Exact record quotient: independent explicit fibres vs formula.
record_cases=0; exact_cases=0; nonexact_cases=0
for d in range(4):
 for f in range(4):
  for ld in product(range(2),repeat=d):
   for lf in product(range(2),repeat=f):
    for r in partitions(d):
     for s in partitions(f):
      for q in [(0,0),(0,1)]:
       rd=max(r,default=-1)+1; sf=max(s,default=-1)+1
       dr=[{q[ld[x]] for x in range(d) if r[x]==a} for a in range(rd)]
       fs=[{q[lf[y]] for y in range(f) if s[y]==b} for b in range(sf)]
       if any(len(z)!=1 for z in dr+fs): continue
       # Include non-surjective quotients by adjoining empty target fibres.
       for ed in [[],[{0}],[{1}]]:
        for ef in [[],[{0}],[{1}]]:
         DR=dr+ed; FS=fs+ef
         target={(a,b) for a in range(len(DR)) for b in range(len(FS)) if DR[a]==FS[b]}
         fibres={z:[] for z in target}
         for x in range(d):
          for y in range(f):
           if ld[x]==lf[y]: fibres[(r[x],s[y])].append((x,y))
         actual=all(len(v)==1 for v in fibres.values())
         formula=all(sum(sum(r[x]==a and ld[x]==j for x in range(d))*
                         sum(s[y]==b and lf[y]==j for y in range(f)) for j in range(2))==1
                     for a,b in target)
         assert actual==formula
         record_cases+=1
         exact_cases+=actual; nonexact_cases+=not actual

out={'status':'PASS','linear_reflection':stats,'state_induced_views':state_tests,
     'temporal_circulation':{'states_per_side':3,'entry_range':[0,2],'proper_joint_views':16,'global_factorization':False,'all_proper_views_factor':True,'aggregate_only_blindness':True,'aligned_record_reconstruction':True,'actual_event_count':81},
     'record_descent':{'cases':record_cases,'exact':exact_cases,'nonexact':nonexact_cases},
     'trust':'Python exact rational/integer finite checks; not a formal proof or unbounded enumeration.'}
p=Path(__file__).with_suffix('.json'); p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
