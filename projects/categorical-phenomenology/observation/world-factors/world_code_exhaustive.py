#!/usr/bin/env python3
"""Exhaustive tiny affine-code checks, with exact rational certificates.

Requirements: Python 3.10+, NumPy, SciPy. No network access.
Enumerates every affine code and every family of nonempty coordinate contexts
for m=1,2,3. LP solutions are found numerically, then certified EXACTLY by
rational primal/dual feasibility and equality; no conclusion uses LP tolerance.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, math
import numpy as np
from scipy.optimize import linprog
HERE=Path(__file__).resolve().parent
parity=lambda x:x.bit_count()%2

def span(vectors):
    s={0}
    for v in vectors:s|={x^v for x in tuple(s)}
    return frozenset(s)
def subspaces(m):
    spaces={frozenset([0])}
    while True:
        new=spaces|{span(tuple(V)+(x,)) for V in spaces for x in range(1<<m)}
        if new==spaces:return sorted(spaces,key=lambda V:(len(V),sorted(V)))
        spaces=new
def dual(V,m):return frozenset(a for a in range(1<<m) if all(parity(a&v)==0 for v in V))
def reps(V,m):
    seen=set();out=[]
    for x in range(1<<m):
        if x not in seen:out.append(x);seen|={x^v for v in V}
    return out
def exact_rank(rows):
    A=[[F(x) for x in row] for row in rows];i=0
    for j in range(len(A[0])):
        p=next((k for k in range(i,len(A)) if A[k][j]),None)
        if p is None:continue
        A[i],A[p]=A[p],A[i];pivot=A[i][j]
        A[i]=[x/pivot for x in A[i]]
        for k in range(i+1,len(A)):
            v=A[k][j]
            if v:A[k]=[a-v*b for a,b in zip(A[k],A[i])]
        i+=1
        if i==len(A):break
    return i

def exact_cover(M,n):
    if not M:return F(0)
    if not n or any(not any(row) for row in M):return None # infinity
    A=np.array(M,float)
    p=linprog(np.ones(n),A_ub=-A,b_ub=-np.ones(len(M)),bounds=(0,None),method='highs')
    d=linprog(-np.ones(len(M)),A_ub=A.T,b_ub=np.ones(n),bounds=(0,None),method='highs')
    assert p.success and d.success
    x=[F(float(v)).limit_denominator(1000000) for v in p.x]
    y=[F(float(v)).limit_denominator(1000000) for v in d.x]
    assert all(v>=0 for v in x+y)
    assert all(sum(F(a)*b for a,b in zip(row,x))>=1 for row in M)
    assert all(sum(F(M[i][j])*y[i] for i in range(len(M)))<=1 for j in range(n))
    assert sum(x)==sum(y) # Exact primal/dual equality certifies optimality.
    return sum(x)

def marginal(A,J):
    c=Counter(x&J for x in A)
    return {x:F(n,len(A)) for x,n in c.items()}

counts=Counter();by_dimension=[];eps=F(1,10)
for m in range(1,4):
    ms=Counter();allJ=list(range(1,1<<m));universe=range(1<<m)
    for V in subspaces(m):
        D=dual(V,m);rr=reps(V,m);r=int(math.log2(len(V)));Vseq=sorted(V)
        proj={J:{v&J for v in V} for J in allJ}
        local={J:{a for a in D if a&~J==0} for J in allJ}
        # Uniform affine projections and exact contamination likelihood ratios.
        for c in rr:
            A={c^v for v in V};ms['affine_codes']+=1
            for z in rr[1:]:
                B={c^z^v for v in V}
                for J in allJ:
                    p,q=marginal(A,J),marginal(B,J)
                    bad=(z&J) not in proj[J]
                    assert (set(p).isdisjoint(q) if bad else p==q)
                    for x,v in p.items():
                        mixture=(1-eps)*v+eps*q.get(x,F(0))
                        assert v/mixture==(1/(1-eps) if bad else 1)
                    ms['exact_projected_coset_likelihood_checks']+=1
            # Every information-set retraction, with one full-support rational law.
            denom=F((1<<m)*((1<<m)+1),2)
            mu={x:F(x+1)/denom for x in universe}
            for I_tuple in combinations(range(m),r):
                I=sum(1<<i for i in I_tuple)
                if len({v&I for v in V})!=len(V):continue
                inv={x&I:x for x in A};q={x:F(0) for x in universe}
                for x,p in mu.items():q[inv[x&I]]+=p
                tv=sum(abs(mu[x]-q[x]) for x in universe)/2
                assert tv==sum(mu[x] for x in universe if x not in A)
                assert all(sum(mu[x] for x in universe if x&I==i)==sum(q[x] for x in universe if x&I==i) for i in inv)
                ms['exact_retraction_and_marginal_checks']+=1
        for selection in range(1<<len(allJ)):
            H=[J for i,J in enumerate(allJ) if selection>>i&1]
            loc={a for J in H for a in local[J]};loc.add(0)
            S=span(loc)
            hull={x for x in universe if all((x&J) in proj[J] for J in H)}
            assert hull==dual(S,m)
            detectable=S==D
            M=[[int((z&J) not in proj[J]) for J in H] for z in rr[1:]]
            tau=exact_cover(M,len(H));assert (tau is not None)==detectable
            T=sorted(loc-{0});PM=[[parity(z&a) for a in T] for z in rr[1:]]
            sigma=exact_cover(PM,len(T));assert (sigma is not None)==detectable
            if tau is not None:assert tau<=sigma<=2*tau
            ms['exact_LP_pair_certificates']+=1
            chars={0}|{min(a^d for d in D) for a in universe if any(a&~J==0 for J in H)}
            rows=[[1]*len(V)]+[[int(v&J==x) for v in Vseq] for J in H for x in proj[J]]
            rank=exact_rank(rows);assert rank==len(chars)
            # Verify all affine translates as well, not just dimensions.
            for c in rr:
                Aseq=sorted(c^v for v in V)
                arows=[[1]*len(V)]+[[int(v&J==x) for v in Aseq] for J in H for x in {v&J for v in Aseq}]
                assert exact_rank(arows)==len(chars)
                ms['exact_affine_law_rank_checks']+=1
            # Every unseen nonzero coset is observationally invisible.
            for z in rr[1:]:
                invisible=all((z&J) in proj[J] for J in H)
                assert invisible==all(parity(a&z)==0 for a in S)
                if invisible:
                    assert all(marginal(V,J)==marginal({z^v for v in V},J) for J in H)
                    ms['exact_invisible_coset_checks']+=1
            # Every missing character generates two indistinguishable in-code laws.
            for a in universe:
                cls=min(a^d for d in D)
                if cls in chars or a!=cls:continue
                plus={v:F(1+(-1)**parity(a&v),len(V)) for v in V}
                minus={v:F(1-(-1)**parity(a&v),len(V)) for v in V}
                assert sum(plus.values())==sum(minus.values())==1
                assert plus!=minus
                for J in H:
                    for x in proj[J]:assert sum(plus[v] for v in V if v&J==x)==sum(minus[v] for v in V if v&J==x)
                ms['exact_missing_character_witnesses']+=1
            ms['linear_code_context_families']+=1
            if detectable and rank<len(V):ms['support_certifiable_law_unidentified']+=1
            if not detectable and rank==len(V):ms['law_identified_support_uncertifiable']+=1
    by_dimension.append({'m':m,**ms});counts.update(ms)
out={'scope':'Every affine subspace of F2^m and every family of nonempty coordinate contexts, m=1,2,3, including the empty family.', 'arithmetic':'Fraction exact for ranks, probabilities, projection/retraction identities, witnesses, and LP primal/dual certificates. SciPy only locates candidate LP optima.', 'by_dimension':by_dimension,'totals':dict(counts),'all_assertions_passed':True}
(HERE/'world_code_exhaustive_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
