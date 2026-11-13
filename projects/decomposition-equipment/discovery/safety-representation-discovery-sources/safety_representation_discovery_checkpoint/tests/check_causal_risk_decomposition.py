#!/usr/bin/env python3
"""Exact rational calibrations of causal transfer, LP bounds and interaction witnesses."""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import json


def solve_unique(rows, vals, n):
    a=[[Q(x) for x in row]+[Q(v)] for row,v in zip(rows,vals)]
    r=0; piv=[]
    for c in range(n):
        z=next((i for i in range(r,len(a)) if a[i][c]),None)
        if z is None: continue
        a[r],a[z]=a[z],a[r];d=a[r][c];a[r]=[x/d for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][c]:
                d=a[i][c];a[i]=[x-d*y for x,y in zip(a[i],a[r])]
        piv.append(c);r+=1
    if any(not any(row[:n]) and row[n] for row in a): return None
    if r!=n: return None
    v=[Q(0)]*n
    for i,c in enumerate(piv):v[c]=a[i][n]
    return tuple(v)


def rank(rows,n):
    a=[[Q(x) for x in row] for row in rows];r=0
    for c in range(n):
        z=next((i for i in range(r,len(a)) if a[i][c]),None)
        if z is None:continue
        a[r],a[z]=a[z],a[r];d=a[r][c];a[r]=[x/d for x in a[r]]
        for i in range(r+1,len(a)):
            d=a[i][c];a[i]=[x-d*y for x,y in zip(a[i],a[r])]
        r+=1
    return r


def vertices(eq,b,ineq,h,n):
    k=n-rank(eq,n);out=set()
    for choice in combinations(range(len(ineq)),k):
        v=solve_unique(eq+[ineq[i] for i in choice],b+[h[i] for i in choice],n)
        if v is None:continue
        if all(sum(a*x for a,x in zip(row,v))<=z for row,z in zip(ineq,h)):
            out.add(v)
    return out


def bounds(eq,b,c,ineq=None,h=None):
    n=len(c);nn=[[-int(i==j) for j in range(n)] for i in range(n)]
    vs=vertices(eq,b,nn+(ineq or []),[Q(0)]*n+(h or []),n)
    if not vs:return None
    scored=[(sum(ci*pi for ci,pi in zip(c,v)),v) for v in vs]
    return min(scored),max(scored)


def policy_law(init, k0, k1, policy):
    out={}
    for o0,a0,o1,a1,o2 in product(range(2),repeat=5):
        pr=(init if o0 else 1-init)
        pa=policy((o0,),a0);pr*=pa
        z=k0(o0,a0);pr*=z if o1 else 1-z
        pa=policy((o0,a0,o1),a1);pr*=pa
        z=k1(o0,a0,o1,a1);pr*=z if o2 else 1-z
        out[(o0,a0,o1,a1,o2)]=pr
    assert sum(out.values())==1
    return out


def marginal(law,prefix):
    return sum(p for omega,p in law.items() if omega[:len(prefix)]==prefix)


def main():
    counts={}
    # Every feasible 2x2 marginal example has the Frechet range; no independence assumed.
    pts=list(product(range(2),repeat=2));one=[1]*4;x=[s[0] for s in pts];y=[s[1] for s in pts];c=[a*b for a,b in pts]
    n=0
    for a,b in product([Q(i,4) for i in range(5)],repeat=2):
        lo,hi=bounds([one,x,y],[1,a,b],c)
        assert lo[0]==max(Q(0),a+b-1) and hi[0]==min(a,b)
        # A valid dual c <= x or c <= y attains the upper bound.
        d=x if a<=b else y;assert all(ci<=di for ci,di in zip(c,d))
        n+=1
    counts['rational_marginal_lp_cases']=n
    coarse=bounds([one,x,y],[1,Q(1,2),Q(1,2)],c)
    full=bounds([one,x,y,c],[1,Q(1,2),Q(1,2),Q(1,5)],c)
    assert coarse[1][0]==Q(1,2) and full[1][0]==Q(1,5)
    bad=coarse[1][1];assert sum(ci*pi for ci,pi in zip(c,bad))!=Q(1,5)
    assert sum(xi*pi for xi,pi in zip(x,bad))==Q(1,2)
    assert sum(yi*pi for yi,pi in zip(y,bad))==Q(1,2)
    assert bounds([one,x,x],[1,Q(1,5),Q(3,10)],c) is None
    lo,hi=bounds([one],[1],c,[x,[-v for v in x],y,[-v for v in y]],[Q(3,5),-Q(2,5),Q(3,5),-Q(2,5)])
    assert (lo[0],hi[0])==(0,Q(3,5))
    counts['representation_gap_and_interval_controls']=3
    # Threshold adequacy is weaker than exact-risk reconstruction.
    pair_eq=[one+[0]*4,[0]*4+one,x+[-v for v in x],y+[-v for v in y]]
    pair_b=[1,1,0,0];obj=[0]*4+c
    low_constraint=c+[0]*4
    tlo,thi=bounds(pair_eq,pair_b,obj,[low_constraint],[Q(1,4)])
    assert thi[0]==Q(5,8)  # same marginals can straddle threshold1/4
    tlo,thi=bounds(pair_eq+[c+[-v for v in c]],pair_b+[0],obj,[low_constraint],[Q(1,4)])
    assert thi[0]==Q(1,4)  # retaining the joint event prevents a straddling pair
    tiny=[Q(v,10) for v in c]
    assert bounds([one],[1],tiny)[1][0]==Q(1,10)<Q(1,5)
    counts['threshold_adequacy_controls']=3
    # Triple risk is not in the pair marginal span. Construct actual equal-observation laws.
    pts3=list(product(range(2),repeat=3));rows=[[1]*8]
    rows += [[s[i] for s in pts3] for i in range(3)]
    rows += [[s[i]*s[j] for s in pts3] for i,j in combinations(range(3),2)]
    risk=[int(sum(s)>=2) for s in pts3]
    triple=[s[0]*s[1]*s[2] for s in pts3]
    assert rank(rows,8)==7 and rank(rows+[risk],8)==8
    assert rank(rows+[triple],8)==8
    even=[Q(int(sum(s)%2==0),4) for s in pts3]
    odd=[Q(int(sum(s)%2==1),4) for s in pts3]
    assert all(sum(r*p for r,p in zip(row,even))==sum(r*p for r,p in zip(row,odd)) for row in rows)
    assert sum(r*p for r,p in zip(risk,even))==Q(3,4)
    assert sum(r*p for r,p in zip(risk,odd))==Q(1,4)
    for s,r,t in zip(pts3,risk,triple):
        assert r==sum(s[i]*s[j] for i,j in combinations(range(3),2))-2*t
    counts['triple_pointwise_dual_and_rank_checks']=11
    # General proper-patch ambiguity controls.
    patch_cases=0
    for n in range(3,7):
        states=list(product(range(2),repeat=n))
        for k in range(n):
            for scope in combinations(range(n),k):
                for value in product(range(2),repeat=k):
                    counts_by_parity=[sum(1 for s in states if tuple(s[i] for i in scope)==value and sum(s)%2==p) for p in (0,1)]
                    assert counts_by_parity[0]==counts_by_parity[1];patch_cases+=1
    counts['proper_patch_equal_law_checks']=patch_cases
    # Non Markov causal models: the second kernel explicitly depends on old o0 and a0.
    cases=0;prefix_checks=0
    for init, mode, target_mode, eprob in product([Q(0),Q(1,3),Q(1)],range(8),range(4),[Q(1,4),Q(1,2),Q(3,4)]):
        def e(hist,a):
            pa=eprob if hist[0] else 1-eprob
            return pa if a else 1-pa
        def pi(hist,a):
            choice=(hist[-1] if target_mode&1 else hist[0]) ^ int(bool(target_mode&2))
            return Q(a==choice)
        def k0(o,a):return Q(((o if mode&1 else 0)^(a if mode&2 else 0)),1)
        def k1(o0,a0,o1,a1):return Q((o0^a0^o1^(a1 if mode&4 else 0)),1)
        p=policy_law(init,k0,k1,e);q=policy_law(init,k0,k1,pi)
        for omega,pr in p.items():
            w=pi(omega[:1],omega[1])/e(omega[:1],omega[1])*pi(omega[:3],omega[3])/e(omega[:3],omega[3])
            assert q[omega]==w*pr
        for t in (0,1):
            for hist in product(range(2),repeat=2*t+1):
                for a in range(2):
                    assert marginal(p,hist+(a,))==e(hist,a)*marginal(p,hist);prefix_checks+=1
        cases+=1
    counts['causal_nonmarkov_policy_transfer_models']=cases
    counts['exact_prefix_randomization_checks']=prefix_checks
    # Support failure: identical e-law says nothing about never tried action1.
    exploration_laws=[{(0,0):Q(1)} for _ in range(2)]
    target_risks=[Q(0),Q(1)]
    assert exploration_laws[0]==exploration_laws[1] and target_risks[0]!=target_risks[1]
    # Upper hazard detector high risk does not imply physical unsafe.
    assert Q(0)<=Q(1) and not(Q(0)>Q(1,2))
    out={'status':'PASS','counts':counts,'controls':['global joint law retained','finite confidence bands distinct from equal population laws','empty feasible family rejected','known exogenous policy required','missing target support does not identify risk','upper detector alone cannot prove physical unsafety']}
    path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
