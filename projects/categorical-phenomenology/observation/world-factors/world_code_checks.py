#!/usr/bin/env python3
"""Finite checks for affine response-code certification and internal-law identification."""
from pathlib import Path
import itertools,math,json
import numpy as np
from scipy.optimize import linprog
HERE=Path(__file__).resolve().parent
parity=lambda x:x.bit_count()%2

def span(vectors):
    out={0}
    for v in vectors:out|={u^v for u in list(out)}
    return frozenset(out)
def dual(V,m):return frozenset(a for a in range(1<<m) if all(parity(a&v)==0 for v in V))
def reps(V,m):
    seen=set();out=[]
    for x in range(1<<m):
        if x not in seen:out.append(x);seen|={x^v for v in V}
    return out

def lp_cover(M):
    if len(M)==0:return 0.
    M=np.asarray(M,float)
    if M.shape[1]==0:return math.inf
    res=linprog(np.ones(M.shape[1]),A_ub=-M,b_ub=-np.ones(M.shape[0]),bounds=(0,None),method='highs')
    return float(res.fun) if res.success else math.inf

def inspect(V,m,H):
    D=dual(V,m);R=reps(V,m)[1:]
    P=[{v&J for v in V} for J in H]
    M=[[float((z&J) not in p) for J,p in zip(H,P)] for z in R]
    tau=lp_cover(M)
    loc={a for a in D if any(a&~J==0 for J in H)}
    gen=span(loc)
    assert math.isfinite(tau)==(gen==D)
    parityM=[[float(parity(z&a)) for a in loc] for z in R]
    sigma=lp_cover(parityM)
    if math.isfinite(tau):assert tau-1e-8<=sigma<=2*tau+1e-8
    else:assert math.isinf(sigma)
    chars={min(a^d for d in D) for a in range(1<<m) if any(a&~J==0 for J in H)}
    rows=[]
    for J,p in zip(H,P):
        for a in p:rows.append([float(v&J==a) for v in V])
    # Include normalization independently even if H is empty.
    rows.append([1.]*len(V));chars.add(0)
    rank=int(np.linalg.matrix_rank(np.array(rows)))
    assert rank==len(chars)
    return {'m':m,'dimension':int(math.log2(len(V))),'context_count':len(H),'tau':tau if math.isfinite(tau) else 'infinity','parity_tau':sigma if math.isfinite(sigma) else 'infinity','internal_law_rank':rank,'code_size':len(V),'local_dual_dimension':int(math.log2(len(gen)))}

examples={
'double_copy':inspect(span([3,12]),4,[3,12]),
'double_copy_with_cross_pair':inspect(span([3,12]),4,[3,12,5]),
'even_parity_pair_only':inspect(span([3,5]),3,[3,5,6]),
'even_parity_one_pair':inspect(span([3,5]),3,[3]),
'singleton_singletons':inspect(frozenset([0]),4,[1,2,4,8]),
'whole_space_singletons':inspect(frozenset(range(16)),4,[1,2,4,8]),
'repetition_tree':inspect(span([15]),4,[3,6,12])}
assert examples['double_copy']['tau']==2 and examples['double_copy']['internal_law_rank']==3
assert examples['double_copy_with_cross_pair']['tau']==2 and examples['double_copy_with_cross_pair']['internal_law_rank']==4
assert examples['even_parity_pair_only']['tau']=='infinity' and examples['even_parity_pair_only']['internal_law_rank']==4
assert examples['singleton_singletons']['tau']==4
assert examples['whole_space_singletons']['tau']==0

rng=np.random.default_rng(20261103)
cases=[];kl_count=0;tv_count=0;kl_err=0;tv_err=0
for m in range(2,8):
 for t in range(30):
    V=span(int(v) for v in rng.integers(0,1<<m,size=int(rng.integers(0,m+1))))
    H=list({int(v) for v in rng.integers(1,1<<m,size=int(rng.integers(1,2*m+1)))})
    cases.append(inspect(V,m,H))
    c=int(rng.integers(0,1<<m));A=sorted(c^v for v in V)
    # Exact projection supports/counts for uniform code vs uniform coset.
    for z in reps(V,m)[1:]:
      B=[c^z^v for v in V]
      for J in H:
        p={a:sum(x&J==a for x in A)/len(A) for a in {x&J for x in A}}
        r={a:sum(x&J==a for x in B)/len(B) for a in {x&J for x in B}}
        same=set(p)==set(r)
        assert same or set(p).isdisjoint(r)
        if same:assert p==r
        kl=sum(v*math.log(v/(.9*v+.1*r.get(a,0))) for a,v in p.items())
        expected=0 if same else -math.log(.9)
        kl_err=max(kl_err,abs(kl-expected));kl_count+=1
    # A root information set always exists, including rank 0 and full rank.
    rank=int(math.log2(len(V)))
    I=next(sum(1<<i for i in C) for C in itertools.combinations(range(m),rank) if len({v&sum(1<<i for i in C) for v in V})==len(V))
    inv={x&I:x for x in A}
    mu=rng.dirichlet(np.ones(1<<m));q=np.zeros(1<<m)
    for x,p in enumerate(mu):q[inv[x&I]]+=p
    tv=float(.5*abs(mu-q).sum());bad=1-float(mu[A].sum())
    tv_err=max(tv_err,abs(tv-bad));tv_count+=1
    assert abs(tv-bad)<1e-12
out={'examples':examples,'random_cases':len(cases),'all_cases':cases,'raw_context_kl_checks':kl_count,'maximum_kl_error':kl_err,'retraction_checks':tv_count,'maximum_tv_error':tv_err}
(HERE/'world_code_checks_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='all_cases'},indent=2))
