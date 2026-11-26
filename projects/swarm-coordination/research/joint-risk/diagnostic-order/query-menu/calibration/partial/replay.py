from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import json, math

def char(a,x): return (-1)**((a&x).bit_count())

def full(n,menu,signs):
    d=len(menu)
    return {x:F(2*d+sum(s*char(t,x) for t,s in zip(menu,signs)),2*d*(1<<n))
            for x in range(1<<n)}

def marginal(law,B):
    res=Counter()
    for x,w in law.items():res[x&B]+=w
    return dict(res)

def verify_projections():
    n,m=6,3
    menu=tuple(b for b in range(1<<n) if b&1 and b.bit_count()==m)
    d=len(menu)
    p0=full(n,menu,(1,)*d)
    zero_or_one=0
    for B in (b for b in range(1<<n) if b.bit_count()<=m):
        if B in menu:
            assert marginal(p0,B)=={x:F(1,1<<m)*(1+F(char(B,x),2*d))
                                    for x in range(1<<n) if x&B==x}
        else:
            assert marginal(p0,B)=={x:F(1,1<<B.bit_count())
                                     for x in range(1<<n) if x&B==x}
        for j,T in enumerate(menu):
            p1=full(n,menu,tuple(-1 if i==j else 1 for i in range(d)))
            assert (marginal(p0,B)!=marginal(p1,B))==(B==T)
            zero_or_one+=1
    ternary=0
    for s in product((-1,1),repeat=d):
        p=full(n,menu,s)
        for T,j in zip(menu,s):
            result=Counter()
            i=T&-T
            for x,f in p.items():result[(char(T,x)-char(i,x))//2]+=f
            for rho in (F(1,10),F(1,2),F(1)):
                obs={z:rho*result[z]+(1-rho if z==0 else 0) for z in (-1,0,1)}
                assert obs=={-1:rho/4*(1-F(j,2*d)),0:1-rho/2,1:rho/4*(1+F(j,2*d))}
                ternary+=1
    return dict(sites=n,bundle_size=m,menu_size=d,projection_controls=zero_or_one,
                exact_ternary_checks=ternary)

# Small independent Bayes controls for real observed flags and raw projected
# values. Inside an active window parity is sufficient on the selected arm.
D=3
RHO=F(1,2)
EPS=F(1,2*D)
A=F(1)+EPS
B=F(1)-EPS
SIGNS=tuple(product((-1,1),repeat=D))
TYPES=(-1,0,1) # ± active parities, 0 inactive
def likelihood(s,z):
    return 1-RHO if z==0 else RHO/2*(1+s*z*EPS)

@lru_cache(None)
def arm_marg(L):
    v=(A/B)**L
    return v/(1+v)

def update(L,i,z):
    return L[:i]+(L[i]+z,)+L[i+1:]

def map_success(L):
    return math.prod(max(arm_marg(v),1-arm_marg(v)) for v in L)

def predictive(L,i,z):
    p=arm_marg(L[i])
    return p*likelihood(1,z)+(1-p)*likelihood(-1,z)

def validate_transcripts(horizon):
    # A visibly history-dependent policy, not fixed equal allocation.
    leaves=0
    gain=F(0)
    def walk(logs,full_weights,depth,path):
        nonlocal leaves,gain
        mass=sum(full_weights)
        posterior=tuple(w/mass for w in full_weights)
        expect=tuple(math.prod((arm_marg(l) if s==1 else 1-arm_marg(l))
                               for l,s in zip(logs,h)) for h in SIGNS)
        assert posterior==expect
        assert max(posterior)==map_success(logs)
        if depth==horizon:
            leaves+=1
            gain+=max(full_weights)
            return
        i=(depth+sum((i+1)*z for i,z in enumerate(path)))%D
        for z in TYPES:
            direct=tuple(v*likelihood(s[i],z) for v,s in zip(full_weights,SIGNS))
            assert sum(direct)/mass==predictive(logs,i,z)
            walk(update(logs,i,z),direct,depth+1,path+(z,))
    walk((0,)*D,(F(1,len(SIGNS)),)*len(SIGNS),0,())
    return leaves,gain

@lru_cache(None)
def optimal(logs,h):
    if not h:return map_success(logs)
    return max(sum(predictive(logs,i,z)*optimal(update(logs,i,z),h-1) for z in TYPES)
               for i in range(D))

@lru_cache(None)
def fixed_pull(logs,order):
    if not order:return map_success(logs)
    i,*q=order
    return sum(predictive(logs,i,z)*fixed_pull(update(logs,i,z),tuple(q)) for z in TYPES)

def bayes():
    horizon=5
    leaves,gain=validate_transcripts(horizon)
    cases=[(h-i-j,j,i) for h in (horizon,) for i in range(h+1) for j in range(h-i+1)]
    fixed_best=max(fixed_pull((0,)*D,(0,)*a+(1,)*b+(2,)*c) for a,b,c in cases)
    adaptive=optimal((0,)*D,horizon)
    assert adaptive>=max(gain,fixed_best)
    return dict(arms=D,rho=str(RHO),horizon=horizon,full_posterior_leaves=leaves,
                history_rule_success=str(gain),optimal_adaptive_success=str(adaptive),
                optimal_fixed_allocation_success=str(fixed_best))

if __name__=="__main__":
    print(json.dumps({"projections":verify_projections(),"small_flagged_bayes_oracle":bayes()},
                     sort_keys=True,indent=2))
