"""Exact certificates for any-failure ambiguity under shared low-order laws."""
from fractions import Fraction as F
from itertools import combinations
import json
from math import comb,prod

def signed_weights(S):
    w=tuple(F(1,prod(x-y for y in S if y!=x)) for x in S)
    return tuple(-v for v in w) if w[0]<0 else w

def score(S):
    w=signed_weights(S)
    return w[0]/sum(x for x in w if x>0)

def law_pair(S):
    w=signed_weights(S)
    a=sum(x for x in w if x>0)
    return ({x:v/a for x,v in zip(S,w) if v>0},
            {x:-v/a for x,v in zip(S,w) if v<0})

def verify_pair(S,k):
    lo,hi=law_pair(S)
    assert sum(lo.values())==sum(hi.values())==1
    for j in range(k+1):
        assert sum(v*comb(x,j) for x,v in lo.items())==sum(v*comb(x,j) for x,v in hi.items())
    gap=lo[0]-hi.get(0,0)
    assert gap==score(S)
    return gap

def uniform_upper(n,k,S):
    """Independent pointwise bounded polynomial giving the matching upper bound."""
    err=score(S)/2
    X=S[:-1]
    assert len(X)==k+1
    vals=[F(x==0)-(-1)**i*err for i,x in enumerate(X)]
    weights=signed_weights(X)
    def eval_p(t):
        if t in X:return vals[X.index(t)]
        lows=[w/F(t-x) for x,w in zip(X,weights)]
        return sum(y*b for y,b in zip(vals,lows))/sum(lows)
    assert all(abs(F(t==0)-eval_p(t))<=err for t in range(n+1))
    return err*2

def support_search(n,k):
    if k>=n:return F(0),None
    options=((0,*cc) for cc in combinations(range(1,n+1),k+1))
    S=max(options,key=score)
    p=verify_pair(S,k)
    assert uniform_upper(n,k,S)==p
    return p,S

def k2(n):
    S=(0,1,(n+1)//2,n)
    m=(n-1)**2//4
    return S,F(m,n+m)

def n_minus2(n):
    j=(n+1)//2
    return tuple(x for x in range(n+1) if x!=j),F(2,comb(n,n//2))

def example():
    n=31
    lo,hi=law_pair(k2(n)[0])
    qlo=F(1-lo[0],10); qhi=F(1,10)
    old_risk=lambda law: sum(p*F(comb(n,2)-comb(n-i,2),comb(n,2)) for i,p in law.items())/10
    r=old_risk(lo)
    assert r==old_risk(hi)==F(3,320)
    cap=F(1,20); q=(cap-r)/(qhi-r)
    assert q==F(13,29) and r+q*(qhi-r)==cap and qlo<cap
    gap=score(k2(n)[0])/10
    # The symmetric diagnostics after the mixture determine the same moments.
    # A tighter upper endpoint than qhi is impossible (it is itself feasible).
    assert qhi-qlo==gap
    return {"unknown_law_A":str(qlo),"unknown_law_B":str(qhi),
            "old_exposure_risk":str(r),"unchanged_mission_cap":str(cap),
            "robust_optional_bundle_probability":str(q),"fully_informed_A":1,
            "fully_informed_B":str(q)}

def main():
    exact={}
    for n in range(1,14):
        exact[n]=[str(support_search(n,k)[0]) for k in range(n+1)]
        assert exact[n][n-1]==str(F(1,2**(n-1)))
        if n>=2:
            assert exact[n][1]==str(F(n-1,n))
            assert exact[n][n-2]==str(n_minus2(n)[1])
        if n>=3:assert exact[n][2]==str(k2(n)[1])
    count=0
    for n in range(3,257):
        S,g=k2(n)
        assert verify_pair(S,2)==uniform_upper(n,2,S)==g
        count+=1
    for n in range(2,81):
        S,g=n_minus2(n)
        assert verify_pair(S,n-2)==uniform_upper(n,n-2,S)==g
        count+=1
    print(json.dumps({"all_orders_through_n":13,"pointwise_closed_formula_checks":count,
                      "curves":exact,"operational_example":example()},
                     sort_keys=True,indent=2))

if __name__=="__main__":main()
