from fractions import Fraction as F
from itertools import product
from math import comb
import json,math

def family(n,m):
    return [t for t in range(1<<n) if (t&1)==1 and t.bit_count()==m]

def check():
    n,k,m=6,2,3
    ts=family(n,m)
    d=len(ts)
    assert d==comb(n-1,m-1)==10 and m>k
    cells=list(range(1<<n))
    walsh=[[(-1)**((t&x).bit_count()%2) for x in cells] for t in ts]
    ns=0
    for sig in product((-1,1),repeat=d):
        num=[2*d+sum(a*w[x] for a,w in zip(sig,walsh)) for x in cells]
        z=sum(num)
        assert z==2*d*len(cells)
        p=[F(a,z) for a in num]
        assert min(p)>=F(1,2*len(cells))
        for j,w in enumerate(walsh):
            assert sum(a*b for a,b in zip(p,w))==F(sig[j],2*d)
            for rho in (F(1,10),F(1,2),F(1)):
                obs_mean=(1-rho)+rho*F(sig[j],2*d)
                assert 1-obs_mean**2<=3*rho
            ns+=1
    star=[]
    num=[2*d+sum(w[x] for w in walsh) for x in cells]
    z=sum(num)
    p0=[F(a,z) for a in num]
    for j,w in enumerate(walsh):
        alt=[F(a-2*b,z) for a,b in zip(num,w)]
        assert sum(alt)==1 and min(alt)>=F(1,2*len(cells))
        chi=sum((q-p)**2/p for q,p in zip(alt,p0))
        assert chi<=F(2,d*d)
        for rho in (F(1,10),F(1,2),F(1)):
            m0=[rho*p+(1-rho if x==0 else 0) for x,p in enumerate(p0)]
            m1=[rho*q+(1-rho if x==0 else 0) for x,q in enumerate(alt)]
            assert sum((q-p)**2/p for q,p in zip(m1,m0))<=rho*chi
        star.append(chi)
    rho=.1;delta=.25
    lower=d*d/(2*rho)*((1-delta)*math.log(d+1)-math.log(2))
    upper=80*d*d/(3*rho)*math.log(2*d/delta)
    return dict(d=d,exact_mean_and_variance_vectors=ns,star_alternatives=len(star),
                largest_active_chi_squared=str(max(star)),
                upper_chi_squared_bound=str(F(2,d*d)),
                illustrative_rho="1/10",illustrative_max_familywise_error="1/4",
                numeric_lower_ceiling=math.ceil(lower),numeric_sufficient_ceiling=math.ceil(upper))
if __name__=="__main__":
    print(json.dumps(check(),sort_keys=True,indent=2))
