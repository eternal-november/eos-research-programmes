"""Exact checks of selectively observed anonymous handoff experiments."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from random import Random

def parity(bits):
    return sum(bits) % 2

OPTIONS = {1:(F(1,10),F(1)), 2:(F(1,4),F(1,3))}

def source(n,s):
    for x in product(range(2),repeat=n):
        if parity(x)==s:
            yield x,F(1,2**(n-1))

def leaves(n,s,policy,noise=None):
    out=defaultdict(F)
    # This enumerates source states, plant reads and actual faults.
    for x,px in source(n,s):
        if noise is None:
            def emit(i,prefix,weight):
                if i==n:
                    out[prefix]+=weight
                    return
                u=policy[i,prefix]
                if u==0:
                    emit(i+1,prefix+((0,-1),),weight)
                else:
                    f,_=OPTIONS[u]
                    for z,q in [(0,1-f),(1,f)]:
                        emit(i+1,prefix+((u,x[i]^z),),weight*q)
            emit(0,(),px)
        else:
            for z,pz in noise.items():
                prefix=()
                for i in range(n):
                    u=policy[i,prefix]
                    prefix+=((u,x[i]^z[i] if u else -1),)
                out[prefix]+=px*pz
    return out

def make_policy(n,rng,passive):
    options=((0,-1),(1,0),(1,1),(2,0),(2,1))
    return {(i,prefix):(0 if i==passive else rng.randrange(3))
            for i in range(n) for prefix in product(options,repeat=i)}

def direct_checks(n,policy):
    p,q=(leaves(n,i,policy) for i in range(2))
    tv=sum(abs(p[k]-q[k]) for k in (p.keys()|q.keys()))/2
    # Enumerate only fair readouts, as if local sensor replies give
    # fair independent bits. The likelihood correction is needed only
    # when every stage was actually inspected.
    expected_cost=expected_information=F(0)
    def loop(i,prefix,w,cost,rel):
        nonlocal expected_cost,expected_information
        if i==n:
            expected_cost+=w*cost
            expected_information+=w*rel
            return
        u=policy[i,prefix]
        if u==0:
            loop(i+1,prefix+((0,-1),),w,cost,F(0))
        else:
            f,charge=OPTIONS[u]
            for y in (0,1):
                loop(i+1,prefix+((u,y),),w/2,cost+charge,rel*(1-2*f))
    loop(0,(),F(1),F(0),F(1))
    costs=[]
    for D in (p,q):
        costs.append(sum(w*sum(OPTIONS[u][1] for u,y in k if u) for k,w in D.items()))
    assert sum(p.values())==sum(q.values())==1
    assert tv==expected_information and costs==[expected_cost]*2
    err0=sum(w for k,w in p.items() if all(u for u,y in k) and parity(y for u,y in k))
    err1=sum(w for k,w in q.items() if all(u for u,y in k) and not parity(y for u,y in k))
    for k in p.keys()|q.keys():
        if any(not u for u,y in k):
            assert p[k]==q[k]
            err0+=p[k]/2
            err1+=q[k]/2
    assert err0==err1==(1-tv)/2
    return tv

def main():
    rng=Random(9176202); count=0
    for n in range(2,7):
        for it in range(80):
            passive=it%n if it%2 else -1
            policy=make_policy(n,rng,passive)
            tv=direct_checks(n,policy)
            if passive>=0:
                assert tv==0
            count+=1
    # Two simultaneous scans have the same individual error rates in
    # these mechanisms. With a common slip, both identities reverse.
    full={(i,k):1 for i in range(2) for k in product(((1,0),(1,1)),repeat=i)}
    common={(0,0):F(9,10),(1,1):F(1,10)}
    ps=[leaves(2,s,full,common) for s in (0,1)]
    common_tv=sum(abs(ps[0][k]-ps[1][k]) for k in (ps[0].keys()|ps[1].keys()))/2
    assert common_tv==1 and direct_checks(2,full)==F(16,25)
    # Given the two 10% marginals, the joint probability of two
    # flips ranges from zero to 1/10. Scan outcomes cannot justify
    # substituting the independent product for that range.
    for k in range(101):
        both=F(k,1000)
        noise={(0,0):F(4,5)+both,(0,1):F(1,10)-both,
               (1,0):F(1,10)-both,(1,1):both}
        ps=[leaves(2,s,full,noise) for s in (0,1)]
        tv=sum(abs(ps[0][k]-ps[1][k]) for k in (ps[0].keys()|ps[1].keys()))/2
        assert (1-tv)/2==F(1,5)-2*both
    def price(u):
        c=sum(OPTIONS[a][1] for a in u)
        r=F(1)
        for a in u:r*=1-2*OPTIONS[a][0]
        return c+10*(1-r)/2
    assert [price(u) for u in ((1,1),(1,2),(2,2))]==[F(19,5),F(13,3),F(53,12)]
    assert 5-min(price(u) for u in product((1,2),repeat=2))==F(6,5)
    print(count,"adaptive scan policies agree with exact source-history enumeration")
    print("200 forced missing-stage policies are exactly non-identifying")
    print("two 10%-error scans: independent parity TV=16/25; common-slip parity TV=1")
    print("101 coupled calibrations match error range [0,1/5]; independence gives 9/50")
    print("foregone job value cutoff=6/5 (independent scans, loss=10)")

if __name__=="__main__":
    main()

