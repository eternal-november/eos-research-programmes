#!/usr/bin/env python3
"""Sharp epoch-offset intervals under a declared error/rate law, not a clock driver."""
from fractions import Fraction as Q
from itertools import product
import json
import random

from scipy.optimize import linprog


def compress(t, begin, finish):
    assert begin<=finish
    return t if t<=begin else begin if t<=finish else t-(finish-begin)


def constraints(begin,finish,admit,samples,prior):
    # Keep only evidence delivered by the admission cut. A future-in-time
    # sample cannot have arrived earlier, even if an inconsistent row says so.
    assert all(lo<=hi and source<=delivery for source,delivery,lo,hi in samples)
    kept=[(compress(t,begin,finish),a,b) for t,at,a,b in samples if at<=admit]
    return [(begin,*prior)]+kept


def interval(begin,finish,admit,samples,prior,rate):
    z=constraints(begin,finish,admit,samples,prior)
    if any(a>d+rate*abs(t-u) for (t,a,b),(u,c,d) in product(z,repeat=2)):
        return None
    lo=max(a-rate*abs(begin-t) for t,a,_ in z)
    hi=min(b+rate*abs(begin-t) for t,_,b in z)
    values=sorted({t for t,_,_ in z})
    # Construct each extremal trace on an independent finite knot set.
    for x in (lo,hi):
        ys={k:max(a-rate*abs(k-t) for t,a,b in z+[(begin,x,x)]) for k in values}
        assert ys[begin]==x
        assert all(a<=ys[t]<=b for t,a,b in z)
        assert all(abs(ys[k]-ys[l])<=rate*abs(k-l) for k,l in zip(values,values[1:]))
    return lo,hi


def lp(begin,finish,admit,samples,prior,rate):
    z=constraints(begin,finish,admit,samples,prior)
    times=sorted({p[0] for p in z})
    row=[]
    rhs=[]
    def coefs(*terms):
        a=[0]*len(times)
        for t,w in terms:
            a[times.index(t)]+=w
        return a
    def add(terms,b):
        row.append(coefs(*terms))
        rhs.append(float(b))
    for t,a,b in z:
        add(((t,1),),b)
        add(((t,-1),),-a)
    for t,u in zip(times,times[1:]):
        add(((t,1),(u,-1)),rate*(u-t))
        add(((t,-1),(u,1)),rate*(u-t))
    ans=[]
    for s in (1,-1):
        p=linprog(coefs((begin,s)),A_ub=row,b_ub=rhs,
            bounds=[(None,None)]*len(times),method='highs')
        if not p.success:
            assert p.status==2
            return None
        ans.append(s*p.fun)
    return tuple(ans)


def check_clock_class(z):
    if z is None: return "inconsistent"
    a,b=z
    return "affirmative" if a>=Q(3,4) else "negative" if b<Q(3,4) else "unknown"


def main():
    prior=(Q(0),Q(1))
    r=Q(1,10)
    one=[(8,8,Q(1,2),Q(1,2))]
    assert interval(0,4,8,one,prior,r)==(Q(1,10),Q(9,10))
    late=one+[(-1,9,Q(87,100),Q(91,100))]
    assert interval(0,4,8,late,prior,r)==interval(0,4,8,one,prior,r)
    timely=one+[(-1,8,Q(87,100),Q(91,100))]
    two=interval(0,4,8,timely,prior,r)
    assert two==(Q(77,100),Q(9,10))
    bad=[(0,5,Q(1,10),Q(1,10)),(4,5,Q(3,10),Q(3,10))]
    assert interval(0,4,8,bad,prior,r) is None
    rng=random.Random(502)
    cases=320
    passes=0
    for k in range(cases):
        rate=Q(rng.randrange(6),10)
        rows=[]
        for j in range(rng.randrange(1,8)):
            t=rng.randrange(-8,14)
            delivery=t+rng.randrange(0,5)
            y=Q(rng.randrange(-20,40),10)
            eps=Q(rng.randrange(9),10)
            rows.append((t,delivery,y-eps,y+eps))
        exact=interval(0,4,8,rows,prior,rate)
        other=lp(0,4,8,rows,prior,rate)
        assert (other is None)==(exact is None)
        if exact:
            passes+=1
            assert all(abs(float(a)-b)<1e-8 for a,b in zip(exact,other))
    as_list=lambda xs: list(map(str,xs))
    first=interval(0,4,8,one,prior,r)
    print(json.dumps(dict(cases=cases,feasible=passes,one_current_sample=as_list(first),
        one_current_class=check_clock_class(first),late_measure_usable=False,
        bracketed_at_cut=as_list(two),bracketed_class=check_clock_class(two),
        inconsistent_epoch=check_clock_class(None)),indent=2))


if __name__=='__main__':
    main()
