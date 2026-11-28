"""Exact finite clock translation from echo brackets, no assumed symmetric delay."""
from fractions import Fraction as F
from itertools import combinations
import json,sys
from pathlib import Path

def ceil(x):return -((-x.numerator)//x.denominator)

def feasible(anchor, bins, radius):
    # For gate timestamp g, t(g)=anchor+u*(g-anchor)+v.
    # All constraints are nonstrict => a bounded closed polygon; include
    # rank-one / point degeneracy via line-intersection vertices too.
    constraints=[(F(1),F(0),1+radius),(-F(1),F(0),radius-1)]
    for a,g,b in bins:
        x=g-anchor
        constraints.extend([(x,F(1),b-anchor),(-x,-F(1),anchor-a)])
    out=set()
    for (a,b,c),(d,e,f) in combinations(constraints,2):
        q=a*e-b*d
        if q:
            u,v=(c*e-b*f)/q,(a*f-c*d)/q
            if all(m*u+n*v<=r for m,n,r in constraints):
                out.add((u,v))
    assert all(u>0 for u,v in out)
    return out

def interval(anchor, stamp, support):
    if not support:return None
    real=[anchor+u*(stamp-anchor)+v for u,v in support]
    return min(real),max(real)

def end_side_clear(anchor, stamp, support, end):
    # First integer gate tick with world-time lower bound at least the
    # first certified integer instant after the held interval.
    if not support:return None
    cert=ceil(max(anchor+(end+1-anchor-v)/u for u,v in support))
    return max(0,cert-stamp)

def play(raw):
    ret=raw['hulls'][1][1];i,j=raw['cores'][1]
    stamp=ret+10000; high=ret+1
    anchor=stamp-250_000_000
    r=F(1,5000)
    old=[(anchor-3000,anchor,anchor+3000),
         (anchor+50_000_000-12000,anchor+50_000_000,anchor+50_000_000+12000)]
    kw=feasible(anchor,old,r)
    unit=feasible(anchor,old,F(0))
    assert kw and unit
    t=interval(anchor,stamp,kw)
    tru=[(1-r,F(0)),(1+r,F(0))]
    for u,v in tru:
        assert all(a<=anchor+u*(g-anchor)+v<=b for a,g,b in old)
    true_times=[anchor+u*(stamp-anchor)+v for u,v in tru]
    assert i<=true_times[0]<=j and true_times[1]>ret
    assert t[0]<=true_times[0]<=true_times[1]<=t[1]
    assert interval(anchor,stamp,unit)[0]>ret  # false admit in early world
    # New exchange is physically performed near the use time.
    # Master send/receive fixed; the returned gate timestamp is a
    # different value by the law R^-1 at the same physical echo time.
    target=stamp-10_000_000
    fresh=[]
    for u,v in tru:
        gate=anchor+(target-anchor-v)/u
        raw_bins=old+[(target-2500,gate,target+2500)]
        known=feasible(anchor,raw_bins,r)
        assert known
        w=interval(anchor,stamp,known)
        assert w[0]<=anchor+u*(stamp-anchor)+v<=w[1]
        fresh.append(w[0]>ret)
    assert fresh==[False,True]
    wait=end_side_clear(anchor,stamp,kw,ret)
    assert wait>0
    assert interval(anchor,stamp+wait,kw)[0]>=high
    assert interval(anchor,stamp+wait-1,kw)[0]<high
    # A later gate reading whose compatible offsets/rates are impossible
    # must not be interpreted as vacuous proof of disjointness.
    ghost=old+[(stamp,stamp+2_000_000,stamp+1)]
    assert end_side_clear(anchor,stamp,feasible(anchor,ghost,r),ret) is None
    return dict(gate=raw['gate'],old_support_vertices=len(kw),unknown_release_bracket_us=[str(x) for x in t],
                true_effect_starts=[int(x) for x in true_times],both_worlds_same_old_echo=True,
                constant_clock_unsafe_worlds=1,near_echo_decisions=fresh,first_safe_wait_gate_us=wait)
if __name__=='__main__':
    for line in (Path(sys.argv[1])/'PORTAL.jsonl').read_text().splitlines():
        print(json.dumps(play(json.loads(line)),sort_keys=True))
