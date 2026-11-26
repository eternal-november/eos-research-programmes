#!/usr/bin/env python3
"""Exact source-independent assembly of time and shared translation uncertainty."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import importlib.util
import json
from random import Random

spec=importlib.util.spec_from_file_location(
    'time_envelope',Path(__file__).resolve().parent.parent/'replay.py')
stn=importlib.util.module_from_spec(spec)
spec.loader.exec_module(stn)


def inside(p,hs):
    x,y=p
    return all(a*x+b*y<=c for a,b,c in hs)


def intersection(h1,h2):
    a,b,c=h1
    d,e,f=h2
    det=a*e-b*d
    return None if not det else (F(c*e-b*f,det), F(a*f-c*d,det))


def intersections(hs):
    for h1,h2 in combinations(hs,2):
        p=intersection(h1,h2)
        if p is not None:
            yield p


class Geometry:
    """Cache issued footprints, not an old calibration-support or time verdict."""
    def __init__(self,regions):
        self.regions=regions
        self.rows=tuple({r for region in regions for r in region})
        self.base={p:self.mask(p) for p in set(intersections(self.rows))}

    def mask(self,p):
        return tuple(i for i,zone in enumerate(self.regions) if inside(p,zone))

    def query(self,support):
        pts={p:I for p,I in self.base.items() if inside(p,support)}
        boundary=set(intersections(support))
        for r in support:
            for s in self.rows:
                p=intersection(r,s)
                if p is not None:
                    boundary.add(p)
        for p in boundary-pts.keys():
            if inside(p,support):
                pts[p]=self.mask(p)
        return pts


def fm(hs):
    # Independent feasibility oracle: eliminate y, then x; no vertices.
    co=[(a,c) for a,b,c in hs if b==0]
    plus=[(a,b,c) for a,b,c in hs if b>0]
    minus=[(a,b,c) for a,b,c in hs if b<0]
    for a,b,c in plus:
        for d,e,f in minus:
            co.append((-e*a+b*d,-e*c+b*f))
    lo=[];hi=[]
    for a,c in co:
        if a==0 and c<0:
            return False
        if a>0:
            hi.append(F(c,a))
        if a<0:
            lo.append(F(c,a))
    return not lo or not hi or max(lo)<=min(hi)


def shifted(site,point):
    x,y=point
    return [(a,b,c-a*x-b*y) for a,b,c in site]


def optimum(n,es,jobs,t,support,regions,prepared=None):
    d=stn.close(n,es)
    assert stn.sat(d)
    U=[i for i,j in enumerate(jobs) if stn.eligible(d,j,t)]
    reps={}
    if prepared is None:
        hs=list(support)+[h for i in U for h in regions[i]]
        pts={p for p in intersections(hs) if inside(p,support)}
        for p in sorted(pts):
            I=tuple(i for i in U if inside(p,regions[i]))
            reps.setdefault(I,p)
    else:
        eligible=set(U)
        for p,key in sorted(prepared.query(support).items()):
            I=tuple(i for i in key if i in eligible)
            reps.setdefault(I,p)
    assert reps
    value=-1
    for I,p in reps.items():
        v,S=stn.interval_method(d,[jobs[i] for i in I],t)
        if v>value:
            value=v
            claim=[I[i] for i in S]
            shift=p
    wit=stn.schedule(n,es+stn.bounds(jobs,claim,t))
    assert wit is not None
    realized=sum(w for i,(e,x,w) in enumerate(jobs)
                 if wit[e]<=t<wit[x] and inside(shift,regions[i]))
    assert realized==value
    return value,len(reps)


def baseline(n,es,jobs,t,support,regions):
    value=checks=0
    for k in range(len(jobs)+1):
        for S in combinations(range(len(jobs)),k):
            checks+=1
            h=list(support)+[row for i in S for row in regions[i]]
            if fm(h) and stn.schedule(n,es+stn.bounds(jobs,S,t)) is not None:
                value=max(value,sum(jobs[i][2] for i in S))
    return value,checks


def box(x0,x1,y0,y1):
    return [(1,0,x1),(-1,0,-x0),(0,1,y1),(0,-1,-y0)]


def replay():
    support=box(-4,4,-4,4)
    tray=box(0,1,0,1)
    j=[(2*i+1,2*i+2,1) for i in range(4)]
    es=[(x,e,-1) for e,x,w in j]+[(j[1][0],j[0][1],0),(j[3][0],j[2][1],0)]
    pos=[(0,0),(0,0),(3,0),(3,0)]
    zones=[shifted(tray,p) for p in pos]
    independent=stn.interval_method(stn.close(9,es),j,0)[0]
    geometry=optimum(9,[(x,e,-1) for e,x,w in j],j,0,support,zones)[0]
    combined=optimum(9,es,j,0,support,zones)[0]
    assert (independent,geometry,combined)==(2,2,1)
    assert all(fm(support+q) for q in zones)
    assert baseline(9,es,j,0,support,zones)[0]==1

    triangle=[(-1,0,0),(0,-1,0),(1,1,3)]
    z=[shifted(triangle,p) for p in [(0,0),(-2,0),(0,-2)]]
    assert all(fm(support+a+b) for a,b in combinations(z,2))
    assert not fm(support+z[0]+z[1]+z[2])
    simple=[(x,e,-1) for e,x,w in j[:3]]
    assert optimum(7,simple,j[:3],0,support,z)[0]==2
    less_spread=[shifted(triangle,p) for p in [(0,0),(-1,0),(0,-1)]]
    assert all(fm(support+a+b) for a,b in combinations(less_spread,2))
    assert optimum(7,simple,j[:3],0,support,less_spread)[0]==3

    # Two labelled calibration/schedule branches; their projections don't compose.
    one=j[:1]
    modes=[
        ([(2,1,-1),(0,1,0),(2,0,-1)],box(2,2,0,0)),
        ([(2,1,-1),(1,0,-1)],box(0,0,0,0)),
    ]
    assert max(optimum(3,E,one,0,K,[tray])[0] for E,K in modes)==0
    assert optimum(3,modes[0][0],one,0,box(0,2,0,0),[tray])[0]==1

    # Two closed regions that meet only on the boundary still jointly block.
    z=[shifted(tray,p) for p in [(0,0),(-1,-1)]]
    x=[(a,b,c) for a,b,c in support]+z[0]+z[1]
    assert {p for p in intersections(x) if inside(p,x)}=={(F(1),F(1))}
    assert optimum(5,simple[:2],j[:2],0,support,z)[0]==2
    assert optimum(5,simple[:2],j[:2],0,box(1,1,1,1),z)[0]==2

    R=Random(531532)
    subs=checked=masks=updates=0
    for it in range(300):
        m=R.randrange(1,8)
        n=2*m+1
        ticks=[0]+sum(([e,e+R.randrange(1,5)] for e in
                       (R.randrange(-5,6) for _ in range(m))),[])
        jobs=[(2*i+1,2*i+2,R.randrange(1,9)) for i in range(m)]
        es=[(x,e,-1) for e,x,w in jobs]
        es += [(a,b,ticks[b]-ticks[a]+R.randrange(3))
               for a in range(n) for b in range(n) if a!=b and R.random()<.21]
        sup=box(-R.randrange(4),R.randrange(4),-R.randrange(4),R.randrange(4))
        if it%2:
            sup+=[(R.randrange(-3,4),R.randrange(-3,4),R.randrange(5))]
        site=tray if it%3==0 else triangle
        zs=[shifted(site,(R.randrange(-5,6),R.randrange(-5,6))) for _ in jobs]
        prep=Geometry(zs)
        for t in (-4,0,4):
            v,c=optimum(n,es,jobs,t,sup,zs)
            u,s=baseline(n,es,jobs,t,sup,zs)
            assert v==u==optimum(n,es,jobs,t,sup,zs,prep)[0]
            newer=box(R.randrange(-4,1),R.randrange(5),R.randrange(-4,1),R.randrange(5))
            assert optimum(n,es,jobs,t,newer,zs)[0]==optimum(n,es,jobs,t,newer,zs,prep)[0]
            updates+=1
            masks+=c;subs+=s;checked+=1
    return {"sharp_joint_vs_marginal_loads":[combined,independent,geometry],
            "pairwise_but_not_triple_translation":True,"closed_corner_load":2,
            "branch_labels_matter":True,"support_update_checks":updates,"joint_checks":checked,"weight_subset_checks":subs,
            "distinct_masks_per_cut_summed":masks}


if __name__=='__main__':
    print(json.dumps(replay(),indent=2,sort_keys=True))
