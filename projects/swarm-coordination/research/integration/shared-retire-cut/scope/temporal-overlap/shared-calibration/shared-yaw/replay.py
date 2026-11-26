#!/usr/bin/env python3
"""Common SE(2) calibration, independent integer timing; all decisions exact."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from random import Random
import importlib.util,json
from phase import add,sub,mul,phases,sign

spec=importlib.util.spec_from_file_location(
    'linear_calibration',Path(__file__).resolve().parent.parent/'replay.py')
linear=importlib.util.module_from_spec(spec)
spec.loader.exec_module(linear)
stn=linear.stn
Z=(0,0,0)
def cap(a,b,c): # a*cos(theta)+b*sin(theta)<=c
    return c-a,-2*b,c+a
def lift(support):
    return [(a,b,(c,0,c)) for a,b,c in support]
def shifted(region,u):
    x,y=u
    return [(a,b,cap(a*x+b*y,b*x-a*y,c)) for a,b,c in region]
def corner(r,s):
    a,b,c=r
    d,e,f=s
    det=a*e-b*d
    if det:
        k=F(1,det)
        return mul(k,sub(mul(e,c),mul(b,f))),mul(k,sub(mul(a,f),mul(d,c)))
def residual(row,p):
    a,b,c=row
    x,y=p
    return sub(c,add(mul(a,x),mul(b,y)))
def masks(K,regions,angles):
    rows=tuple(set(K+sum(regions,[])))
    cs={p for r,s in combinations(rows,2) if (p:=corner(r,s)) is not None}
    out=set()
    for p in cs:
        rs=[*[residual(h,p) for h in K],*angles]
        ys=[[residual(h,p) for h in G] for G in regions]
        for t in phases(rs+sum(ys,[])):
            if all(sign(poly,t)>=0 for poly in rs):
                out.add(tuple(i for i,v in enumerate(ys) if all(sign(poly,t)>=0 for poly in v)))
    return out
def fm_rhs(rows):
    # Eliminate y, then x; coefficient of each eliminated variable is constant.
    qs=[(a,c) for a,b,c in rows if b==0]
    lo=[r for r in rows if r[1]<0]
    hi=[r for r in rows if r[1]>0]
    for a,b,c in hi:
        for d,e,f in lo:
            qs.append((-e*a+b*d,add(mul(-e,c),mul(b,f))))
    out=[c for a,c in qs if a==0]
    for a,c in qs:
        if a>0:
            for b,d in qs:
                if b<0:
                    out.append(add(mul(-b,c),mul(a,d)))
    return out
def exact(K,regions,angles):
    p=fm_rhs(K+sum(regions,[]))+angles
    return any(all(sign(poly,t)>=0 for poly in p) for t in phases(p))

def test():
    R=Random(532533)
    checked=subs=0
    for i in range(36):
        m=R.randint(1,5)
        jobs=[(2*j+1,2*j+2,R.randrange(1,6)) for j in range(m)]
        es=[(x,e,-1) for e,x,_ in jobs]
        es += [(jobs[b][0],jobs[a][1],0) for a,b in combinations(range(m),2)
               if R.random()<.25]
        n=2*m+1
        d=stn.close(n,es)
        K=lift(linear.box(-1,1,-1,1) if i%2 else linear.box(0,0,0,0))
        site=linear.box(0,1,0,1) if i%3 else [(-1,0,0),(0,-1,0),(1,1,2)]
        regions=[shifted(site,(R.randrange(-2,3),R.randrange(-2,3))) for j in jobs]
        angles=[[cap(1,1,1)], [cap(1,0,0),cap(-1,0,0)], [cap(1,0,1)], []][i%4]
        S=masks(K,regions,angles)
        assert S
        v=max(stn.interval_method(d,[jobs[j] for j in s],0)[0] for s in S)
        b=0
        for k in range(m+1):
            for s in combinations(range(m),k):
                seen=any(set(s)<=set(u) for u in S)
                feasible=exact(K,[regions[j] for j in s],angles)
                assert seen==feasible
                subs+=1
                if feasible and stn.schedule(n,es+stn.bounds(jobs,s,0)) is not None:
                    b=max(b,sum(jobs[j][2] for j in s))
        assert v==b
        checked+=1
    still=lift(linear.box(0,0,0,0))
    # Only cos=1/2 on the upper semicircle works: irrational finite t.
    tangent=shifted(linear.box(F(1,2),F(1,2),0,1),(1,0))
    ys=masks(still,[tangent],[])
    assert (0,) in ys and () in ys
    assert exact(still,[tangent],[])
    intcap=[cap(0,1,0),cap(0,-1,0),cap(1,0,-1)]
    # All finite tangent parameters excluded: the omitted -x direction matters.
    assert masks(still,[shifted(linear.box(-1,-1,0,0),(1,0))],intcap)=={(0,)}
    bounds={}
    for n in (4,8,16):
        # One shared footprint, a fixed narrow arc, no translation.
        arc=[cap(-1,0,F(-15,17)),cap(0,-1,0)]
        cell=linear.box(-1,1-F(1,16*(n-1)**2),-1,1)
        jobs=[]
        for i in range(n):
            t=F(i,4*(n-1))
            jobs.append(shifted(cell,((1-t*t)/(1+t*t),-2*t/(1+t*t))))
        have=masks(still,jobs,arc)
        allids=set(range(n))
        assert tuple(range(n)) not in have
        assert all(tuple(sorted(allids-{j})) in have for j in allids)
        assert not exact(still,jobs,arc)
        for j in allids:
            assert exact(still,jobs[:j]+jobs[j+1:],arc)
        bounds[n]=max(map(len,have))
    return dict(scene_checks=checked,subset_checks=subs,
                isolated_irrational_direction=True,isolated_omitted_direction=True,
                minimal_conflict_sizes=list(bounds),max_loads=list(bounds.values()))

if __name__=='__main__':
    print(json.dumps(test(),indent=2,sort_keys=True))
