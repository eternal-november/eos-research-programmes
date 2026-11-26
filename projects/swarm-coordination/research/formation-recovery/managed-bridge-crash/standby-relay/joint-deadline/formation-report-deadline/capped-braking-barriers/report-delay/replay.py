#!/usr/bin/env python3
"""Exact rational integration of two-world braking prefixes."""
from fractions import Fraction as Q
from itertools import product
import json


def integrate(w,a,ds,us,sign):
    """Replay one threatened span, with the endpoint at maximum correction."""
    v=w
    pos=high=Q(0)
    for dt,u in zip(ds,us,strict=True):
        dv=-a+sign*u
        dv_end=v+dv*dt
        if v>0 and dv_end<0:
            high=max(high,pos-v*v/(2*dv))
        pos+=dt*(v+dv_end)/2
        high=max(high,pos)
        v=dv_end
    return high if v<=0 else max(high,pos+v*v/(4*a))


def clip_at_first_contact(w,a,ds,us):
    """Trim overshoot using the same open-loop plan in both worlds."""
    k=Q(0)
    r=w
    remain=sum(ds)
    dnew=[]
    unew=[]
    for dt,u in zip(ds,us,strict=True):
        hits=[((r+sg*k)/(a-sg*u),sg)
              for sg in (-1,1) if a-sg*u>0]
        if hits:
            h,sg=min(hits)
            if h<dt:
                return dnew+[h,remain-h],unew+[u,sg*a]
        dnew.append(dt)
        unew.append(u)
        k+=u*dt
        r-=a*dt
        remain-=dt
    return dnew,unew


def moment_bounds(a,t,k):
    return -a*t*t/4+t*k/2+k*k/(4*a), a*t*t/4+t*k/2-k*k/(4*a)


def prefix_moments(ds,us):
    t=sum(ds)
    k=z=Q(0)
    for dt,u in zip(ds,us,strict=True):
        z+=u*dt*(t-dt/2)
        k+=u*dt
        t-=dt
    return k,z


def replay():
    all_paths=early_paths=late_paths=frontier_paths=clipping_checks=modified=0
    for w,a in product((Q(1,2),Q(1),Q(3,2)),(Q(1),Q(2))):
        for frac in (Q(0),Q(1,8),Q(1,4),Q(1,2),Q(3,4),Q(7,8),Q(1),Q(3,2)):
            t=frac*w/a
            th=min(t,w/a)
            L=w*t-a*t*t/2
            r=w-a*t
            bound=w*w/(4*a)+w*th/2-a*th*th/4
            ds=(t/8,t*3/8,t/4,t/4)
            for us in product((-a,-a/2,Q(0),a/2,a),repeat=4):
                k,z=prefix_moments(ds,us)
                zlo,zhi=moment_bounds(a,t,k)
                assert zlo<=z<=zhi
                A=integrate(w,a,ds,us,-1)
                B=integrate(w,a,ds,us,1)
                assert max(A,B)>=bound
                if t<=w/(2*a):
                    assert A==L-z+(r-k)**2/(4*a)
                    assert B==L+z+(r+k)**2/(4*a)
                    early_paths+=1
                else:
                    late_paths+=1
                if t<=w/a:
                    dc,uc=clip_at_first_contact(w,a,ds,us)
                    kc,zc=prefix_moments(dc,uc)
                    assert abs(kc)<=r
                    Ac=integrate(w,a,dc,uc,-1)
                    Bc=integrate(w,a,dc,uc,1)
                    assert Ac<=A and Bc<=B
                    assert Ac==L-zc+(r-kc)**2/(4*a)
                    assert Bc==L+zc+(r+kc)**2/(4*a)
                    clipping_checks+=1
                    modified+=(kc,zc)!=(k,z)
                all_paths+=1
            assert integrate(w,a,ds,[Q(0)]*4,-1)==bound
            assert integrate(w,a,ds,[Q(0)]*4,1)==bound
            for q in range(-8,9):
                k=a*t*q/8
                left=(t+k/a)/2
                _,limit=prefix_moments((left,t-left),(a,-a))
                _,floor=prefix_moments((t-left,left),(-a,a))
                assert (floor,limit)==moment_bounds(a,t,k)
                frontier_paths+=2
    # Holding one side exactly at its full-information limit forces its
    # preferred maximum action, raising the other side's required reserve.
    t=Q(1,4)
    assert integrate(Q(1),Q(1),(t,),(Q(1),),-1)==Q(1,4)
    assert integrate(Q(1),Q(1),(t,),(Q(1),),1)==Q(1,2)
    s=integrate(Q(1),Q(1),(t,),(Q(0),),1)
    assert s==Q(23,64) and 2*s==Q(1,4)+Q(15,32)
    return dict(segmented_prefixes=all_paths,early_prefixes=early_paths,
                late_prefixes=late_paths,exact_moment_endpoints=frontier_paths,
                clipped_prefix_checks=clipping_checks, prefixes_modified=modified,
                symmetric_named_threshold=str(s),
                same_total_asymmetric_budget=['1/4','15/32'],
                required_second_when_first_tight='1/2')


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
