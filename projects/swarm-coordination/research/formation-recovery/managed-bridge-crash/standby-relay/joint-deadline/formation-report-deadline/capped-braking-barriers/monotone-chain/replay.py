#!/usr/bin/env python3
"""Exact tangent witnesses for simultaneous braking in a monotone-speed chain."""
from fractions import Fraction as Q
from itertools import combinations,product
import json
import random


def need(u,v,a):
    assert u>=v
    return (u-v)**2/(4*a)


def pairs(v,z,a):
    return [(i,j) for i,j in combinations(range(len(v)),2)
            if z[j]-z[i] == need(v[i],v[j],a) and v[i]>v[j]]


def valid(v,z,a):
    return all(z[j]-z[i]>=need(v[i],v[j],a) for i,j in combinations(range(len(v)),2))


def tangent_ok(v,z,u,a,W):
    # Direct derivative tests at every active barrier, tie and speed cap.
    if any(abs(x)>a or (s==0 and x<0) or (s==W and x>0) for s,x in zip(v,u,strict=True)):
        return False
    if any(s==t and x<y for s,t,x,y in zip(v,v[1:],u,u[1:])):
        return False
    for i,j in combinations(range(len(v)),2):
        w=v[i]-v[j]
        if z[j]-z[i]==need(v[i],v[j],a):
            db=-w-w*(u[i]-u[j])/(2*a)
            if db<0:
                return False
    return True


def acceleration(v,z,a,W,exterior=False):
    assert a>0 and 0<W and all(0<=x<=W for x in v)
    assert all(v[i]>=v[i+1] for i in range(len(v)-1)) and valid(v,z,a)
    ep=pairs(v,z,a)
    plus={j for _,j in ep}
    minus={i for i,_ in ep}
    assert not plus&minus
    out=[Q(0)]*len(v)
    from itertools import groupby
    for _,items in groupby(range(len(v)),v.__getitem__):
        block=list(items)
        hi=max((i for i in block if i in plus),default=block[0]-1)
        lo=min((i for i in block if i in minus),default=block[-1]+1)
        assert hi<lo
        for i in block:
            out[i]=a if i<=hi else -a if i>=lo else Q(0)
    if exterior and v[0]>v[-1]:
        for i,s in enumerate(v):
            if s==v[0]:
                assert out[i]<=0
                out[i]=-a
            if s==v[-1]:
                assert out[i]>=0
                out[i]=a
    assert tangent_ok(v,z,out,a,W)
    return out,len(ep),len(plus)+len(minus)


def inverse_tight_cases():
    a,W=Q(1),Q(3)
    v=tuple(map(Q,[3,2,2,1]))
    good=tuple(map(Q,[0,Q(1,4),Q(3,4),1]))
    out,ep,_=acceleration(v,good,a,W)
    assert out==[-1,1,-1,1] and ep==3
    crossing=tuple(map(Q,[0,Q(1,10),Q(1,4),Q(7,20)]))
    assert set(pairs(v,crossing,a))=={(0,2),(1,3)}
    assert not valid(v,crossing,a)
    assert tangent_ok(v,good,out,a,W)
    tied_contact=[Q(0),Q(1,4),Q(1,4),Q(5,4)]
    assert acceleration(v,tied_contact,a,W)[0]==[-1,1,1,0]
    # Three adjacent pairs by themselves all pass; some skipped span fails.
    v2=tuple(map(Q,[3,2,1,0]))
    z2=[Q(i,2) for i in range(4)]
    assert all(z2[i+1]-z2[i]>=need(v2[i],v2[i+1],a) for i in range(3))
    assert not valid(v2,z2,a)
    return [str(o) for o in out]


def sampled_states():
    rng=random.Random(512)
    total=tight=with_ties=elective=brute=0
    for k in range(1800):
        n=rng.randrange(2,12)
        W,a=Q(4),Q(rng.choice((1,2,3)))
        v=sorted([Q(rng.randrange(9),2) for _ in range(n)],reverse=True)
        z=[Q(0)]
        for j in range(1,n):
            # Construct a feasible all-span prefix, balancing tight and loose states.
            plateau=max(z[i]+need(v[i],v[j],a) for i in range(j))
            z.append(plateau+Q(rng.choice((0,0,0,1,3)),8))
        us,nt,forced=acceleration(v,z,a,W)
        fast,_,_=acceleration(v,z,a,W,exterior=True)
        assert v[0]==v[-1] or (fast[0],fast[-1])==(-a,a)
        total+=1
        tight+=nt>0
        with_ties+=nt>0 and len(set(v))<len(v)
        elective+=nt>0 and sum(u!=0 for u in us)>forced
        if n<=6:
            assert any((v[0]==v[-1] or (u[0],u[-1])==(-a,a))
                       and tangent_ok(v,z,u,a,W) for u in product((-a,0,a),repeat=n))
            brute+=1
    return total,tight,with_ties,elective,brute


def exact_path():
    z=[Q(0),Q(1,4),Q(3,4),Q(1)]
    v=[Q(3),Q(2),Q(2),Q(1)]
    times=[Q(0),Q(1,2),Q(1),Q(3)]
    velocities=[v,[Q(5,2),Q(5,2),Q(3,2),Q(3,2)],[Q(2)]*4,[Q(0)]*4]
    for k,(t,s) in enumerate(zip(times,times[1:])):
        left,right=velocities[k:k+2]
        dt=s-t
        assert all(0<=q<=3 for q in left+right)
        assert all(left[i]>=left[i+1] and right[i]>=right[i+1] for i in range(3))
        assert all(abs(u-w)<=dt for u,w in zip(left,right))
        z=[x+dt*(u+w)/2 for x,u,w in zip(z,left,right)]
        assert valid(right,z,Q(1))
    assert z==[Q(9,2)]*4
    return dict(equalization_time=1, stop_time=3,
                final_shifted_positions=[str(x) for x in z])


def main():
    good=inverse_tight_cases()
    t,w,vt,extra,brute=sampled_states()
    assert t==1800 and extra==0 and brute>800
    print(json.dumps(dict(exact_source_states=t,
      with_tight_spans=w,with_tight_spans_and_velocity_ties=vt,
      tie_propagation_exceeding_forced_set=extra,
      brute_force_independent_tangent_checks=brute,named_tie_compatible_acceleration=good,
      exact_four_robot_stop=exact_path()),
      indent=2))


if __name__=='__main__':
    main()
