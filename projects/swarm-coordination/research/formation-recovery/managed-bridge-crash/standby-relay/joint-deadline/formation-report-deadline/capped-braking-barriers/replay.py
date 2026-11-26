#!/usr/bin/env python3
"""Exact stopping-margin checks for independent speed and acceleration caps."""
from fractions import Fraction as Q
from itertools import product
import json


def pos(x):
    return max(Q(0),x)


def margins(v1,v2,a,A,V,W):
    assert 0<=v1<=W and 0<=v2<=V and 0<V<=W and 0<a<=A
    k=a+A
    w=pos(v1-v2)
    excess=pos(w-k*(V-v2)/A)
    return w*w/(2*k)+A*excess*excess/(2*a*k), pos(v2-v1)**2/(2*k)


def integrate_bounds(v1,v2,a,A,V,W):
    # Integrate extremal independent rates by splitting at all saturations
    # and every zero crossing of each relative-speed segment.
    tmax=max(v1/a,v2/A,(W-v1)/a,(V-v2)/A)
    pairs=[((v1,-a,0),(v2,A,V)),((v2,-A,0),(v1,a,W))]
    out=[]
    for (x,m,z),(y,n,s) in pairs:
        vx=lambda t:max(z,x+m*t)
        vy=lambda t:min(s,y+n*t)
        knots=sorted({Q(0),(z-x)/m,(s-y)/n,tmax})
        assert knots[0]==0 and knots[-1]==tmax
        value=Q(0)
        for low,high in zip(knots,knots[1:]):
            u,v=vx(low)-vy(low),vx(high)-vy(high)
            if u>0 and v>=0:
                value+=(u+v)*(high-low)/2
            elif u>0 and v<0:
                value+=u*u*(high-low)/(2*(u-v))
            # u<=0 implies v<=0 since this curve is nonincreasing.
            if u<=0:
                assert v<=0
        out.append(value)
    return tuple(out)



def three_gaps(a,w,v0,c1,c2):
    m=w*w/(4*a)
    if c1<m or c2<m or c1+c2<4*m:
        return False
    d1=max(m,4*m-c2)
    d2=4*m-d1
    alpha=(2*m-d1)/m
    assert -1<=alpha<=1 and d1<=c1 and d2<=c2
    T=w/a
    def speed(t):
        return v0+2*w-a*t,v0+w+alpha*a*min(t,T-t),v0+a*t
    absorb=[Q(0)]*2
    knots=(Q(0),T/2,T)
    for r,s in zip(knots,knots[1:]):
        u,v=speed(r),speed(s)
        assert u[0]>=u[1]>=u[2]>=0 and v[0]>=v[1]>=v[2]>=0
        assert all(abs(x-y)<=a*(s-r) for x,y in zip(u,v))
        for i in range(2):
            absorb[i]+=(s-r)*(u[i]-u[i+1]+v[i]-v[i+1])/2
    assert speed(T)==(v0+w,)*3 and absorb==[d1,d2]
    return True

if __name__=='__main__':
    checks=0
    for i,j,a,A,V,W in product(range(9),range(5),(1,2),(2,4),(1,2),(2,3)):
        vv1,vv2=Q(i,4),Q(j,4)
        tup=(vv1,vv2,Q(a),Q(A),Q(V),Q(W))
        assert margins(*tup)==integrate_bounds(*tup)
        checks+=1
    raw=(Q(1),Q(4),Q(1),Q(3))
    slow=margins(Q(1),Q(0),*raw)
    fast=margins(Q(2),Q(1),*raw)
    band=Q(3,10)
    assert slow[0]==Q(1,10) and fast[0]==Q(1,2) and slow[0]<=band<fast[0]
    # Pointwise link margin for the exact #508 shared prefix.
    early=[]
    for t in (Q(33,100),Q(35,100)):
        y=t-Q(1,8)-t*t/2
        cut=Q(1,5)-y-margins(t,Q(1),*raw)[1]
        assert y<Q(1,5)
        early.append(str(cut))
    assert early==["57/12500","-3/500"]
    assert not three_gaps(Q(1),Q(1),Q(0),Q(2,5),Q(2,5))
    assert three_gaps(Q(1),Q(1),Q(0),Q(1,4),Q(3,4))
    count=sum(three_gaps(Q(1),Q(1),Q(0),Q(a,10),Q(b,10))
        for a,b in product(range(11),repeat=2))
    print(json.dumps(dict(exact_extremal_integration_cases=checks,
       jointly_feasible_grid_budgets=count,grid_budget_pairs=121,
       pairwise_feasible_but_jointly_not=["2/5","2/5"],
       exact_joint_limit_pair=["1/4","3/4"],
       same_relative_speed="1",distance_to_clearance_limit="3/10",
       no_speed_cap_margin="1/10",low_common_speed_required=str(slow[0]),
       at_cap_required=str(fast[0]),latest_bit_margin_at_033_and_035=early),indent=2))
