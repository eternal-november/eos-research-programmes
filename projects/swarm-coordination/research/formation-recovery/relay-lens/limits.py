"""Restricted control-family refinements, separate from unrestricted feasibility."""
from math import acos, asin, atan2, hypot, sin, sqrt, tan, pi
from scipy.optimize import brentq,minimize_scalar
from random import Random

def unequal_suffix(b,c,rho,h):
    d1,d2=hypot(h,c),hypot(b,c)
    assert d1>=rho-1e-12 and d2>=rho and c<rho
    t1=atan2(h,c)-acos(min(1,rho/d1))
    t2=atan2(b,c)-acos(rho/d2)
    return sqrt(max(0,d1*d1-rho*rho))+sqrt(d2*d2-rho*rho)+rho*(t1+t2)

def vertical_arrival(t,b,c,rho,v):
    # Safe common vertical progress can continue until the common line
    # touches both disks; we then wait at the deepest feasible point.
    z=sqrt(rho*rho-c*c)
    return t+unequal_suffix(b,c,rho,max(z,b-v*t))/v

def optimal_rho(b,r0,r1,v,acc):
    angle=brentq(lambda t:t*tan(t)-1,1e-8,pi/2-1e-8)
    return min(r1,max(r0,min(b*sin(angle),v*v/acc)))

def travel_time(r,b,v,acc):
    return (2*sqrt(b*b-r*r)+2*r*asin(r/b))/min(v,sqrt(acc*r))

if __name__=='__main__':
    a,R,c,r,b=3,5,.5,1.75,3.5
    for t in (0,1,1.75,2,3):
        print('sign at',t,'optimal causal completion',round(vertical_arrival(t,b,c,r,1),9))
    D=9
    T=brentq(lambda t:vertical_arrival(t,b,c,r,1)-D,0,D)
    print('exact latest sign time under the speed-only law by',D,round(T,9))
    rr=optimal_rho(3.5,1,2,4,1)
    print('required clearance 1; best constant-speed tangent-arc radius',rr,
          'time',round(travel_time(rr,3.5,4,1),9),
          'vs minimum-radius time',round(travel_time(1,3.5,4,1),9))
    rng=Random(2461)
    for _ in range(100):
        b=rng.uniform(2,20);l=b*rng.uniform(.02,.45);u=b*rng.uniform(.5,.95)
        v=rng.uniform(.1,5);acc=rng.uniform(.05,3)
        rr=optimal_rho(b,l,u,v,acc)
        f=lambda z:travel_time(z,b,v,acc)
        g=minimize_scalar(f,bounds=(l,u),method='bounded')
        assert abs(f(rr)-min(f(l),f(u),g.fun))<.001
    print('100 constant-speed/curvature choices agree with bounded numerical optimization')
