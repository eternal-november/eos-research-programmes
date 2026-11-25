"""Exact reachable inward travel with bounded acceleration and required rest."""
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import combinations

@dataclass(frozen=True)
class Side:
    speed: F
    vmax: F
    accel: F
    brake: F
    clearance: F
    anchor: F

def integrate(knots,fn):
    return sum(((fn(a)+fn(b))*(b-a)/2 for a,b in zip(knots,knots[1:])),F(0))

def envelope(s,T):
    assert 0<=s.speed<=s.vmax and s.accel>=0 and s.brake>0
    stop=s.speed/s.brake
    if T<stop:return None
    m=min(s.clearance,s.anchor)
    l=s.speed*stop/2
    if m<l:return None
    affine=((F(0),s.vmax),(s.accel,s.speed),(-s.brake,s.brake*T))
    ks={F(0),T,stop}
    for (a,c),(b,d) in combinations(affine,2):
        if a!=b and 0<=(x:=(d-c)/(a-b))<=T:ks.add(x)
    ks=sorted(ks)
    vmax=lambda t:min(s.vmax,s.speed+s.accel*t,s.brake*(T-t))
    vmin=lambda t:max(F(0),s.speed-s.brake*t)
    u=integrate(ks,vmax)
    return l,min(m,u),u,ks,vmin,vmax

def positive(s,T,travel):
    lo,hi,u,ks,vmin,vmax=envelope(s,T)
    assert lo<=travel<=hi
    alpha=(travel-lo)/(u-lo) if u>lo else F(0)
    vf=lambda t:(1-alpha)*vmin(t)+alpha*vmax(t)
    assert vf(F(0))==s.speed and vf(T)==0
    assert all(0<=vf(t)<=s.vmax for t in ks)
    assert all(-s.brake*(b-a)<=vf(b)-vf(a)<=s.accel*(b-a)
               for a,b in zip(ks,ks[1:]))
    assert integrate(ks,vf)==travel
    return ks,vf

def join(a,b,T,gap,radio):
    sa,sb=envelope(a,T),envelope(b,T)
    if sa is None or sb is None or sa[1]+sb[1]<gap-radio:
        return None
    return sa[1],sb[1]
