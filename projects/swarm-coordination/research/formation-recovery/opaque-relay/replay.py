"""Exact rational controls for the single relay classifier and explicit chains."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

def le_surd(base, coefficient, radicand, upper):
    assert coefficient >= 0 and radicand >= 0
    d = upper - base
    return d >= 0 and d*d >= coefficient*coefficient*radicand

def relay(a,r,q,h,R2):
    assert 0 < r <= q < a and h >= 0 and R2 >= 0
    a,r,q,h,R2 = map(F,(a,r,q,h,R2))
    b = max(0,q*q-h*h)
    k = r*r/(a*a-r*r)
    base, coeff = a*a+b, 2*a
    return (le_surd(k*base,k*coeff,b,h*h)
            and le_surd(a*a+q*q,coeff,b,R2)
            and le_surd((1+k)*base,(1+k)*coeff,b,R2))

def dist2(p,q):
    return sum((x-y)**2 for x,y in zip(p,q))

def segment_dist2(p,q):
    u,v = (y-x for x,y in zip(p,q))
    norm = u*u+v*v
    t = F(0) if not norm else min(F(1),max(F(0),-(p[0]*u+p[1]*v)/norm))
    return (p[0]+t*u)**2+(p[1]+t*v)**2

def direct(p,a,r,q,h,R2):
    return (abs(p[1]) <= h and dist2(p,(0,0)) >= q*q
            and all(segment_dist2(p,t) >= r*r and dist2(p,t) <= R2
                    for t in [(-a,F(0)),(a,F(0))]))

def rational_sqrt(v):
    v=F(v)
    n,d=isqrt(v.numerator),isqrt(v.denominator)
    return F(n,d) if n*n==v.numerator and d*d==v.denominator else None

checks = [0,0,0]
for a,r in [(F(3),F(1)),(F(5),F(3)),(F(5),F(4)),(F(13),F(5))]:
    k2 = r*r/(a*a-r*r)
    for x,y in product((F(i,4) for i in range(-48,49)), repeat=2):
        p=(x,y)
        visible = all(segment_dist2(p,t) >= r*r for t in [(-a,F(0)),(a,F(0))])
        assert visible == (y*y >= k2*(a+abs(x))**2)
        checks[0] += 1

# Generate rational realizers when at the best lateral position. Check the
# classifier for thresholds on either side against exact independent segment checks.
for a,r in [(F(5),F(3)),(F(5),F(4)),(F(13),F(5))]:
    k=r/rational_sqrt(a*a-r*r)
    for q,h in product([r, (a+r)/2, (a+3*r)/4], [F(3), F(4), F(5), F(13), F(1)]):
        b = max(0,q*q-h*h)
        x = rational_sqrt(b)
        if x is None:
            continue
        y = max(k*(a+x), h if b else q)
        R2 = dist2((-a,0),(x,y))
        for delta in (-F(1,100),F(0),F(1,100)):
            assert relay(a,r,q,h,R2+delta)==direct((x,y),a,r,q,h,R2+delta)
            checks[1] += 1

# Rational-body cases with q>H and x*=3, z=4^2. For the second case the
# height cap fails even at unbounded range; it is not an actuator failure.
for a,r,expected in [(F(13),F(1),True),(F(13),F(5),False)]:
    assert relay(a,r,5,4,272)==expected
    assert direct((F(3),F(4)),a,r,5,4,272)==expected
    assert not relay(a,r,5,4,F(27199,100))
    checks[1]+=3

# The range-only one-relay model passes while the optical segment is blocked.
a,r,q,h,R2 = F(3),F(1),F(21,20),F(3,2),F(1011,100)
assert dist2((-a,0),(0,q)) <= R2
assert not relay(a,r,q,h,R2)
assert not direct((0,q),a,r,q,h,R2)
assert relay(a,r,q,h,F(81,8))
assert not relay(a,r,q,h,F(81,8)-F(1,10000))
checks[2]+=4

# Strictly more room than tangency for the two-relay path; the corridor
# height is smaller than the unavoidable one-relay visibility height.
a,r,q,h,R2=F(3),F(1),F(21,20),F(211,200),F(9)
p=(-F(3,2),F(21,20))
t=(F(3,2),F(21,20))
path=[(-a,F(0)),p,t,(a,F(0))]
assert not relay(a,r,q,h,F(10000))
assert all(abs(z[1]) <= h and dist2(z,(0,0)) >= q*q for z in path)
assert all(segment_dist2(u,v) > r*r and dist2(u,v) <= R2 for u,v in zip(path,path[1:]))
assert min(dist2(u,v) for i,u in enumerate(path) for v in path[i+1:]) >= F(1)
checks[2]+=4
# At the grazing height exactly two service positions remain. Check an
# explicit rightward semicircle at rational points through the middle.
a,r,q,h=F(5),F(3),F(15,4),F(15,4)
R2=(a+q)**2
assert relay(a,r,q,h,F(625,16))
assert not relay(a,r,q,h,F(625,16)-F(1,100))
arc_checks=0
for t in [F(i,400) for i in range(401)]:
    x,y=2*q*t/(1+t*t),q*(1-t*t)/(1+t*t)
    for yy in {y,-y}:
        assert x*x+yy*yy==q*q and abs(yy)<=h
        assert dist2((-a,0),(x,yy))<=R2
        assert direct((x,yy),a,r,q,h,R2)==(t==0)
        arc_checks+=1
assert dist2((-a,0),(q,0))==R2
print(json.dumps(dict(point_visibility_checks=checks[0], threshold_controls=checks[1], arc_samples=arc_checks,
                      explicit_masked_range_and_chain_controls=checks[2]),sort_keys=True))
