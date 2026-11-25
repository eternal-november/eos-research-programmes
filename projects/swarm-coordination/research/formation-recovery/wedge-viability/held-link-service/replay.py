"""Exact test for the scoped two-period, zero-velocity cancellation interface."""
from fractions import Fraction as Q
from itertools import product

def exact(gamma,h,R,live,target,D,dwell):
    s=h-1
    brake=min(h,D-dwell-h)
    if s<=0 or brake<=0 or live[1]<Q(1,2):
        return None
    lo=max(2*s*s,1+2*R,1-2*target[1])
    hi=min(s*s+s*brake,1-2*live[0],1-2*target[0])
    if gamma>1:hi=min(hi,2*gamma/(gamma-1))
    return (lo,hi) if lo<=hi else None

def motion(gamma,h,R,live,target,D,dwell,c):
    # Independent physical-time evaluation after choosing a held brake.
    if not 0<c<=1:return False
    s=h-1
    t=s/c
    if not 0<t<=h or h+t+dwell>D:return False
    x0=-(1+gamma)/2
    v1=1-h
    y1=h-h*h/2
    y2=y1+v1*t+c*t*t/2
    if v1+c*t != 0:return False
    # Each expression is affine in the common path coordinate. These
    # are every endpoint and derivative-zero extremum of its two arcs.
    ys=(Q(0),Q(1,2),y1,y2)
    for y in ys:
        x=x0+y
        if x+gamma*y>0 or x-gamma*y>0:return False
        # A real disk centered on the line; compare squared distances.
        center=sum(live)/2
        radius2=2*((live[1]-live[0])/2)**2
        if (x-(x0+center))**2+(y-center)**2>radius2:return False
    center=sum(target)/2
    radius2=2*((target[1]-target[0])/2)**2
    in_final=(y2-center)**2+(x0+y2-(x0+center))**2<=radius2
    return y2<=-R and in_final

def oracle(gamma,h,R,live,target,D,dwell):
    s=h-1
    if s<=0:return False
    y1=h-h*h/2
    cand={Q(0),Q(1),s/h}
    if D-dwell>h:cand.add(s/(D-dwell-h))
    # End-state predicates change truth only at these thresholds.
    walls=[-R,*live,*target]
    if gamma>1:walls.append(-(1+gamma)/(2*(gamma-1)))
    for y in walls:
        if y<y1:cand.add(s*s/(2*(y1-y)))
    bounds=sorted(v for v in cand if 0<=v<=1)
    probes=set(bounds)|{(a+b)/2 for a,b in zip(bounds,bounds[1:])}
    return any(motion(gamma,h,R,live,target,D,dwell,x) for x in probes)

tracks=[(Q(-2),Q(0)),(Q(-1),Q(1,2)),(Q(-7,10),Q(1,2)),(Q(-7,2),Q(2,5)),(Q(-3),Q(1))]
left=(Q(-7,10),Q(-1,2))
right=(Q(-1),Q(-4,5))
goals=[left,right,(Q(-5,2),Q(-1)),(Q(-5,4),Q(-1,2)),(Q(-1,4),Q(0))]
checks=passed=0
for gamma,h,R,live,target,delta,dwell in product(map(Q,(1,2,3,4)),map(Q,(1,Q(3,2),2,Q(5,2),3)),
        (Q(1,4),Q(1,2),Q(1)),tracks,goals,(Q(-2),Q(-1,4),Q(0),Q(1)),(Q(0),Q(1))):
    D=2*h+delta
    x=exact(gamma,h,R,live,target,D,dwell)
    truth=oracle(gamma,h,R,live,target,D,dwell)
    assert bool(x)==truth
    if x:
        for u in x:
            c=(h-1)**2/(u-(h-1)**2)
            assert motion(gamma,h,R,live,target,D,dwell,c)
        passed+=1
    checks+=1
print('exact intervals and independent whole-trajectory critical-cell allocator',checks,'cases;',passed,'feasible')
args=(Q(2),Q(2),Q(1,2),(Q(-1),Q(1,2)))
x=exact(*args,left,Q(5),Q(1))
y=exact(*args,right,Q(5),Q(1))
assert x==(Q(2),Q(12,5))
assert y==(Q(13,5),Q(3))
assert motion(*args,left,Q(5),Q(1),Q(1))
assert motion(*args,right,Q(5),Q(1),Q(1,2))
assert x[1]<y[0]
fixed=(args[1]-1)/args[1]
assert not motion(*args,left,Q(5),Q(1),fixed)
assert motion(*args,right,Q(5),Q(1),fixed)
assert exact(*args,right,Q(9,2),Q(1)) is None
print('near and far named terminal service U windows',x,y)
print('separate per-world feasible; one first common command cannot reach both without timely authority information')
print('fixed second hold works for far only; earlier deadline 4.5 rules out far even when its identity is known')
tight=(Q(-7,10),Q(1,2))
assert exact(Q(2),Q(2),Q(1,2),tight,left,Q(5),Q(1))
assert exact(Q(2),Q(2),Q(1,2),tight,right,Q(5),Q(1)) is None
print('tight old-link case can maintain the link and can reach the far terminal separately, but not both')
