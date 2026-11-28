"""Controllable reentry after a local physical release, not a deployed policy."""
from pathlib import Path
from fractions import Fraction as F
import json,sys,ast
from math import isqrt

def lower_sqrt(n):
    fac=10**15
    return F(isqrt(n*fac**2),fac)

def upper_sqrt(n):
    return lower_sqrt(n)+F(1,10**15)

def floor(x):return x.numerator//x.denominator
def play(hold,path,box,axis,chord):
    src,dst=path[chord+1],path[chord]
    n=sum((a-b)**2 for a,b in zip(src,dst))
    leg=lower_sqrt(n); legmax=upper_sqrt(n)
    direction=1 if dst[axis]>src[axis] else -1
    assert axis==min(range(3),key=lambda k:box[1][k]-box[0][k])
    plane=box[direction==1][axis]
    fraction=(plane+direction*F(302,1000)-src[axis])/(dst[axis]-src[axis])
    assert min(fraction,1-fraction)*leg>F(1,5)
    coords=[a+fraction*(b-a) for a,b in zip(src,dst)]
    assert all(box[0][k]+F(1,5)<coords[k]<box[1][k]-F(1,5)
               for k in range(3) if k!=axis)
    # One metre per second along the original outward certified chord.
    component=F(abs(src[axis]-dst[axis]))
    lo=component/legmax
    hi=component/leg
    assert 0<lo<=hi<1
    acc=F(5); effect=F(1,4)
    # Global model uses at most 5 m/s^2 acceleration norm; for any
    # continuation this limits adverse signed normal acceleration.
    def lower(t):return lo*t-acc*t*t/2
    horizon=2*lo/acc
    cap=floor((horizon-effect)*10**6)
    assert lower(F(1,100))>0 and lower(F(26,100))>0
    assert F(cap,10**6)+effect<horizon<=F(cap+1,10**6)+effect
    # Construct an actual allowed collinear reversal after the report:
    # v=1-5t until -1 at .4s and -1 thereafter, all with |v|<=1.
    def along(t):
        if t<=F(2,5):return t-5*t*t/2
        return -(t-F(2,5))
    t_hit=F(401,1000)
    assumed_positive_margin=F(1,10**6)
    assert assumed_positive_margin+lo*along(t_hit)<0
    assert F(175,1000)<t_hit<F(175,1000)+effect
    # Counter-world with identical sensed center but no measured
    # outward momentum. Accelerate directly toward the plane along
    # the certified chord. Contact occurs during even the short hold.
    t0=F(11,1000)
    assert 5*t0<1 and assumed_positive_margin+lo*(-F(5,2)*t0*t0)<0
    assert F(1,100)<t0<F(1,100)+effect
    # Assert these displacements are near the actual returning
    # crossing, well inside the same physical chord.
    assert leg>10 and abs(along(t_hit))<F(1,10)
    assert hold['cores'][1][1]-hold['cores'][1][0]>500_000
    return dict(gate=hold['gate'],normal_speed_bound=[round(float(lo),9),round(float(hi),9)],
        min_reentry_horizon_bound_us=floor(horizon*10**6),max_certified_delay_us=cap,
        timely_10ms_lease_with_velocity=True,timely_10ms_clearance_only_counterexample=True,
        allowed_collinear_reentry_in_175ms_delayed_closure=True)
root=Path(sys.argv[1])
t=ast.parse((root/'ride.py').read_text())
d=next(a.value for a in t.body if isinstance(a,ast.Assign) and
       [x.id for x in a.targets if isinstance(x,ast.Name)]==["closures"])
slabs={ast.literal_eval(k):tuple(tuple(F(ast.literal_eval(x.args[0])) for x in j.elts)
                                  for j in v.elts) for k,v in zip(d.keys,d.values)}
p=json.loads((root/'paths.json').read_text())
for x,line in enumerate((root/'PORTAL.jsonl').read_text().splitlines()):
    print(json.dumps(play(json.loads(line),p['AB'[x]]['polyline'],
                          slabs[((117,132),(118,132))[x]],x,(4,5)[x]),sort_keys=True))
