from decimal import Decimal as D, getcontext
from itertools import product
from pathlib import Path
from hashlib import sha1
from xml.etree.ElementTree import parse
import re,math
getcontext().prec=65
P=Path(__file__).resolve().parent
for line in (P/'PINS.tsv').read_text().splitlines():
    n,_,_,_,h=line.split('\t')
    b=(P/n).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
helper=(P/'ConnectionHelper.cc').read_text()
assert 'pt1tf.Equal(pt2tf, 1.5)' in helper
sdf=parse(P/'world.sdf')
byname={x.findtext('name'):x for x in sdf.findall('.//include')}
def mouth(tile):
    i=byname[f'tile_{tile}']
    typ=i.findtext('uri').split('/models/')[1]
    row=next(l for l in helper.splitlines() if f'{{"{typ}", {{' in l)
    xyz=[tuple(map(float,x)) for x in re.findall(r'\{([-\d.]+), ([-\d.]+), ([-\d.]+)\}',row)]
    xc,yc,zc,roll,pitch,yaw=map(float,i.findtext('pose').split())
    assert roll==pitch==0
    return [(xc+math.cos(yaw)*x-math.sin(yaw)*y,
             yc+math.sin(yaw)*x+math.cos(yaw)*y,zc+z) for x,y,z in xyz]
joins=[(a,b) for a,b in product(mouth(13),mouth(42))
       if all(abs(u-v)<=1.5 for u,v in zip(a,b))]
assert len(joins)==1 and joins[0][0]==(100,62.5,0)
assert 0<math.dist(*joins[0])<0.000035

# Analytic quotient: intentionally authored lumen, gate, marker, and vehicle.
# x=0 is center 13; x=25 is nominal center 42. Decimal arithmetic is a
# replay of the real formulas with a tolerance, not their proof.
eps=D('1e-56')
def close(a,b): return abs(a-b)<eps
def leg(x,v,a,V):
    assert x>=0 and 0<=v<=V and v*v<=2*a*x+eps
    p=min(V,(a*x+v*v/2).sqrt())
    coast=max(D(0),x-(2*p*p-v*v)/(2*a))
    return [(p/a,a),(coast/p if p else D(0),D(0)),((p-v)/a,-a)]
def apply(x,v,h):
    for t,a in h:
        assert t>=-eps
        x+=v*t+a*t*t/2
        v+=a*t
    return x,v
def total(h): return sum(t for t,_ in h)
def durations(d,v,L,A,V,S):
    pre=leg(d,v,A,V)
    assert all(close(a,b) for a,b in zip(apply(D(0),D(0),pre),(d,v)))
    rev=[(t,-a) for t,a in leg(d+v*v/(2*A),D(0),A,V)]
    back=[(v/A,-A)]+rev
    assert all(close(a,b) for a,b in zip(apply(d,v,back),(D(0),D(0))))
    far=[(t,-a) for t,a in reversed(leg(L-d,v,A,V))]
    assert all(close(a,b) for a,b in zip(apply(d,v,far),(L,D(0))))
    assert d+v*v/(2*A)<=S+eps
    return total(pre),total(pre)+total(far),total(pre)+total(back)
def scan(A,V,S=12,L=25):
    m=0
    for dx in range(1,25):
        d=D(dx)/2
        vmax=min(V,(2*A*d).sqrt(),(2*A*(S-d)).sqrt())
        old=None
        for z in range(65):
            v=vmax*z/64
            pos=durations(d,v,D(L),A,V,S)
            if old:
                assert pos[0]<=old[0]+eps and pos[1]<=old[1]+eps and pos[2]>=old[2]-eps
            m+=1;old=pos
    return m
p=durations(D(8),D(2),D(25),D(1),D(3),D(12))
assert all(close(u,v) for u,v in zip(p,(D(13)/3,D(35)/3,D(38)/3)))
assert durations(D(8),D(0),D(25),D(1),D(3),D(12))[0]>5
# At the peak transition sqrt(2), both capped formulas agree. The far
# deadline needs v>=3-sqrt(2)>sqrt(2), then the near bound is violated.
sqrt2=D(2).sqrt()
assert 3-sqrt2>sqrt2
boundary=durations(D(8),+sqrt2,D(25),D(1),D(3),D(12))
assert close(boundary[2],D(12)) and boundary[1]>12
checks=sum(scan(D(a),D(v)) for a,v in product((1,2,3),(2,3,4)))

# Ideal positive returns in a proved authored rectangular beam tube at d=8.
# Coarse bounds cover all emitter offsets/slopes, extrema checked as well.
# Open target x=14, closed gate x=12.5. Keep origin y ±.1 and z .7 .. 1.1;
# lateral ray slope is .14 .. .17; vertical slope is bounded by .02.
ray=0
for y,z,h,k in product((D('-.1'),D('.1')),(D('.7'),D('1.1')),
                       (D('.14'),D('.17')),(D('-.02'),D('.02'))):
    for dx in (D(0),D('4.5'),D(6)):
        Y=y+h*dx;Z=z+k*dx
        assert abs(Y)<D('1.3') and D('.5')<Z<D('1.4')
        if dx==6: assert D('.7')<Y<D('1.2')
        norm=(1+h*h+k*k).sqrt()
        # The inclusive measurement intervals are disjoint and fit range 6.2.
        assert D('4.5')*norm+D('.05')<D('5')
        assert D(6)*norm-D('.05')>D('5')
        assert D(6)*norm+D('.05')<D('6.2')
        ray+=1
print('unique compiled-design mouth (100,62.5,0); transformed port mismatch < 0.035 mm')
print(checks,'analytic motion endpoint/monotonicity replay cases;',ray,'interval-corner ray cases')
print('moving read at 2 m/s: read 13/3 s, far 35/3 s, near 38/3 s')
print('both branch arrivals by 12 s impossible for every feasible velocity; stationary read misses 5 s')
