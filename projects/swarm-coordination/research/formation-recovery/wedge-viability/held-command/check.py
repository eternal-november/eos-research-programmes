from fractions import Fraction as F
from math import ceil
from itertools import product

one,zero=F(1),F(0)
P=lambda z:max(z,zero)

# Exact maximum on a whole segment, including any interior stationary point.
def qmax(x,v,a,h):
    when=[zero,h]
    if a<0 and 0 < -v/a < h: when.append(-v/a)
    return max(x+v*t+a*t*t/2 for t in when)

def run(g,x,y,v,w,a,b,h):
    ok=all(qmax(x+s*g*y,v+s*g*w,a+s*g*b,h)<=0 for s in (-1,1))
    return ok,(x+v*h+a*h*h/2,y+w*h+b*h*h/2,v+a*h,w+b*h)

def kernel(g,z):
    x,y,v,w=z
    return max(x+P(v)**2/2,*(x+s*g*y+P(v+s*g*w)**2/(2*(1+g)) for s in (-1,1)))<=0

first=0
for g,V,h in product(map(F,('1','1.25','1.5','2','3','10')), (F(1,3),one,F(4)), (F(i,24) for i in range(1,1001))):
    x=-(1+g)*V*V/2
    safe,z=run(g,x,zero,V,V,-one,-one,h)
    predicts=h<=V or (g-1)*(h/V-1)**2<=g+1
    assert (safe and kernel(g,z))==predicts
    first+=1

good=bad=pieces=0
g=F(2)
for h in (F(i,100) for i in range(1,901)):
    if h>1 and (h-1)**2>3:
        safe,z=run(g,-F(3,2),zero,one,one,-one,-one,h)
        assert not (safe and kernel(g,z))
        bad+=1
        continue
    z=(-F(3,2),zero,one,one)
    steps=max(1,ceil(one/h))
    for j in range(steps):
        safe,z=run(g,*z,-one,-one,h)
        assert safe
        pieces+=1
    T=steps*h
    b=(T-1)/h if h<F(3,2) else one
    assert zero<=b<=1
    safe,z=run(g,*z,-one,b,h)
    assert safe and z[2]+g*abs(z[3])<=0
    # After the terminal switch, horizontal full braking and zero lateral
    # acceleration keep both projected velocities nonpositive.
    for s in [-1,1]:
        assert z[2]+s*g*z[3]<=0
    pieces+=1
    good+=1

print(f'first_hold_exact_checks={first} periodic_positive={good} periodic_negative={bad} independently_checked_segments={pieces}')
