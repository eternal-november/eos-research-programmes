"""Exact sample points on and between signs of univariate quadratics."""
from fractions import Fraction as F
from math import gcd,isqrt,lcm

def add(p,q): return tuple(a+b for a,b in zip(p,q))
def mul(k,p): return tuple(k*a for a in p)
def sub(p,q): return add(p,mul(-1,q))
def sg(x): return (x>0)-(x<0)

def roots(p):
    # Convert rational coefficients, normalize primitive degree-two sign.
    c,b,a=(int(v*lcm(*(F(w).denominator for w in p))) for v in p)
    if a==0:
        return [F(-c,b)] if b else []
    if a<0:
        a,b,c=-a,-b,-c
    g=gcd(a,b,c)
    a,b,c=a//g,b//g,c//g
    d=b*b-4*a*c
    if d<0:
        return []
    s=isqrt(d)
    if s*s==d:
        return list({F(-b+i*s,2*a) for i in (-1,1)})
    return [(a,b,c,d,i) for i in (-1,1)]

def enclosure(r,s):
    if isinstance(r,F):
        return r,r
    a,b,_,d,i=r
    bnd=isqrt(d*s*s)
    lo,hi=(bnd,bnd+1) if i==1 else (-bnd-1,-bnd)
    return F(-b*s+lo,2*a*s),F(-b*s+hi,2*a*s)

def phases(polys):
    rr={r for p in polys for r in roots(p)}
    if not rr:
        return [None,F(0)]
    # Distinct rational numbers or canonical irreducible quadratic roots.
    scale=1
    while True:
        boxes=sorted(((*enclosure(r,scale),r) for r in rr), key=lambda v:v[:2])
        if all(a[1]<b[0] for a,b in zip(boxes,boxes[1:])):
            break
        scale*=2
    out=[None,boxes[0][0]-1]
    for i,(lo,hi,r) in enumerate(boxes):
        out.append(r)
        out.append((hi+boxes[i+1][0])/2 if i+1<len(boxes) else hi+1)
    return out

def radical_sign(x,y,d):
    # Exact sign(x+y sqrt(d)); used only for non-square d.
    if not x or not y or sg(x)==sg(y):
        return sg(x or y)
    return sg(x)*sg(x*x-d*y*y)

def sign(p,r):
    c,b,a=p
    if r is None: # omitted direction (-1,0), use homogeneous quadratic's t^2 coefficient
        return sg(a)
    if isinstance(r,F):
        return sg(c+b*r+a*r*r)
    A,B,C,D,i=r
    c,b=c-a*F(C,A),b-a*F(B,A)
    return radical_sign(2*A*c-B*b,i*b,D)
