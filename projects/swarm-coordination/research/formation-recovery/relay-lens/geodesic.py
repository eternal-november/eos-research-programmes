"""Matched boundary-arc graph and independent radial integral for known centers."""
from math import acos, asin, atan2, cos, hypot, pi, sin, sqrt, inf
from random import Random
from scipy.integrate import quad

def length_abs(b,c,rho):
    d=hypot(b,c)
    assert 0<=c<rho<=b
    theta=atan2(b,c)
    return 2*sqrt(d*d-rho*rho)+2*rho*(theta-acos(rho/d))

def numeric_bound(b,c,rho):
    d=hypot(b,c)
    def f(r):return sqrt(max(0,1-(rho/r)**2))
    return 2*quad(f,rho,d,epsabs=1e-9)[0]+2*rho*atan2(b,c)

def graph_upper(b,c,r,n=4096):
    # True circular arcs, not unsafe chords. Only far semicircle has
    # been certified to fit the two-radio lens in the offset family.
    # Two straight visible end edges plus arc subpaths are enough.
    best=inf
    out=inf
    for i in range(n+1):
        t=-pi/2+pi*i/n; x,y=c-r*cos(t),r*sin(t)
        ux,uy=x-c,y
        if ux*(-x)+uy*(-b-y)>=-1e-12:
            best=min(best,hypot(x,y+b)-r*t)
        if ux*(-x)+uy*(b-y)>=-1e-12:
            out=min(out,best+r*t+hypot(x,b-y))
    return out

def main():
    rng=Random(10836);n=0
    for it in range(150):
        a=3;R=5
        c=0 if it%2 else rng.uniform(0,.8)
        r=rng.uniform(c+.15,min(R-a+c,sqrt(R*R-(a+c)**2))-.05)
        b=rng.uniform(r+.05,sqrt(R*R-a*a))
        L=length_abs(b,c,r)
        assert abs(numeric_bound(b,c,r)-L)<1e-7
        U=graph_upper(b,c,r)
        assert L-1e-9<=U and U-L<.03,(b,c,r,L,U)
        n+=1
    print(n,'known-world radial integrals and matched visibility/true-arc graphs agree with the optimum')
    for c,r in ((0,1.9),(0,2),(.5,1.75)):
        print('center',c,'clearance',r,'optimum',length_abs(3.5,c,r),'arc graph',graph_upper(3.5,c,r))
if __name__=='__main__':main()
