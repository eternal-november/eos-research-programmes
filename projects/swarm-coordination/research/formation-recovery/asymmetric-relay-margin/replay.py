"""Exact expressions and independent sampled true-arc path checks."""
from math import sqrt,hypot,atan2,cos,sin,pi,acos,inf
from random import Random
from scipy.optimize import brentq


def near(h,b,c,r):
    def end(z):
        d=hypot(z,c)
        return sqrt(max(0,d*d-r*r))+r*(atan2(z,c)-acos(min(1,r/d)))
    return end(h)+end(b)


def outer(b,c,r):
    return near(b,b,c,r)+4*r*atan2(c,b)


def staged(t,b,c,r,v):
    return t+near(max(sqrt(r*r-c*c),b-v*t),b,c,r)/v


def visibility_graph(a,rp,rm,b,h,c,r,side,N=4096):
    """Straight visible tangent approximations and exact circle arcs.

    Angles are sampled uniformly, not calculated by the optimum formula.
    Every path used is feasible: arc intervals admissible on this side of
    circle are contiguous around the corresponding tip under the stated
    radius assumptions, and the line segments stay in the convex lens.
    """
    best=out=inf
    edge=acos(c/r) if side==-1 else pi/2
    # Treat the endpoint on the obstacle exactly, not by a grid proxy.
    angles=[-edge+2*edge*i/N for i in range(N+1)]
    for t in angles:
        x,y=c+side*r*cos(t),r*sin(t)
        if hypot(x-a,y)>rp+1e-10 or hypot(x+a,y)>rm+1e-10:
            continue
        if side==1:
            assert x>=0  # the other disk is farther
        ux,uy=x-c,y
        if ux*(-x)+uy*(-h-y)>=-1e-10:
            best=min(best,hypot(x,y+h)-r*t)
        if ux*(-x)+uy*(b-y)>=-1e-10:
            out=min(out,best+r*t+hypot(x,b-y))
    return out


def main():
    rng=Random(625793)
    for _ in range(180):
        a=rng.uniform(.8,5)
        c=rng.uniform(.1,min(a,.9))
        r=rng.uniform(c+.03,c+2)
        b=r+rng.uniform(0,3)
        # Exactly at the useful radius for the outer arc, unless the
        # physical endpoint already requires more range.
        base=max(hypot(a,b),a-c+r)
        rm=max(base,a+c+r)
        hstar=sqrt(r*r-c*c)
        h=rng.choice([hstar,rng.uniform(hstar,b),b])
        for side,expected,start in (
            (-1,near(h,b,c,r),h),(1,outer(b,c,r),b)
        ):
            got=visibility_graph(a,base,rm,b,start,c,r,side)
            assert expected-1e-7<=got<=expected+.025,(a,b,h,c,r,side,expected,got)
        v=rng.uniform(.25,3)
        prev=near(b,b,c,r)/v
        for i in range(1,41):
            now=staged(i*b/(20*v),b,c,r,v)
            assert now>=prev-1e-10
            prev=now
    print("360 matched feasible true-arc graphs; 7200 monotonicity checks")
    a,b,c,r,v=3,3.5,.5,1.75,1
    B=outer(b,c,r)/v
    cutoff=brentq(lambda t: staged(t,b,c,r,v)-8.25,0,5)
    crossover=brentq(lambda t:staged(t,b,c,r,v)-B,0,5)
    print(f"reach={a+c+r:.6f} blind={B:.9f} known={near(b,b,c,r)/v:.9f}")
    print(f"deadline=8.25 latest={cutoff:.9f}; blind-preferred after={crossover:.9f}")


if __name__=="__main__":
    main()

