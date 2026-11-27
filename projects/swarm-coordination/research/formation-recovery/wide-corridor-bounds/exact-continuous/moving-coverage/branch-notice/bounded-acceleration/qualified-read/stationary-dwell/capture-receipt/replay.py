"""Rational certificates for fixed sensing sites and post-capture delay."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

H=F(637,100)
A=F(10)
S=4/H
C=F(2,3)
ETA=C-S
DELTA=7-H-S
SLO=F(797193939,10**10)
SHI=F(797193940,10**10)
RED=2*A*DELTA
RGOOD=F(604725,10**6)
RBAD=F(604726,10**6)

def cutoff(s,r):
    return r<=C and (C-r)**2>=s*ETA+ETA**2/2

def test(s,p,d,q,r):
    if not (0<=p<=A*s*s/2 and 0<=d<=q<=r and cutoff(s,r)):
        return False
    u=S-s-q
    return u>=0 and 4*p<=A*(q-d)**2 and 4*p>=A*(2*s*s-u*u)

def envelopes(s,p,d,q,r):
    if not (0<=p<=A*s*s/2 and 0<=d<=q<=r and cutoff(s,r)):
        return False
    t=S-q; v=A*s
    if t<s:return False
    bend=(t-s)/2
    low=-A*bend
    integral=low*bend/2+(low+v)*(t-bend)/2
    # Rest-to-rest backward cone is two triangles.
    reach=A*(q-d)**2/4
    return integral<=p<=reach

def trace(segments):
    ans=[]
    time=F(0);x=F(4);v=F(0)
    for end,a in segments:
        assert end>=time
        if end==time:continue
        ans.append((time,end,x,v,a))
        x,v=state(ans[-1],end)
        time=end
    return ans
def state(piece,t):
    l,_,x,v,a=piece
    d=t-l
    return x+v*d+a*d*d/2,v+a*d
def at(path,t):
    return state(next(z for z in path if z[0]<=t<=z[1]),t)
def verify(path,world):
    # Check affine inequalities against the quadratic extrema.
    phases=((0,2,H/2,0),) if world=='far' else ((0,1,F(3,2),0),(1,2,0,F(3,2)))
    def affine(z,l,r,sign,b,m):
        t,_,x,v,a=z
        q=[l,r]
        if a:
            z0=t+(sign*m-v)/a
            if l<z0<r:q.append(z0)
        assert all(sign*state(z,key)[0]<=b+m*key for key in q),(world,z,l,r,b,m,q)
        return len(q)
    seen=0
    for z in path:
        t,u,x,v,a=z
        assert -A<=a<=A and -1<=v<=1 and -1<=state(z,u)[1]<=1
        seen+=affine(z,t,u,1,F(6),F(0))+affine(z,t,u,-1,F(-1),F(0))
        for lo,hi,m,b in phases:
            l=max(t,lo);r=min(u,hi)
            if l>=r:continue
            edges=sorted({l,r,*((F(k-b,m) for k in (1,2) if m and l<F(k-b,m)<r))})
            for left,right in zip(edges,edges[1:]):
                center=b+m*(left+right)/2
                if center<=1:continue
                seen+=affine(z,left,right,-1,1-b,-m)
                if center<=2:seen+=affine(z,left,right,1,F(4),F(0))
                else:seen+=affine(z,left,right,1,b+2,m)
    return seen

def checked_families():
    cuts=0;paths=0
    # Use strictly upper seam velocity for the positive paths, but
    # choose p away from the narrow uncertain p0 boundary.
    for u in (F(11,100),F(9,100),F(7,100),F(3,100),F(1,100)):
        s=SHI
        p=A*(2*s*s-u*u)/4
        q=S-s-u
        tau=F(117,1000) # slower triangle, still before each dwell
        a=4*p/tau**2
        assert p<=A*SLO**2/2 and 0<a<=A and 2*p/tau<=1
        branch=RGOOD
        cfs=[(tau/2,-a),(tau,a),(q,0),(q+u/2,-A),(branch,A)]
        assert at(trace(cfs),q)==(4-p,0)
        vf=A*s
        far=trace(cfs+[(S+(1-vf)/A,A),(2,0)])
        assert at(far,S)==(4,vf) and at(far,2)[0]>=H-1
        partial=trace(cfs+[(C,-A)])
        x,v=at(partial,C)
        assert x<=4 and v<0
        late=trace(cfs+[(C,-A),(C-v/A,A),(2,0)])
        assert test(s,p,q-tau,q,branch)
        cuts+=verify(far,'far')+verify(late,'late')
        paths+=2

    # Boundary counterexample: farther sensor at p=.1 is outside the
    # restricted theorem. Known far works at q=S-.15 with unit speed,
    # but equality at r_a would require reaching the seam at speed k.
    # The speed-capped maximal rest-to-k travel is .1-DELTA < .1.
    p=F(1,10);tau=F(1,5);q=S-F(3,20)
    d=q-tau
    assert d>0 and p>A*SHI**2/2
    prep=[(tau/2,-A),(tau,A),(q,0)]
    assert at(trace(prep),q)==(4-p,0)
    branch=F(57,100)
    common=prep+[(branch,A)]
    x,v=at(trace(common),branch)
    assert 0<v<1 and x+v*v/(2*A)<=4
    far=trace(common+[(q+1/A,A),(2,0)])
    late=trace(common+[(branch+v/A,-A),(2,0)])
    assert at(far,S)==(4,1) and at(far,2)[0]>=H-1
    assert F(3,20)>=F(1,10)+(1-A*SLO)/A
    assert F(3,20)-F(1,20)-DELTA<p
    cuts+=verify(far,'far')+verify(late,'late')
    paths+=2
    # Exact isolation of the farther site's different switching law.
    zlo=F(14340554,10**8)
    zhi=F(14340555,10**8)
    assert zlo*zlo<A*DELTA<zhi*zhi
    rc=S+(zlo-F(1,2))/A
    zbad=S+(zhi-F(1,2))/A
    assert F(59228403,10**8)<rc<zbad<F(59228405,10**8)
    assert C<S+F(1,20) and 1-zhi>F(1,2)
    for p in (F(1,10),F(12,100),F(15,100),F(1,5),F(23,100)):
        q=S-p-1/(2*A)
        tau=p+1/A
        assert q>=tau
        prep=[(1/A,-A),(p,0),(tau,A),(q,0)]
        assert at(trace(prep),q)==(4-p,0)
        coast_end=q+p
        brake=rc-coast_end
        assert 0<brake<1/A
        f=trace(prep+[(q+1/A,A),(coast_end,0),(rc,-A),(rc+brake,A),(2,0)])
        l=trace(prep+[(q+1/A,A),(coast_end,0),(q+p+1/A,-A),(2,0)])
        # The shared trajectory is identical through receipt.
        assert at(l,rc)==at(f,rc)
        assert at(l,q+p+1/A)==(4,0)
        assert at(f,2)[0]>=H-1 and at(f,2)[0]==4+2-S-A*brake**2
        cuts+=verify(f,'far')+verify(l,'late')
        paths+=2
    middle=[]
    for speed in (F(72,100),F(8,10),F(9,10),F(97,100)):
        p=speed**2/A
        q=S-p-1/(2*A)
        tau=2*speed/A
        z2=A*DELTA+(1-speed)**2
        scale=10**10
        scaled=z2*scale*scale
        k=isqrt(scaled.numerator//scaled.denominator)
        zl,zh=F(k,scale),F(k+1,scale)
        assert zl**2<z2<zh**2
        tstar=q+(2*speed-1+zl)/A
        assert tstar>S-F(1,20) and tstar<S and q+2*speed/A>C
        prep=[(tau/2,-A),(tau,A),(q,0)]
        shared=prep+[(q+speed/A,A),(tstar,-A)]
        far=trace(shared+[(tstar+zl/A,A),(2,0)])
        late=trace(shared+[(q+2*speed/A,-A),(2,0)])
        cuts+=verify(far,'far')+verify(late,'late')
        assert at(late,2)==(4,0) and at(far,2)[0]>=H-1
        assert at(far,2)[0]==4+2-S-(zl**2-(1-speed)**2)/A
        middle.append([str(p),str(tstar),str(tstar+(zh-zl)/A)])
        paths+=2
    return paths,cuts,middle

def main():
    assert (1-A*SHI)**2<RED<(1-A*SLO)**2
    assert cutoff(SHI,RGOOD) and not cutoff(SLO,RBAD)
    comparisons=0
    for s,pi,di,qi,ri in product((SLO,SHI),range(0,32,3),
                    range(0,481,12),range(360,561,7),range(450,611,11)):
        p,d,q,r=(F(pi,1000),F(di,1000),F(qi,1000),F(ri,1000))
        assert test(s,p,d,q,r)==envelopes(s,p,d,q,r)
        comparisons+=1
    # Positive separated timing witness, plus stationary-until-receive failure.
    for s in (SLO,SHI):
        assert test(s,0,F(42,100),F(425,1000),F(59,100))
        assert S-s<F(59,100)
        assert not test(s,0,F(42,100),F(445,1000),F(59,100))
    paths,cuts,middle=checked_families()
    print(json.dumps(dict(comparisons=comparisons,continuous_witnesses=paths,
          extrema_checks=cuts,intermediate_site_cutoffs=middle,arrival_bracket=['0.604725','0.604726'],
          boundary_site='1/10',boundary_early_receipt='57/100',boundary_global_limit_impossible=True,
          boundary_exact_receipt_bracket=['0.59228403','0.59228405']),
          sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
