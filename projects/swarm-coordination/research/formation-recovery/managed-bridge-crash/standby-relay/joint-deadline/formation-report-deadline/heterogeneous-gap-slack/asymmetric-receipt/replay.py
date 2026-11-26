#!/usr/bin/env python3
"""Exact quadratic-field trajectories and an independent shared-prefix LP."""
import json
from math import sqrt
from sympy import Rational as Q, sqrt as root, simplify, sign
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def sgn(z):
    n=sign(simplify(z))
    assert n in (-1,0,1)
    return int(n)


def compare(z,y):
    return sgn(z-y)


def integrate(knots,x0,x1,gap_lower,gap_upper):
    x,y=Q(0),Q(0)
    minsl,maxsl=Q(0),Q(0)
    for l,r in zip(knots,knots[1:]):
        u,v=x0(l),x1(l)
        U,V=x0(r),x1(r)
        dt=simplify(r-l)
        assert sgn(dt)>0
        for s,w,cap,rate in ((u,U,3,1),(v,V,1,4)):
            assert sgn(s)>=0 and sgn(w)>=0 and sgn(cap-s)>=0 and sgn(cap-w)>=0
            assert sgn(rate*dt-(w-s))>=0 and sgn(rate*dt+(w-s))>=0
        vel=v-u
        slope=simplify((V-U-vel)/dt)
        samples=[Q(0),dt]
        if slope:
            cut=simplify(-vel/slope)
            if sgn(cut)>0 and sgn(dt-cut)>0:
                samples.append(cut)
        for t in samples:
            d=simplify(y-x+vel*t+slope*t*t/2)
            assert sgn(d-gap_lower)>=0 and sgn(gap_upper-d)>=0
            minsl=d if compare(d,minsl)<0 else minsl
            maxsl=d if compare(d,maxsl)>0 else maxsl
        x=simplify(x+(u+U)*dt/2)
        y=simplify(y+(v+V)*dt/2)
    return x,y,minsl,maxsl


def trajectories():
    c=1-root(7)/4
    b=1-root(7)/5
    assert sgn(c-Q(1,4))>0 and sgn(b-c)>0 and sgn(1-b)>0

    def picked(p,q):
        return p if sgn(p-q)<=0 else q

    def v1(t):
        if sgn(t-1)<=0:
            return t
        if sgn(t-3)>=0:
            return 4-t
        return 1+Q(23,40)*picked(t-1,3-t)

    def v2A(t):
        if sgn(t-1)<=0:
            return picked(4*t,1)
        if sgn(t-3)<=0:
            return 1
        return picked(1,(4-t)/Q(3,5))

    def v2B(t):
        if sgn(t-c)<=0:
            return picked(4*t,1)
        if sgn(t-b)<=0:
            return simplify(1-4*(t-c))
        if sgn(t-1)<=0:
            return t
        if sgn(t-3)<=0:
            return 1
        return picked(1,4*(4-t))

    eA=[0,Q(1,4),c,1,2,3,Q(17,5),4]
    eB=[0,Q(1,4),c,b,1,2,3,Q(15,4),4]
    D=Q(143,40)
    ansA=integrate(eA,v1,v2A,-Q(1,5),Q(2,5))
    ansB=integrate(eB,v1,v2B,-Q(2,5),Q(1,5))
    assert ansA==(D,D,-Q(1,5),Q(3,8))
    assert ansB==(D,D,-Q(3,8),Q(1,5))
    c_gap=simplify(c-Q(1,8)-c*c/2)
    assert simplify(c_gap+(1-c)**2/10)==Q(1,5)
    assert simplify(v2A(c)-v2B(c))==0 and simplify(v2B(b)-v1(b))==0
    return c,ansA,ansB


def direct(cut_index, hz=100, bands=((-0.2,0.4),(-0.4,0.2))):
    # Full time-grid optimization of both worlds, rather than a scalar deadline formula.
    N=4*hz
    size=8*(N+1)
    ids=lambda j,i,p,t: (4*j+2*i+p)*(N+1)+t
    ub=[]; eq=[]
    def add(out,mapping,rhs):
        col={}
        for i,w in mapping:
            col[i]=col.get(i,0)+w
        out.append((col,rhs))
    for j,(low,high) in enumerate(bands):
        for i in range(2):
            for coordinate,k in ((0,0),(1,0),(1,N)):
                add(eq,[(ids(j,i,coordinate,k),1)],0)
            for t in range(N):
                u,v=ids(j,i,1,t),ids(j,i,1,t+1)
                x,y=ids(j,i,0,t),ids(j,i,0,t+1)
                add(eq,[(y,1),(x,-1),(u,-.5/hz),(v,-.5/hz)],0)
                for z in (-1,1):
                    add(ub,[(v,z),(u,-z)],(1 if i==0 else 4)/hz)
        for t in range(N+1):
            add(ub,[(ids(j,1,0,t),1),(ids(j,0,0,t),-1)],high)
            add(ub,[(ids(j,1,0,t),-1),(ids(j,0,0,t),1)],-low)
    for t in range(cut_index+1):
        for i,p in ((0,0),(0,1),(1,0),(1,1)):
            add(eq,[(ids(0,i,p,t),1),(ids(1,i,p,t),-1)],0)
    ref=ids(0,0,0,N)
    for j,i in ((0,1),(1,0),(1,1)):
        add(eq,[(ids(j,i,0,N),1),(ref,-1)],0)
    def export(rows):
        v=[];a=[];b=[];rhs=[]
        for ri,(cols,c) in enumerate(rows):
            rhs.append(c)
            for ci,w in cols.items():
                if w:
                    a.append(ri);b.append(ci);v.append(w)
        return coo_matrix((v,(a,b)),shape=(len(rows),size)).tocsr(),rhs
    A,b=export(ub);Aeq,beq=export(eq)
    bounds=[]
    for j in range(2):
        for i,h in ((0,3),(1,1)):
            bounds.extend([(None,None)]*(N+1))
            bounds.extend([(-h,h)]*(N+1))
    obj=[0]*size;obj[ref]=-1
    r=linprog(obj,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method='highs')
    assert r.success
    return -r.fun


if __name__=='__main__':
    c,a,b=trajectories()
    assert sgn(c-Q(33,100))>0 and sgn(Q(35,100)-c)>0
    checks={q:direct(q) for q in (0,33,35,400)}
    assert abs(checks[0]-143/40)<1e-7
    assert abs(checks[33]-143/40)<1e-7
    assert checks[35]<143/40-1e-5
    assert abs(checks[400]-3.4)<1e-7
    symmetric=direct(0,hz=40,bands=((-0.25,0.25),)*2)
    shifted=direct(0,hz=40,bands=((0.0,0.5),)*2)
    assert abs(symmetric-3.5)<1e-8 and abs(shifted-3.375)<1e-8
    print(json.dumps(dict(cut=str(c),approx=round(float(c),9),
        equal_width_known_gap_advances=[round(symmetric,9),round(shifted,9)],
        trajectory_advance=[str(a[0]),str(b[0])],
        gap_excursions=[[str(q) for q in r[2:]] for r in (a,b)],
        independent_sampled_LP={str(k/100):round(v,9) for k,v in checks.items()}),indent=2))
