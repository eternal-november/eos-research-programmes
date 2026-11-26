#!/usr/bin/env python3
"""Exact active range-sensing trajectories and independent fixed-read LPs."""
from fractions import Fraction as Q
from math import sqrt
import json
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def trajectory(q):
    # This is the family of rational probe times, d = 3 q^2/8.
    d=3*q*q/8
    loss=3*q/4
    p=Q(3,8)-loss
    k=p+Q(1,5)
    lam=(Q(1,5)+d)/(p+d)
    def v1(t,fallback=False):
        if t<=1:
            return t
        if t<=3:
            return 1+(Q(2,5) if fallback else k)*min(t-1,3-t)
        return 4-t
    def ramp_fast(t):
        return min(Q(1),4*max(Q(0),t-3*q/4))
    def v2(t,mode):
        if t<=q:
            return ramp_fast(t)
        if t<=1:
            return ramp_fast(t) if mode==0 else (1-lam)*t+lam*ramp_fast(t)
        if t<=3:
            return Q(1)
        n=Q(1,5) if mode!=1 else p
        return min(Q(1),(4-t)/(1-2*n))
    out=[]
    for mode,(lo,hi) in enumerate(((-Q(1,5),Q(2,5)),(-Q(2,5),Q(1,5)),(-Q(1,5),Q(1,5)))):
        n=Q(1,5) if mode!=1 else p
        knots=sorted({Q(0),3*q/4,q,3*q/4+Q(1,4),Q(1),Q(2),Q(3),Q(3)+2*n,Q(4)})
        x1=x2=Q(0)
        low=high=Q(0)
        for t,u in zip(knots,knots[1:]):
            v,w=v1(t,mode==2),v2(t,mode)
            V,W=v1(u,mode==2),v2(u,mode)
            dt=u-t
            assert 0<=v<=3 and 0<=V<=3 and 0<=w<=1 and 0<=W<=1
            assert abs(V-v)<=dt and abs(W-w)<=4*dt
            dif=w-v
            slope=(W-V-dif)/dt
            cuts=[Q(0),dt]
            if slope and 0<-dif/slope<dt:
                cuts.append(-dif/slope)
            for s in cuts:
                r=x2-x1+dif*s+slope*s*s/2
                assert lo<=r<=hi
                low=min(low,r)
                high=max(high,r)
            x1+=(v+V)*dt/2
            x2+=(w+W)*dt/2
            if u==q:
                assert x1==q*q/2 and x2==q*q/8 and x2-x1==-d
                assert V==W==q
        target=Q(17,5) if mode==2 else Q(143,40)-loss
        assert x1==x2==target and v1(Q(4))==v2(Q(4),mode)==0
        out.append(dict(advance=str(target),gap_excursions=[str(low),str(high)]))
    return out


def direct(sample, d, hz=40, condition=True):
    # World-pair optimizer with identical state/velocity before the selected sample.
    N=4*hz
    size=8*(N+1)
    idx=lambda j,r,p,k: (4*j+2*r+p)*(N+1)+k
    le=[];eq=[]
    def add(rows,s,rhs):
        dd={}
        for col,a in s:
            dd[col]=dd.get(col,0)+a
        rows.append((dd,rhs))
    for j,(lo,hi) in enumerate(((-.2,.4),(-.4,.2))):
        for r in (0,1):
            for k,p in ((0,0),(0,1),(N,1)):
                add(eq,[(idx(j,r,p,k),1)],0)
            for k in range(N):
                u,v=idx(j,r,1,k),idx(j,r,1,k+1)
                x,y=idx(j,r,0,k),idx(j,r,0,k+1)
                add(eq,[(y,1),(x,-1),(u,-1/(2*hz)),(v,-1/(2*hz))],0)
                rate=1 if r==0 else 4
                for sign in (-1,1):
                    add(le,[(v,sign),(u,-sign)],rate/hz)
        for k in range(N+1):
            x,y=idx(j,0,0,k),idx(j,1,0,k)
            add(le,[(y,1),(x,-1)],hi)
            add(le,[(x,1),(y,-1)],-lo)
    for k in range(sample+1):
        for r,p in ((0,0),(0,1),(1,0),(1,1)):
            add(eq,[(idx(0,r,p,k),1),(idx(1,r,p,k),-1)],0)
    if condition:
        k=sample
        add(le,[(idx(0,1,0,k),1),(idx(0,0,0,k),-1)],-float(d))
    ref=idx(0,0,0,N)
    for j,r in ((0,1),(1,0),(1,1)):
        add(eq,[(idx(j,r,0,N),1),(ref,-1)],0)
    def export(rows):
        a=[];b=[];w=[];rhs=[]
        for i,(d,z) in enumerate(rows):
            rhs.append(z)
            for j,c in d.items():
                if c:
                    a.append(i);b.append(j);w.append(c)
        return coo_matrix((w,(a,b)),shape=(len(rows),size)).tocsr(),rhs
    A,b=export(le);E,e=export(eq)
    bounds=[]
    for _ in range(2):
        for W in (3,1):
            bounds.extend([(None,None)]*(N+1))
            bounds.extend([(0,W)]*(N+1))
    obj=[0.]*size;obj[ref]=-1
    z=linprog(obj,A_ub=A,b_ub=b,A_eq=E,b_eq=e,bounds=bounds,method='highs')
    if z.status==2:
        return None
    assert z.success
    return -z.fun


if __name__=='__main__':
    exact=[trajectory(q) for q in (Q(1,20),Q(3,40),Q(1,10))]
    d=Q(3,800)
    tests={q:direct(q,d) for q in (2,3,4,5,6,8,10)}
    assert tests[2] is None and tests[3] is None # less than sqrt(2d)
    assert abs(tests[4]-3.5)<1e-8 and all(z<3.5 for q,z in tests.items() if q>4)
    oracle=direct(0,d,condition=False)
    silent=direct(160,d,condition=False)
    assert abs(oracle-3.575)<1e-8 and abs(silent-3.4)<1e-8
    print(json.dumps(dict(distance_needed_for_detection=str(d),exact_family=exact,
        direct_fixed_read_LP={str(q/40):round(z,9) if z is not None else None for q,z in tests.items()},
        directly_informed=round(oracle,9),no_report=round(silent,9),
        old_optimal_advance_minus_active=str(Q(143,40)-Q(7,2)),
        optimal_probe_time=str(Q(1,10))),indent=2))
