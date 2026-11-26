#!/usr/bin/env python3
"""Exact visibility-dwell trajectories and sampled two-world trajectory comparisons."""
from fractions import Fraction as Q
import json
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def exact_case(l,h,long=False):
    if long:
        d=Q(1,512)
        s,r=Q(1,16),Q(17,128)
        assert 2*d==s*s and h==r-s and h*h>8*d/9
        assert 2*(r-l)**2==r*r/2-d
        assert s<l<r
    else:
        d=Q(2,3)*(l*l-Q(9,16)*h*h)
        s,r=4*l/3-h/2,4*l/3+h/2
        assert h*h<=8*d/9 and l<=s
    assert 0<d<=Q(3,800) and 0<h<=Q(1,10) and s<r<Q(1,4)
    delta=(3*r-4*l)
    b=r+delta/5
    base_gap=-d+delta*delta/10
    goal=Q(143,40)-l
    p=Q(3,8)-l
    lam=(Q(1,5)-base_gap)/(p-base_gap)
    assert 0<lam<1 and base_gap<Q(1,5)
    def v1(t,mode):
        if t<=1:
            return t
        if t<=3:
            extra=Q(2,5) if mode==2 else p+Q(1,5)
            return 1+extra*min(t-1,3-t)
        return 4-t
    def fast(t):
        return min(Q(1),4*max(Q(0),t-l))
    def far_base(t):
        return fast(r)-4*(t-r) if t<=b else t
    def v2(t,mode):
        if t<=r:return fast(t)
        if t<=1:return fast(t) if mode==0 else lam*fast(t)+(1-lam)*far_base(t)
        if t<=3:return Q(1)
        n=p if mode==1 else Q(1,5)
        return min(Q(1),(4-t)/(1-2*n))
    for mode,(lo,hi) in enumerate(((-Q(1,5),Q(2,5)),(-Q(2,5),Q(1,5)),
                                  (-Q(1,5),Q(1,5)))):
        kn=sorted({Q(0),l,s,r,b,l+Q(1,4),Q(1),Q(2),Q(3),
             3+2*(p if mode==1 else Q(1,5)),Q(4)})
        x=y=Q(0)
        max_read=-Q(100)
        for t,u in zip(kn,kn[1:]):
            v,w=v1(t,mode),v2(t,mode)
            V,W=v1(u,mode),v2(u,mode)
            assert 0<=v<=3 and 0<=V<=3 and 0<=w<=1 and 0<=W<=1
            assert abs(V-v)<=u-t and abs(W-w)<=4*(u-t)
            p0=w-v
            vel=(W-V-p0)/(u-t)
            times=[0,u-t]
            if vel and 0<-p0/vel<u-t:
                times.append(-p0/vel)
            for z in times:
                e=y-x+p0*z+vel*z*z/2
                assert lo<=e<=hi
                if s<=t+z<=r:
                    assert e<=-d and e>-d-Q(1,5)
                    max_read=max(max_read,e)
            x+=(v+V)*(u-t)/2
            y+=(w+W)*(u-t)/2
        assert max_read==-d
        assert x==y==(Q(17,5) if mode==2 else goal)
        assert v1(Q(4),mode)==v2(Q(4),mode)==0
    return d,s,r,goal


def direct(start,end,d,hz=200):
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
    for k in range(end+1):
        for r,p in ((0,0),(0,1),(1,0),(1,1)):
            add(eq,[(idx(0,r,p,k),1),(idx(1,r,p,k),-1)],0)
    for k in range(start,end+1):
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
    results=[]
    for delay,h in ((Q(3,40),Q(1,50)),(Q(3,40),Q(1,25)),
                    (Q(3,40),Q(1,20)),(Q(2,25),Q(1,25))):
        d,s,r,D=exact_case(delay,h)
        results.append(dict(admitted_shortfall=str(d),duration=str(h),opening=str(s),
            receipt=str(r),attained_advance=str(D),hidden_safe_fallback="17/5"))
    dl,sl,rl,Dl=exact_case(Q(19,256),Q(9,128),long=True)
    lg=direct(16,34,dl,hz=256)
    assert abs(lg-float(Dl))<1e-8
    d=Q(63,20000)
    checks=[direct(15,23,d),direct(16,24,d),direct(17,25,d)]
    assert checks[0] is None and checks[1] is not None and checks[2] is not None
    assert abs(checks[1]-3.5)<1e-8 and checks[2]<3.5
    print(json.dumps(dict(exact=results,long_dwell=[str(x) for x in (dl,sl,rl,Dl)],long_sampled_LP=round(lg,9),nearby_sampled_LP=[round(x,9) if x is not None else None for x in checks]),indent=2))
