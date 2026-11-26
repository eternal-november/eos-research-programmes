#!/usr/bin/env python3
"""Exact motion witness and independent sampled LP comparison."""
from fractions import Fraction as Q
import json
from scipy.optimize import linprog


def D(t,a,v):
    tau=min(t/2,v/a)
    return a*tau*(t-tau)


def proof_profile(T,a,V,A,W,eta):
    tau=V/a
    H=T-2*tau
    assert W>=V and A>=a
    if H<0:
        # Both execute the slow acceleration limit below both speed caps.
        assert a*T/2 <= V
        return a*T*T/4,[Q(0),T/2,T],Q(0)
    maximum=min(D(T,a,W),D(T,A,V),V*T-V*V/a+2*eta)
    eta=(maximum-(V*T-V*V/a))/2
    s=tau-2*eta/V
    mass=D(H,a,W-V)
    assert s>0 and V/s<=A and 2*eta<=mass
    length=V*T-V*V/a+2*eta
    mult=2*eta/mass if mass else Q(0)
    bump_edge=min(H/2,(W-V)/a)
    times=sorted({Q(0),s,tau,tau+bump_edge,T-tau-bump_edge,T-tau,T-s,T})

    def velocity(t):
        u=min(t,T-t)
        if u<=tau:
            return a*u,min(V,V/s*u)
        h=t-tau
        return V+mult*min(a*h,a*(H-h),W-V),V

    p=[Q(0),Q(0)]
    gaps=[]
    for x,y in zip(times,times[1:]):
        A0,B0=velocity(x)
        A1,B1=velocity(y)
        dt=y-x
        assert 0<=A0<=W and 0<=A1<=W and 0<=B0<=V and 0<=B1<=V
        assert abs(A1-A0)<=a*dt and abs(B1-B0)<=A*dt
        v0=B0-A0
        slope=(B1-A1-v0)/dt
        sample=[Q(0),dt]
        if slope and 0<-v0/slope<dt:
            sample.append(-v0/slope)
        gaps.extend(p[1]-p[0]+v0*t+slope*t*t/2 for t in sample)
        p[0]+=(A0+A1)*dt/2
        p[1]+=(B0+B1)*dt/2
    assert velocity(0)==velocity(T)==(0,0) and p==[length,length]
    assert length==maximum
    assert max(gaps)==eta and min(gaps)==-eta
    return length,times,eta


def direct_lp(T,a,V,A,W,eta,dt):
    N=int(T/dt)
    assert T==dt*N
    size=4*(N+1)
    vals=[]
    e=[]
    b=[]
    g=[]
    h=[]
    def x(i,k):return (2*i)*(N+1)+k
    def v(i,k):return (2*i+1)*(N+1)+k
    def row(components):
        w=[0.0]*size
        for i,c in components:
            w[i]+=float(c)
        return w
    for i,(ac,sp) in enumerate(((a,W),(A,V))):
        vals.extend([(None,None)]*(N+1))
        vals.extend([(-float(sp),float(sp))]*(N+1))
        for p in (x(i,0),v(i,0),v(i,N)):
            e.append(row(((p,1),)))
            b.append(0)
        for k in range(N):
            e.append(row(((x(i,k+1),1),(x(i,k),-1),(v(i,k),-dt/2),(v(i,k+1),-dt/2))))
            b.append(0)
            for sign in (-1,1):
                g.append(row(((v(i,k+1),sign),(v(i,k),-sign))))
                h.append(float(ac*dt))
    e.append(row(((x(0,N),1),(x(1,N),-1))))
    b.append(0)
    for k in range(N+1):
        for sign in (-1,1):
            g.append(row(((x(0,k),sign),(x(1,k),-sign))))
            h.append(float(eta))
    r=linprog(row(((x(0,N),-1),)),A_ub=g,b_ub=h,A_eq=e,b_eq=b,bounds=vals,method='highs')
    assert r.success
    return -r.fun


if __name__=='__main__':
    examples=[]
    for T,A,W,eta in [(4,4,3,0),(4,4,3,Q(1,10)),(4,4,3,Q(1,4)),
                      (3,4,3,Q(1,10)),(4,2,Q(11,10),Q(1,20)),(4,4,Q(6,5),Q(1,10)),(1,4,3,Q(1,4)),(4,2,3,Q(1,2)),(4,4,Q(6,5),Q(1,2))]:
        T,A,W,eta=map(Q,(T,A,W,eta));a=V=Q(1)
        exact,knots,used_eta=proof_profile(T,a,V,A,W,eta)
        dt=Q(1,20) if all((t/Q(1,20)).denominator==1 for t in knots) else Q(1,50)
        assert all((t/dt).denominator==1 for t in knots)
        independent=direct_lp(T,a,V,A,W,eta,dt)
        assert abs(independent-float(exact))<1e-8
        examples.append(dict(T=str(T),second_acceleration=str(A),first_speed=str(W),half_gap=str(eta),used_half_gap=str(used_eta),
            exact_distance=str(exact),independent_LP=round(independent,9),knots=[str(t) for t in knots]))
    scope=examples[1]
    assert scope['exact_distance']=='16/5'
    assert min(D(Q(4),Q(1),Q(3)),D(Q(4),Q(4),Q(1)))>Q(7,2)>Q(16,5)
    print(json.dumps(dict(cases=examples,individually_feasible_but_jointly_impossible="7/2"),indent=2))
