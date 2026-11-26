#!/usr/bin/env python3
"""Continuous stopping cut and direct trajectory check for a civil corridor."""
from fractions import Fraction as Q
from math import sqrt
import json
from scipy.optimize import minimize_scalar
from scipy.optimize import linprog


def stop_cut(q,a,gate,target):
    """Candidate endpoints of, and stationary points in, the two exact regimes."""
    p=a*q
    cap=min(p,sqrt(a*gate))
    switch=max(0.,2*sqrt(a*gate)-p)
    va=sqrt(a*(target-gate)/3)
    disc=6*a*target-2*p*p
    vb=(p+sqrt(disc))/3 if disc>=0 else 0
    cand=[0.,cap,min(cap,switch),min(cap,max(switch,va)),min(cap,switch,max(0.,vb))]
    def score(v):
        x=min(a*q*q/4+v*q/2-v*v/(4*a),gate-v*v/(2*a))
        out=(2*sqrt(a*(target-x)+v*v/2)-v)/a
        return out,x,v
    after,x,v=min(score(v) for v in cand)
    diff=minimize_scalar(lambda v:score(v)[0],bounds=(0,cap),method="bounded",
                         options={"xatol":1e-12})
    assert abs(after-min(diff.fun,score(0)[0],score(cap)[0]))<2e-6
    return after,x,v


def integrate(pairs):
    x=Q(0)
    for (t,v),(u,w) in zip(pairs,pairs[1:]):
        assert u>t and v>=0 and w>=0 and abs(v-w)<=u-t
        x+=(u-t)*(v+w)/2
    return x


def selected_path():
    approach=[(Q(0),Q(0)),(Q(2,5),Q(0)),(Q(7,5),Q(1)),(Q(11,5),Q(1,5))]
    x=integrate(approach)
    assert x==Q(49,50) and x+Q(1,5)**2/2==1
    brake=[(Q(0),Q(1,5)),(Q(1,5),Q(0))]
    proceed=[(Q(0),Q(1,5)),(Q(1,5),Q(2,5)),(Q(3,5),Q(0))]
    assert x+integrate(brake)==1 and x+integrate(proceed)==Q(28,25)
    return approach,brake,proceed


def direct_grid():
    # No stopping-envelope formula for reachability; fix the witnessed cut
    # speed, constrain its stopping position, and optimize explicit velocities.
    dt=Q(1,5)
    q,d=11,14
    n=d+1
    z=[]
    h=[]
    def row(a):
        v=[0.]*n
        for i,c in a:
            v[i]+=float(c)
        return v
    for k in range(d):
        for s in (-1,1):
            z.append(row(((k+1,s),(k,-s))))
            h.append(float(dt))
    def area(k):
        return [float(dt)/2]+[float(dt)]*(k-1)+[float(dt)/2]+[0.]*(d-k)
    z.append(area(q))
    h.append(float(Q(49,50)))
    vb=[(0,None)]*n
    vb[0]=vb[d]=(0,0)
    vb[q]=(.2,.2)
    r=linprog([-x for x in area(d)],A_ub=z,b_ub=h,bounds=vb,method='highs')
    assert r.success and abs(-r.fun-28/25)<1e-8
    return -r.fun


if __name__=='__main__':
    for q in (0.5,0.75,1,1.2,1.4,1.7,2,2.2,3):
        for target in (1.04,1.12,1.5,2,3,4,5,8,12):
            stop_cut(q,1,1,target)
    a,x,v=stop_cut(2.2,1,1,1.12)
    assert abs(a-.6)<1e-12 and abs(v-.2)<1e-12
    p,b,g=selected_path()
    before,after,old=2.2,.6,2*sqrt(.12)
    assert before+after<before+old
    opt=direct_grid()
    print(json.dumps(dict(independent_numeric_regime_comparisons=81,decision_time="11/5",
        cut_position="49/50",cut_speed="1/5",conditional_completion="14/5",
        stopped_at_gate_completion=round(before+old,9),good_endpoint=str(Q(28,25)),
        direct_fixed_cut_speed_endpoint=round(opt,9)),indent=2))
