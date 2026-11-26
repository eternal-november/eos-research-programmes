#!/usr/bin/env python3
"""Condition progress and safety on the same bounded calibration offset."""
from fractions import Fraction as F
from pathlib import Path
import sys,json,importlib.util
from random import Random

parent=Path(__file__).resolve().parent
# The independent oracle preserves signs at isolated algebraic events.
phase_path=(Path(sys.argv[1]) if len(sys.argv)>1 else
    parent.parents[3]/'shared-retire-cut/scope/temporal-overlap/shared-calibration/shared-yaw/phase.py')
spec=importlib.util.spec_from_file_location('phase',phase_path)
phase=importlib.util.module_from_spec(spec)
spec.loader.exec_module(phase)
def at(q,t):
    return q[0]+t*(q[1]+t*q[2])
def vertex(q):
    return F(-q[1],2*q[2]) if q[2] else None
def range_on(q,l,r):
    vs=[at(q,l),at(q,r)]
    v=vertex(q)
    if v is not None and l<v<r:
        vs.append(at(q,v))
    return min(vs),max(vs)
def possible_y(q,l,r,zlo,zhi,L,U):
    mn,mx=range_on(q,l,r)
    return max(mn,L-zhi),min(mx,U-zlo)

def decision(q,l,r,zlo,zhi,L,U,c,drift=0):
    # Order of arguments: prior progress, offset support, observation, ceiling.
    assert 0<=l<=r<=1 and zlo<=zhi and L<=U and drift>=0
    a,b=possible_y(q,l,r,zlo,zhi,L,U)
    if a>b:
        return 'inconsistent',None
    # Worst continuation attained at its current parameter or a fixed candidate.
    worst=(min(b+zhi,U+drift),('at-observation',b))
    fixed=[(F(1),r)]
    v=vertex(q)
    if q[2]<0 and v is not None and l<=v<=1:
        fixed.append((v,min(r,v)))
    for t,upper in fixed:
        a,b=possible_y(q,l,upper,zlo,zhi,L,U)
        if a<=b:
            val=at(q,t)+min(zhi,U-a+drift)
            if val>worst[0]:
                worst=val,(t,a)
    return ('safe' if worst[0]<=c else 'unsafe'),worst

def direct(q,l,r,zlo,zhi,L,U,c,drift=0):
    # Sign-arrangement oracle on observed progress, independent of the range test.
    def const(k): return (k,0,0)
    def check(interval_end, extra):
        pol_l=phase.sub(q,const(L-zhi))
        pol_u=phase.sub(const(U-zlo),q)
        closed=[(-l,1,0),(interval_end,-1,0),pol_l,pol_u]
        return any(t is not None and all(phase.sign(p,t)>=0 for p in closed)
                   and all(phase.sign(p,t)>0 for p in extra)
                   for t in phase.phases(closed+extra))
    if not check(r,[]):
        return 'inconsistent'
    if U+drift>c and check(r,[phase.sub(q,const(c-zhi))]):
        return 'unsafe'
    for t in (F(1),vertex(q)):
        if t is not None and l<=t<=1 and at(q,t)+zhi>c:
            if check(min(r,t),[phase.sub(const(U+drift+at(q,t)-c),q)]):
                return 'unsafe'
    return 'safe'

def check_witness(q,l,r,zlo,zhi,L,U,result,drift=0):
    value,w=result
    t,y=w
    if t=='at-observation':
        future=y
        interval=r
    else:
        future=at(q,t)
        interval=min(r,t)
    a,b=range_on(q,l,interval)
    assert a<=y<=b # intermediate value furnishes the past parameter.
    z=min(zhi,U-y)
    assert zlo<=z<=zhi and L<=y+z<=U and future+min(zhi,z+drift)==value

def main():
    half_turn=(0,4,-4)
    ex=half_turn,F(1,3),F(1),0,F(1,3),F(9,10),F(1),F(10,9)
    got,w=decision(*ex)
    assert got=='safe' and w[0]==F(10,9)
    assert decision(*ex[:-1],F(10,9)-F(1,1000))[0]=='unsafe'
    assert decision(half_turn,0,1,0,F(1,3),F(9,10),F(1),F(10,9))[0]=='unsafe'
    # The precise separate maxima are 1 and 1/3, both witnessed.
    assert at(half_turn,F(1,2))==1
    a,b=range_on(half_turn,F(1,2),F(1))
    assert F(2,3)+F(1,3)==1 and a<=F(2,3)<=b
    for drift in (0,F(1,90),F(2,9),1):
        g,w=decision(*ex,drift=drift)
        assert w[0]==1+min(F(1,3),F(1,9)+drift)
        assert (g=='safe')==(drift==0)
        assert g==direct(*ex,drift=drift)
        check_witness(*ex[:-1],w,drift=drift)
    R=Random(535)
    counts=dict(safe=0,unsafe=0,inconsistent=0)
    for i in range(900):
        q=tuple(R.randrange(-7,8) for _ in range(3))
        l,r=sorted(F(R.randrange(9),8) for _ in range(2))
        zl,zh=sorted(F(R.randrange(-8,9),4) for _ in range(2))
        L,U=sorted(F(R.randrange(-10,11),4) for _ in range(2))
        c=F(R.randrange(-8,9),4)
        args=q,l,r,zl,zh,L,U,c
        g,w=decision(*args)
        assert g==direct(*args)
        if w: check_witness(*args[:-1],w)
        counts[g]+=1
        drift=F(R.randrange(5),4)
        g,w=decision(*args,drift=drift)
        assert g==direct(*args,drift=drift)
        if w: check_witness(*args[:-1],w,drift=drift)
    print(json.dumps(dict(checked=counts,joint_peak='10/9',separate_peaks_sum='4/3',
                          tightening_breaks=True,unearned_progress_breaks=True,drift_checks=900),indent=2,sort_keys=True))

if __name__=='__main__':
    main()
