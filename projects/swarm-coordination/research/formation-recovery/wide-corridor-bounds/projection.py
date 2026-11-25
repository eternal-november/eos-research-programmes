from fractions import Fraction as F
from itertools import combinations
from math import inf, isclose
from random import Random
import json
try:
    from exact_ref import outside,span,holds,full,lp
except ModuleNotFoundError as e:
    if e.name!='exact_ref':raise
    from pathlib import Path
    import sys
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'continuous-corridor-coverage'))
    from replay import outside,span,holds,full,lp

def setup(q,box,g,R,b,L,U):
    n=len(box);e=outside(n,q,box,g,R)
    return [e+span(i,j,q,b,L,U) for i in range(n-q+1) for j in range(i,n-q+1)]

def cap_cell(upper,lower,edges):
    n=len(upper)
    z=list(upper)+[0]
    edges=list(edges)+[(i,-1,-b) for i,b in enumerate(lower)]
    for _ in range(n+1):
        changed=False
        for i,j,c in edges:
            u=z[i]+c
            if u<z[j]:z[j]=u;changed=True
        if z[-1]<0:return None
        if not changed:return tuple(z[:-1])
    return None

def project(upper,lower,cells):
    pts=[x for e in cells if (x:=cap_cell(upper,lower,e)) is not None]
    if not pts:return None
    return tuple(map(max,zip(*pts)))

def samples(A,B,v,cells,h,N):
    assert all(x<=y for x,y in zip(A,B))
    if A==B:return [A],True
    x=A;path=[x]
    for t in range(1,N+1):
        cap=tuple(min(z,a+h*w) for z,a,w in zip(B,x,v))
        y=project(cap,A,cells)
        assert y is not None and all(a<=b for a,b in zip(x,y))
        if y==x:return path,False
        path.append(y);x=y
        if x==B:return path,True
    return path,False

def sensed(x,q,b,L,U):
    # Direct interval union per loss set.
    for lost in combinations(range(len(x)),q-1):
        left=[z for i,z in enumerate(x) if i not in lost]
        r=L
        ok=False
        for z in left:
            if z+b<r:continue
            if z-b>r:break
            r=z+b
            if r>=U:ok=True;break
        if not ok:return False
    return True

def chord(x,y,q,b,L,U):
    # Only crossing of coverage edges changes the interval test. Test each
    # closed event and the open strata, exactly with rationals.
    ends=[(z-b,w-z) for z,w in zip(x,y)]+[(z+b,w-z) for z,w in zip(x,y)]+[(L,0),(U,0)]
    times={F(0),F(1)}
    for (u,c),(v,d) in combinations(ends,2):
        if c!=d:
            t=F(v-u)/F(c-d)
            if 0<t<1:times.add(t)
    t=sorted(times)
    probes=t+[(a+b)/2 for a,b in zip(t,t[1:])]
    return all(sensed([a+p*(z-a) for a,z in zip(x,y)],q,b,L,U) for p in probes)

def guessed_order(A,B,v,q,box,g,R,b,L,U):
    n=len(A)
    assert all(x<=y for x,y in zip(A,B))
    assert 0<U-L
    outer=outside(n,q,box,g,R)
    marks=(L-b,U-b)
    state=[sum(x<s for x in A) for s in marks]
    seq=[]
    pins=[]
    def make():
        i,j=state
        if j>n-q:return None
        z=outer+span(i,j,q,b,L,U)
        for a,t in zip(state,marks):
            z += [(-1,h,t) if h<a else (h,-1,-t) for h in range(n)]
        return z
    seq.append(make())
    for i in reversed(range(n)):
        for j,t in enumerate(marks):
            if A[i]<t<=B[i]:
                state[j]-=1
                pins.append((len(seq),i,t))
                seq.append(make())
    assert state==[sum(x<s for x in B) for s in marks]
    if any(c is None for c in seq):return inf,None
    return lp(A,B,v,seq,monotone=True,pins=pins)

def main():
    counters=dict(wide_cases=0,lower_checks=0,chord_certified=0,uncertified=0)
    rng=Random(434088)
    for _ in range(90):
        n=rng.randrange(3,5);q=2;g=rng.randrange(1,4);b=rng.randrange(2,6);L=0;U=rng.randrange(g,g+5)
        v=tuple(rng.randrange(1,4) for _ in range(n));R=rng.randrange(q*g,q*g+7)
        box=[(-9,12)]*n;gaps=[g]*(n-1)
        C=setup(q,box,gaps,R,b,L,U)
        states=[x for x in combinations(range(-6,10),n) if any(holds(e,x) for e in C)]
        if not states:continue
        A=rng.choice(states)
        B=rng.choice([z for z in states if all(a<=x for a,x in zip(A,z))])
        gt=full(A,B,v,q,box,gaps,R,b,L,U)
        counters['wide_cases']+=1
        for h in (F(2),F(1),F(1,2)):
            steps=int(24/h)
            path,arrive=samples(A,B,v,C,h,steps)
            if arrive:
                t=(len(path)-1)*h
                assert float(max(F(0),t-h))<=gt+1e-6
                if all(chord(a,b_,q,b,L,U) for a,b_ in zip(path,path[1:])):
                    assert gt<=float(t)+1e-6
                    counters['chord_certified']+=1
                else:counters['uncertified']+=1
            else:
                assert gt>24-1e-6
            counters['lower_checks']+=1
    A=(-12,-3,2);B=(-2,3,12)
    p=(1,1,1);C=setup(2,[(-15,15)]*3,[5,5],14,4,-1,1)
    c,yes=samples(A,B,p,C,F(6),10)
    assert yes and not all(chord(a,b,2,4,-1,1) for a,b in zip(c,c[1:]))
    f,yes=samples(A,B,p,C,F(1,4),100)
    assert not yes
    p=((1,1,0),1,[(-10,15)]*3,[1]*2,10,5,5,9)
    A=(-2,-1,7);B=(5,6,7)
    assert isclose(full(A,B,*p),7)
    assert isclose(guessed_order(A,B,*p)[0],10)
    p=((2,4,4,3),2,[(-10,15)]*4,[3]*3,10,5,0,9)
    A=(-6,1,4,11);B=(1,4,8,11)
    assert isclose(full(A,B,*p),3.5)
    assert guessed_order(A,B,*p)[0]==inf
    print(json.dumps(counters,sort_keys=True))
if __name__=='__main__':main()
