"""Exact audit of short finite closed-cell route LPs with rational certificates."""
from fractions import Fraction as F
from itertools import combinations
from math import inf,isclose
from random import Random
import json
import numpy as np
from scipy.optimize import linprog
from exact_ref import outside,span,full
from projection import setup,samples,chord

def in_cell(E,x):
    at=lambda i:0 if i<0 else x[i]
    return all(at(j)-at(i)<=c for i,j,c in E)

def intersect(a,b,n):
    # Each cell uses -1 for the reference node. Shift all potentials by the
    # reference value at the end so that this node is zero.
    p=[F(0)]*(n+1)
    for _ in range(n+1):
        changed=False
        for u,v,w in a+b:
            z=p[u]+w
            if z<p[v]:p[v]=z;changed=True
        if not changed:return True
    return False

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))

def rational(x):
    return tuple(F(float(z)).limit_denominator(1000000) for z in x)

def solve_lp(A,B,v,route):
    # Every variable free; positive durations and equality endpoints
    # explicitly represented as inequalities for exact dual auditing.
    n=len(v);m=len(route);d=n*(m+1)+m;T=n*(m+1)
    rows=[];rhs=[]
    def add(items,b):
        r=[F(0)]*d
        for j,c in items:r[j]+=c
        rows.append(tuple(r));rhs.append(b)
    for k,E in enumerate(route):
        for cut in (k,k+1):
            for i,j,c in E:
                terms=[]
                if i>=0:terms.append((cut*n+i,-1))
                if j>=0:terms.append((cut*n+j,1))
                add(terms,c)
        add([(T+k,-1)],0)
        for i,u in enumerate(v):
            for p in (-1,1):
                add([(k*n+i,-p),((k+1)*n+i,p),(T+k,-u)],0)
    for k,point in ((0,A),(m,B)):
        for i,x in enumerate(point):
            for p in (-1,1):add([(k*n+i,p)],p*x)
    c=tuple([0]*T+[1]*m)
    mat=np.asarray(rows,dtype=float)
    ans=linprog(c,A_ub=mat,b_ub=np.asarray(rhs,dtype=float),bounds=[(None,None)]*d,method="highs")
    cols=list(zip(*rows))
    if ans.status==2:
        f=linprog([0]*len(rows),A_eq=np.vstack([mat.T,np.asarray(rhs,dtype=float)]),b_eq=[0]*d+[-1],
                  bounds=(0,None),method="highs")
        assert f.success,f.message
        y=rational(f.x)
        assert all(a>=0 for a in y) and all(dot(col,y)==0 for col in cols) and dot(rhs,y)==-1
        return None
    assert ans.success,ans.message
    x=rational(ans.x);y=rational(ans.ineqlin.marginals)
    assert all(dot(r,x)<=v0 for r,v0 in zip(rows,rhs)),("primal",ans.message)
    assert all(a<=0 for a in y) and all(dot(col,y)==v0 for col,v0 in zip(cols,c)),("dual",ans.message)
    assert dot(c,x)==dot(rhs,y),("exact optimum",ans.message)
    return (dot(c,x),tuple(tuple(x[k*n:k*n+n]) for k in range(m+1)),x[T:])

def exact(A,B,v,cells):
    n=len(v);goals={i for i,c in enumerate(cells) if in_cell(c,B)}
    starts=[i for i,c in enumerate(cells) if in_cell(c,A)]
    assert starts and goals
    ed={i:[j for j,c in enumerate(cells) if j!=i and intersect(cells[i],c,n)] for i in range(len(cells))}
    best=None;solved=bad=0
    def dfs(seq):
        nonlocal best,solved,bad
        i=seq[-1]
        if i in goals:
            r=solve_lp(A,B,v,[cells[k] for k in seq])
            solved+=1
            if r is None:bad+=1
            elif best is None or best[0]>r[0]:best=r
            # Any trajectory starting this stay can go directly to B inside it.
            return
        for j in ed[i]:
            if j not in seq:dfs([*seq,j])
    for i in starts:dfs([i])
    return best,solved,bad

def instances():
    rng=Random(434088)
    for _ in range(90):
        n=rng.randrange(3,5);q=2;g=rng.randrange(1,4);b=rng.randrange(2,6);L=0;U=rng.randrange(g,g+5)
        v=tuple(rng.randrange(1,4) for _ in range(n));R=rng.randrange(q*g,q*g+7)
        box=[(-9,12)]*n;gaps=[g]*(n-1)
        C=setup(q,box,gaps,R,b,L,U)
        states=[x for x in combinations(range(-6,10),n) if any(in_cell(e,x) for e in C)]
        if not states:continue
        A=rng.choice(states)
        B=rng.choice([z for z in states if all(a<=x for a,x in zip(A,z))])
        yield A,B,(v,q,box,gaps,R,b,L,U)
    # Positive wide examples and a continuous disconnection at a real clearance.
    yield (-2,-1,7),(5,6,7),((1,1,0),1,[(-10,15)]*3,[1]*2,10,5,5,9)
    yield (-6,1,4,11),(1,4,8,11),((2,4,4,3),2,[(-10,15)]*4,[3]*3,10,5,0,9)
    yield (-12,-3,2),(-2,3,12),((1,1,1),2,[(-15,15)]*3,[5,5],14,4,-1,1)
    # Static cell graph is connected but the fixed robot cannot move.
    yield (0,2),(1,2),((0,1),1,[(-1,4)]*2,[1],8,4,1,3)

def mixed_cases():
    rng=Random(7862401)
    hits=0
    while hits<24:
        n=rng.randrange(3,5);q=2;g=rng.randrange(1,4);b=rng.randrange(3,6);L=0;U=rng.randrange(g,g+4)
        v=tuple(rng.randrange(1,5) for _ in range(n))
        R=rng.randrange(q*g,q*g+7);box=[(-8,11)]*n;gaps=[g]*(n-1)
        C=setup(q,box,gaps,R,b,L,U)
        states=[x for x in combinations(range(-5,9),n) if any(in_cell(e,x) for e in C)]
        if len(states)<2:continue
        A,B=rng.sample(states,2)
        if all(a<=z for a,z in zip(A,B)) or all(z<=a for a,z in zip(A,B)):continue
        hits+=1
        yield A,B,(v,q,box,gaps,R,b,L,U)

def main():
    rows={"mixed_pairs":0,"old_ascending":0,"special":[],"certified_routes":0,"infeasible_lp":0,"direct_chords":0}
    for i,(A,B,p) in enumerate([*instances(),*mixed_cases()]):
        v,q,box,g,R,b,L,U=p
        C=setup(q,box,g,R,b,L,U)
        ans,n,k=exact(A,B,v,C)
        t=full(A,B,*p)
        assert isclose(inf if ans is None else float(ans[0]),t,abs_tol=1e-7),(A,B,t,ans)
        rows["certified_routes"]+=n;rows["infeasible_lp"]+=k
        if i<77:
            assert ans is not None
            rows["old_ascending"]+=1
        elif i<81:rows["special"].append(None if ans is None else str(ans[0]))
        else:rows["mixed_pairs"]+=1
        if ans:
            for x,y,dt in zip(ans[1],ans[1][1:],ans[2]):
                assert dt>=0 and all(abs(w-z)<=a*dt for z,w,a in zip(x,y,v))
                assert chord(x,y,q,b,L,U)
                rows["direct_chords"]+=1
    assert rows["old_ascending"]==77 and rows["mixed_pairs"]==24 and rows["special"]==["7","7/2",None,None]
    print(json.dumps(rows,sort_keys=True,separators=(",",":")))
if __name__=="__main__":
    main()
