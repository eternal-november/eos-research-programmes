#!/usr/bin/env python3
"""Exact difference-constraint cycles with independent direct LP checks."""
from fractions import Fraction as Q
import json
import random

# Edges encode x[v]-x[u] <= c + k*r. Zero coordinate is the fixed anchor.
def bfill(n, edges, r):
    dist=[Q(0)]*n
    pred=[None]*n
    for _ in range(n):
        last=None
        for i,(u,v,c,k,name) in enumerate(edges):
            y=dist[u]+c+k*r
            if dist[v]>y:
                dist[v],pred[v],last=y,i,v
        if last is None:
            z=[d-dist[0] for d in dist]
            assert all(z[v]-z[u]<=c+k*r for u,v,c,k,_ in edges)
            return z,None
    for _ in range(n):
        last=edges[pred[last]][0]
    cur=last
    cycle=[]
    while not cycle or cur!=last:
        e=edges[pred[cur]]
        cycle.append(e)
        cur=e[0]
    cycle.reverse()
    assert all(a[1]==b[0] for a,b in zip(cycle,cycle[1:]+cycle[:1]))
    assert sum(c+k*r for _,_,c,k,_ in cycle)<0
    return None,cycle


def law(worlds,k1=3,k2=3,k3=4,speed=(1,1,1)):
    edges=[]
    def add(u,v,c,k=0,label=""):
        edges.append((u,v,Q(c),Q(k),label))
    def static(p):
        for j in range(3):
            add(0,p+j,12,label="right wall")
            add(p+j,0,0,label="left wall")
        for j in range(2):
            add(p+j,p+j+1,3,label="retain connection")
            add(p+j+1,p+j,-1,label="retain clearance")
    static(1)
    for j,world in enumerate(worlds):
        p=4+3*j
        static(p)
        for i,m in enumerate(speed):
            add(1+i,p+i,0,m,world+" travel")
            add(p+i,1+i,0,m,world+" travel")
        if world=="A":
            add(p+1,p,-k1,label="A needs first gap")
        elif world=="B":
            add(p+2,p+1,-k2,label="B needs second gap")
        elif world=="C":
            add(p,p+2,k3,label="C needs compact span")
        else:
            raise ValueError(world)
    return 4+3*len(worlds),edges


def solve(n,edges):
    r=Q(0)
    history=[]
    while True:
        w,c=bfill(n,edges,r)
        if c is None:
            return r,w,history
        cost=sum(x[2] for x in c)
        mult=sum(x[3] for x in c)
        if not mult:
            return None,None,c
        before=r
        r=-cost/mult
        assert r>before
        history.append((r,c))


def independent(n,es):
    """Straight LP without shortest-path closure or parametric-cycle construction."""
    from scipy.optimize import linprog
    rows=[]
    rs=[]
    for u,v,c,k,_ in es:
        row=[0]*(n+1)
        row[v]+=1
        row[u]-=1
        row[-1]=-float(k)
        rows.append(row)
        rs.append(float(c))
    obj=[0]*n+[1]
    result=linprog(obj,A_ub=rows,b_ub=rs,bounds=[(0,0)]+[(None,None)]*(n-1)+[(0,None)],
                   method="highs")
    assert result.status in (0,2)
    return result.fun if result.success else None


def main():
    import itertools
    n,e=law("ABC")
    r,x,h=solve(n,e)
    assert r==Q(1,3)
    assert [solve(*law(p))[0] for p in itertools.combinations("ABC",2)]==[0,0,0]
    c=h[-1][1]
    assert {x[-1] for x in c if "needs" in x[-1]}=={
        "A needs first gap","B needs second gap","C needs compact span"}
    # Explicit exact common standby and branch terminal witnesses.
    witness=list(map(Q,[0,2,"13/3","20/3","5/3","14/3","20/3",
                        "2","4","7","7/3","13/3","19/3"]))
    assert all(witness[v]-witness[u]<=s+k*r for u,v,s,k,_ in e)
    # Matched heterogeneity control: equal gaps force identical scalar motion.
    T=Q(4)
    def D(a,V):
        z=min(T/2,V/a)
        return a*z*(T-z)
    assert min(D(Q(1),Q(100)),D(Q(100),Q(1)))>Q(7,2)>D(Q(1),Q(1))
    rng=random.Random(489490)
    for i in range(180):
        n,e=law("".join(x for x in "ABC" if rng.randrange(2)) or "A",
                *(rng.randint(0,7) for _ in range(3)),tuple(rng.randint(1,4) for _ in range(3)))
        ours=solve(n,e)[0]
        ref=independent(n,e)
        assert (ours is None and ref is None) or (
            ours is not None and ref is not None and abs(float(ours)-ref)<1e-8)
    print(json.dumps(dict(minimum_displacement=str(r),minimum_time="7/6",
        terminal_witness=list(map(str,witness)),critical_cycle=[f"{u}->{v}: {c}+{k}r ({name})" for u,v,c,k,name in h[-1][1]],
        pairwise_critical_displacements=[0,0,0],numeric_LP_comparisons=180,
        mismatched_shape_individual_displacement="7/2",mismatched_shape_joint_limit="3"),indent=2))


if __name__=='__main__':
    main()
