#!/usr/bin/env python3
"""Exact strict endpoint testing with an independent non-strict oracle."""
from itertools import combinations,product
from pathlib import Path
from random import Random
import json

ROOT=Path(__file__).resolve().parent
from importlib.util import spec_from_file_location, module_from_spec
spec=spec_from_file_location("integer_baseline",ROOT.parent/"replay.py")
parent=module_from_spec(spec)
spec.loader.exec_module(parent)
flow,schedule,close,sat=parent.flow,parent.schedule,parent.close,parent.sat


FAR=(10**12,0)


def plus(p,q):
    return (p[0]+q[0],min(p[1],q[1]))


def stn(n,edges):
    D=[[FAR]*n for _ in range(n)]
    for i in range(n):D[i][i]=(0,0)
    for i,j,w,s in edges: D[i][j]=min(D[i][j],(w,-s))
    for k in range(n):
        for i in range(n):
            if D[i][k]==FAR: continue
            for j in range(n):
                if D[k][j]!=FAR:
                    D[i][j]=min(D[i][j],plus(D[i][k],D[k][j]))
    return D


def good(D):
    return all(D[i][i]>=(0,0) for i in range(len(D)))


def active(jobs,S,t):
    return [(0,jobs[i][0],t,jobs[i][3]) for i in S]+[(jobs[i][1],0,-t,jobs[i][4]) for i in S]


def method(D,jobs,t):
    I=[]
    n=len(D)
    for i,(e,x,w,a,b) in enumerate(jobs):
        if any(p<(0,0) for p in (plus((t,-a),D[e][0]),
                                 plus((-t,-b),D[0][x]),
                                 plus(D[e][x],(0,-(a or b))))):continue
        I.append(i)
    R={(i,j) for i,j in product(I,repeat=2) if i!=j
       and plus(D[jobs[j][0]][jobs[i][1]],(0,-(jobs[i][4] or jobs[j][3])))<(0,0)}
    assert all((j,i) not in R for i,j in R)
    assert all((i,k) in R for i,j in R for p,k in R if j==p)
    pos={i:k for k,i in enumerate(I)}
    total=sum(jobs[i][2] for i in I)
    m=len(I)
    arcs=[(2*m,pos[i],jobs[i][2]) for i in I]
    arcs += [(m+pos[i],2*m+1,jobs[i][2]) for i in I]
    arcs += [(pos[i],m+pos[j],total+1) for i,j in R]
    f,Z=flow(2*m+2,arcs,2*m,2*m+1)
    selected=[i for i in I if pos[i] in Z and m+pos[i] not in Z]
    assert sum(jobs[i][2] for i in selected)==total-f
    return total-f,selected


def nonstrict(n,edges):
    return [(i,j,w*(n+1)-s) for i,j,w,s in edges]


def verify():
    rng=Random(527)
    timecuts=subsets=ties=old_strict=abs_updates=0
    for case in range(140):
        m=rng.randrange(2,7)
        n=2*m+1
        jobs=[(2*i+1,2*i+2,rng.randrange(1,9),rng.randrange(2),rng.randrange(2))
              for i in range(m)]
        moments=[0]
        for _,_,_,a,b in jobs:
            t=rng.randrange(13)
            dur=rng.randrange(a&b,7)
            moments.extend([t,t+dur])
            ties+=dur==0
        es=[(x,e,0,a&b) for e,x,w,a,b in jobs]
        for i,j in product(range(n),repeat=2):
            if i!=j and rng.random()<.22:
                slack=rng.randrange(6)
                strict=int(slack>0 and rng.random()<.5)
                es.append((i,j,moments[j]-moments[i]+slack,strict))
                old_strict+=strict
        D=stn(n,es)
        assert good(D)
        rel=[ed for ed in es if 0 not in ed[:2]]
        rel_D=stn(n,rel)
        hybrid=[row.copy() for row in rel_D]
        for i in range(n):
            hybrid[0][i]=D[0][i]
            hybrid[i][0]=D[i][0]
        for t in range(-1,18):
            w,S=method(D,jobs,t)
            assert method(hybrid,jobs,t)[0]==w
            abs_updates+=1
            alloc=schedule(n,nonstrict(n,es+active(jobs,S,t)))
            assert alloc is not None
            scaled=t*(n+1)
            obs=sum(q for e,x,q,a,b in jobs
                    if (alloc[e] < scaled or (not a and alloc[e]==scaled))
                    and (scaled < alloc[x] or (not b and scaled==alloc[x])))
            assert obs==w
            timecuts+=1
            if case<50 and t in (1,4,7,9,12):
                oracle=0
                for k in range(m+1):
                    for sub in combinations(range(m),k):
                        e=es+active(jobs,sub,t)
                        chk=sat(close(n,nonstrict(n,e)))
                        assert chk==good(stn(n,e))
                        if chk: oracle=max(oracle,sum(jobs[i][2] for i in sub))
                        subsets+=1
                assert w==oracle
    # A=[-1,u], B=(u,v), C=[v,1], constants encoded at half-tick resolution.
    J=[(1,2,1,0,0),(2,3,1,1,1),(3,4,1,0,0)]
    E=[(0,1,-2,0),(1,0,2,0),(0,2,0,0),(2,0,1,0),
       (0,3,1,0),(3,0,0,0),(0,4,2,0),(4,0,-2,0)]
    assert [good(stn(5,E+active(J,s,0))) for s in [(0,),(1,),(2,),(0,1),(1,2),(0,2)]]==[True,True,True,False,False,True]
    E.append((3,2,0,1)) # force B positive; restores the transitive third conflict
    assert not good(stn(5,E+active(J,(0,2),0)))
    assert method(stn(5,E),J,0)[0]==1
    return dict(exact_real_schedule_witnesses=timecuts,old_strict_edges=old_strict,
                boundary_reuse_comparisons=abs_updates,full_active_subsets=subsets,
                zero_duration_samples=ties,zero_open_breaks_transitivity=True)


if __name__=="__main__":
    print(json.dumps(verify(),indent=2))
