"""Compile physical tile chains into checked source transit laws.

No private source truth is published to the controller on import.
Interior tile passage has no control/effect under the declared grammar.
"""
from import_topology import matrix
from collections import defaultdict
from collections import deque
from itertools import product
from math import inf
import json

def cells(dims,vals,level=0):
    Z,N,M=dims
    vals=vals[level*N*M:(level+1)*N*M]
    P={(r,c) for r in range(N) for c in range(M) if vals[r*M+c]}
    E={(a,b) for a in P for b in [(a[0]+1,a[1]),(a[0],a[1]+1)] if b in P}
    A={u:set() for u in P}
    for a,b in E:A[a].add(b);A[b].add(a)
    return A

def development_cells(path="development-topology.json"):
    with open(path,encoding="utf8") as f:d=json.load(f)
    assert d["schema"]=="subt-planar-1"
    dims=d["dims"];Z,N,M=dims
    assert Z==1 and 1<=N<=512 and 1<=M<=512
    vals=[0]*(N*M)
    for r,c,x in d["occupied"]:
        assert 0<=r<N and 0<=c<M and x in (1,10) and not vals[r*M+c]
        vals[r*M+c]=x
    return cells(dims,vals)

def chains(A,pins):
    cut=set(pins)|{x for x in A if len(A[x])!=2}
    rem=set(A)
    while rem:
        first=min(rem);Q=[first];rem.remove(first)
        for u in Q:
            for v in A[u]&rem:rem.remove(v);Q.append(v)
        if not (cut&set(Q)):
            # Pure cycle. Retain two deterministic anchors so nonempty
            # round trips have a real intermediate checkpoint.
            cut.add(min(Q));cut.add(max(Q))
    visited=set()
    C=[]
    added=set()
    for u in sorted(cut):
        for v in sorted(A[u]):
            if (u,v) in visited:continue
            trail=[u,v]
            while trail[-1] not in cut:
                prev,w=trail[-2:]
                rem=A[w]-{prev}
                assert len(rem)==1
                trail.append(next(iter(rem)))
            if trail[0]==trail[-1]:
                j=trail.index(min(trail[1:-1]))
                added.add(trail[j])
                C.extend((tuple(trail[:j+1]),tuple(trail[j:])))
            else:C.append(tuple(trail))
            for a,b in zip(trail,trail[1:]):visited.update([(a,b),(b,a)])
    assert len(visited)==sum(len(v) for v in A.values())
    return cut|added,C

def windows(path,dur,out):
    """List (physical edge, offset, length, outages) in ordered chain."""
    z=0;items=[]
    for a,b in zip(path,path[1:]):
        end=dur[a,b];assert type(end) is int and end>=1
        W=out.get((a,b),())
        items.append(((a,b),z,end,tuple(W)));z+=end
    return items,z

def merged(W):
    out=[]
    for a,b in sorted(W):
        if b<=a:continue
        if out and a<=out[-1][1]:out[-1]=(out[-1][0],max(b,out[-1][1]))
        else:out.append((a,b))
    return tuple(out)

def forbidden(path,duration,outages):
    segs,D=windows(path,duration,outages)
    W=merged([(max(0,l-o-d+1),u-o) for _,o,d,E in segs for l,u in E])
    return D,W

def physical(path,duration,outages,t):
    for a,b in zip(path,path[1:]):
        d=duration[a,b]
        for q in range(t,t+d):
            if any(l<=q<u for l,u in outages.get((a,b),())):return False
        t+=d
    return True

def can_enter(t,forbidden_starts):
    return not any(a<=t<b for a,b in forbidden_starts)

def shortest(left,C,compiled,start,end,deadline):
    """Exact finite transit at externally declared action boundaries."""
    A=defaultdict(list)
    for name,path in enumerate(C):A[path[0]].append((name,path[-1]))
    reach={(start,left)}
    for t in range(left,deadline+1):
        for u in sorted({u for u,q in reach if q==t}):
            if u==end:return t
            reach.add((u,t+1))
            for name,v in A[u]:
                d,W=compiled[name]
                if t+d<=deadline and can_enter(t,W):reach.add((v,t+d))
    return None
