#!/usr/bin/env python3
"""Sharp empirical union-count bounds under a single shared clock offset."""
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import collections
import json
import random
import sys


def assign(cost):
    """Minimum-cost square assignment, primal-dual augmenting paths, integer costs."""
    n = len(cost)
    u,v,p,way = ([0]*(n+1) for _ in range(4))
    for i in range(1,n+1):
        p[0]=i
        j0=0
        slack=[None]*(n+1)
        seen=[False]*(n+1)
        while True:
            seen[j0]=True
            i0=p[j0]
            for j in range(1,n+1):
                if not seen[j]:
                    c=cost[i0-1][j-1]-u[i0]-v[j]
                    if slack[j] is None or c<slack[j]:
                        slack[j],way[j]=c,j0
            j1=min((j for j in range(1,n+1) if not seen[j]),key=slack.__getitem__)
            d=slack[j1]
            for j in range(n+1):
                if seen[j]:
                    u[p[j]]+=d
                    v[j]-=d
                else:
                    slack[j]-=d
            j0=j1
            if p[j0]==0:
                break
        while j0:
            j1=way[j0]
            p[j0]=p[j1]
            j0=j1
    inverse=[None]*n
    for j in range(1,n+1):
        inverse[p[j]-1]=j-1
    # Check the primal-dual certificate, including the artificial costs.
    assert all(u[i+1]+v[j+1]<=cost[i][j] for i in range(n) for j in range(n))
    assert all(u[i+1]+v[j+1]==cost[i][j] for i,j in enumerate(inverse))
    return tuple(inverse)


def union(a,b,p):
    return sum(a[i] or b[j] for i,j in enumerate(p))


def extrema(graph,a,b):
    n=len(a)
    assert n and len(graph)==len(b)==n
    def solve(invert):
        m=assign([[n+1 if j not in graph[i] else int(a[i] or b[j])^invert
                   for j in range(n)] for i in range(n)])
        return None if any(j not in graph[i] for i,j in enumerate(m)) else (union(a,b,m),m)
    lo,hi=solve(0),solve(1)
    assert (lo is None)==(hi is None)
    return (lo,hi) if lo else None


def invariant(graph,a,b,m):
    """All assignments have the reference count iff each active SCC has a potential."""
    n=len(m)
    inv={j:i for i,j in enumerate(m)}
    g=[[inv[j] for j in row] for row in graph]
    reverse=[[] for _ in m]
    for i,row in enumerate(g):
        for j in row:
            reverse[j].append(i)
    done=set()
    order=[]
    for i in range(n):
        if i in done:
            continue
        done.add(i)
        stack=[(i,iter(g[i]))]
        while stack:
            j,it=stack[-1]
            k=next(it,None)
            if k is None:
                order.append(j)
                stack.pop()
            elif k not in done:
                done.add(k)
                stack.append((k,iter(g[k])))
    labels=[None]*n
    for r in reversed(order):
        if labels[r] is not None:
            continue
        labels[r]=r
        stack=[r]
        while stack:
            i=stack.pop()
            for j in reverse[i]:
                if labels[j] is None:
                    labels[j]=r
                    stack.append(j)
    potentials=[None]*n
    for r in range(n):
        if labels[r]!=r:
            continue
        potentials[r]=0
        stack=[r]
        while stack:
            i=stack.pop()
            for j in g[i]:
                if labels[j]!=r:
                    continue
                cost=int(a[i] or b[m[j]])-int(a[i] or b[m[i]])
                x=potentials[i]+cost
                if potentials[j] is None:
                    potentials[j]=x
                    stack.append(j)
                elif potentials[j]!=x:
                    return False
    return True


def cells(left,right,eps,lo,hi):
    assert len(left)==len(right) and lo<=hi and eps>=0
    D=[[y-x for y in right] for x in left]
    breaks=sorted({lo,hi}|{p for row in D for d in row
                           for p in [d-eps,d+eps] if lo<=p<=hi})
    for q in sorted(breaks+[(x+y)/2 for x,y in zip(breaks,breaks[1:])]):
        yield q,tuple({j for j,d in enumerate(row) if abs(d-q)<=eps} for row in D)


def clock_bounds(left,right,a,b,eps,lo,hi):
    all_cells=list(cells(left,right,eps,lo,hi))
    outer=tuple(set().union(*(g[i] for _,g in all_cells)) for i in range(len(a)))
    fitted=[]
    for q,g in all_cells:
        x=extrema(g,a,b)
        if not x:
            continue
        low,high=x
        assert invariant(g,a,b,low[1])==(low[0]==high[0])
        fitted.append(((low[0],q,low[1]),(high[0],q,high[1])))
    return ((min(l for l,_ in fitted),max(h for _,h in fitted)) if fitted else None,
            extrema(outer,a,b))


def poly_oracle(left,right,a,b,eps,lo,hi):
    # Independent direct characterization: intersect the whole offset interval for each permutation.
    for p in permutations(range(len(a))):
        d=[right[j]-left[i] for i,j in enumerate(p)]
        if max(lo,max(d)-eps)<=min(hi,min(d)+eps):
            yield union(a,b,p)


CASES={
    "shared_offset": (Q(1,2),Q(-2),Q(2)),
    "stable_union": (Q(1),Q(0),Q(0)),
    "ambiguous_union": (Q(1),Q(0),Q(0)),
    "inconsistent": (Q(1,2),Q(-2),Q(2)),
    "closed_boundary": (Q(1,2),Q(-1),Q(2)),
}


def recorded(lines):
    groups=collections.defaultdict(list)
    for line in lines:
        topic,payload,rx,tx,seq=line.split()
        name,idx,stamp,fail=payload.split(',')
        assert topic in ('A','B') and int(seq)==0
        groups[name,topic].append((int(idx),Q(stamp),int(fail)))
    reported={}
    for name,(eps,lo,hi) in CASES.items():
        out=[]
        for topic in ('A','B'):
            rows=sorted(groups.pop((name,topic)))
            assert [i for i,_,_ in rows]==list(range(len(rows)))
            out.extend((list(x for _,x,_ in rows),list(f for _,_,f in rows)))
        xs,a,ys,b=out
        sharp,relaxed=clock_bounds(xs,ys,a,b,eps,lo,hi)
        possible=set(poly_oracle(xs,ys,a,b,eps,lo,hi))
        assert ((sharp[0][0],sharp[1][0]) if sharp else None)==(
            (min(possible),max(possible)) if possible else None)
        reported[name]={"possible_counts":sorted(possible),
            "edge_union_range":[relaxed[0][0],relaxed[1][0]] if relaxed else None,
            "offset_witnesses":[str(sharp[0][1]),str(sharp[1][1])] if sharp else None}
    assert not groups
    assert reported["shared_offset"]["possible_counts"]==[1]
    assert reported["shared_offset"]["edge_union_range"]==[1,2]
    assert reported["stable_union"]["possible_counts"]==[2]
    assert reported["ambiguous_union"]["possible_counts"]==[1,2]
    assert reported["inconsistent"]["possible_counts"]==[]
    assert reported["inconsistent"]["edge_union_range"]==[1,1]
    assert reported["closed_boundary"]["offset_witnesses"]==['1/2','1/2']
    return reported


def validate():
    feasible=constant=0
    for n in range(1,4):
        bits=tuple(product((0,1),repeat=n))
        for mask in range(1<<(n*n)):
            g=tuple({j for j in range(n) if mask>>(i*n+j)&1} for i in range(n))
            ps=[p for p in permutations(range(n)) if all(j in g[i] for i,j in enumerate(p))]
            if not ps:
                # Hall failure: check both optimization directions on one labeling.
                assert extrema(g,bits[0],bits[0]) is None
                continue
            for a,b in product(bits,repeat=2):
                x,y=extrema(g,a,b)
                actual={union(a,b,p) for p in ps}
                assert (x[0],y[0])==(min(actual),max(actual))
                assert invariant(g,a,b,x[1])==(len(actual)==1)
                feasible+=1
                constant+=len(ps)>1 and len(actual)==1
    g=tuple({i,j} for i,j in enumerate((2,3,1,0)))
    a=b=(1,1,0,0)
    assert {union(a,b,p) for p in permutations(range(4))
            if all(j in g[i] for i,j in enumerate(p))}=={2,4}
    rng=random.Random(395488)
    for k in range(800):
        n=rng.randrange(1,6)
        x,y=(list(map(Q,rng.sample(range(-5,9),n))) for _ in range(2))
        a,b=(tuple(rng.randrange(2) for _ in range(n)) for _ in range(2))
        eps,lo,hi=Q(rng.randrange(7),2),Q(-2),Q(2)
        got=clock_bounds(x,y,a,b,eps,lo,hi)[0]
        want=list(poly_oracle(x,y,a,b,eps,lo,hi))
        assert ((got[0][0],got[1][0]) if got else None)==(
            (min(want),max(want)) if want else None)
    return dict(feasible_graph_outcomes=feasible,multiple_joins_fixed_count=constant,clock_random=800)


if __name__=='__main__':
    print(json.dumps({"capture":recorded(Path(sys.argv[1]).read_text().splitlines()),
                      "checks":validate()},sort_keys=True,indent=2))
