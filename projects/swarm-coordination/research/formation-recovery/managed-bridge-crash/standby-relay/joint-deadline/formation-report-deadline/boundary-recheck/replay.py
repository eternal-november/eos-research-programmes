#!/usr/bin/env python3
"""Exact terminal constraint certificates and a full-graph comparison."""
from fractions import Fraction as Q
import itertools
import json
import random


def solve(n,edges):
    dist=[Q(0)]*n
    for i in range(n):
        changed=False
        for u,v,c in edges:
            if dist[v]>dist[u]+c:
                dist[v]=dist[u]+c
                changed=True
        if not changed:
            assert all(dist[v]-dist[u]<=c for u,v,c in edges)
            return dist
    return None


def paths(n,edges,s):
    d=[None]*n
    d[s]=Q(0)
    for _ in range(n-1):
        has=False
        for u,v,c in edges:
            if d[u] is not None and (d[v] is None or d[v]>d[u]+c):
                d[v]=d[u]+c
                has=True
        if not has:
            break
    assert all(d[u] is None or d[v] is not None and d[v]<=d[u]+c for u,v,c in edges)
    return d


class Cut:
    def __init__(self,n,base,terminals):
        self.n=n
        self.t=tuple(terminals)
        self.indices={x:i for i,x in enumerate(self.t)}
        assert len(self.indices)==len(self.t)
        self.q=solve(n,base)
        assert self.q is not None
        self.ds=[paths(n,base,s) for s in self.t]
        self.edges=[(i,j,row[s]) for i,row in enumerate(self.ds)
                    for j,s in enumerate(self.t) if i!=j and row[s] is not None]

    def test(self,delta):
        small=[(self.indices[u],self.indices[v],c) for u,v,c in delta]
        return solve(len(self.t),self.edges+small) if self.t else []

    def lift(self,terminal):
        if not self.t:
            return list(self.q)
        assert all(terminal[v]-terminal[u]<=c for u,v,c in self.edges)
        M=max(x-self.q[s] for x,s in zip(terminal,self.t))
        return [min([M+self.q[w]]+
                    [terminal[i]+r[w] for i,r in enumerate(self.ds) if r[w] is not None])
                for w in range(self.n)]


def full_comparison(n,base,ends,changes):
    c=Cut(n,base,ends)
    res=c.test(changes)
    raw=solve(n,base+changes)
    assert (res is None)==(raw is None)
    if res is not None:
        learned=c.lift(res)
        assert [learned[t] for t in ends]==res
        assert all(learned[v]-learned[u]<=w for u,v,w in base+changes)
    return res


def main():
    rng=random.Random(494)
    matches=lifts=0
    joint=0
    for _ in range(780):
        n=rng.randrange(3,20)
        p=[Q(rng.randrange(-12,12),2) for _ in range(n)]
        base=[(x,y,p[y]-p[x]+Q(rng.randrange(0,13),3))
              for x,y in itertools.permutations(range(n),2) if rng.randrange(6)==0]
        s=rng.sample(range(n),rng.randrange(1,min(n,6)+1))
        d=[(rng.choice(s),rng.choice(s),Q(rng.randrange(-16,16),4))
           for _ in range(rng.randrange(6))]
        out=full_comparison(n,base,s,d)
        matches+=1
        lifts+=out is not None
        joint+=bool(out is None and d and all(solve(n,base+[a]) is not None for a in d))
        if rng.randrange(4)==0:
            # Independent projection test: force an arbitrary terminal assignment
            # via two bounds to an extra zero-reference coordinate.
            c=Cut(n,base,s)
            places=[Q(rng.randrange(-18,19),2) for _ in s]
            pin=[(n,u,z) for u,z in zip(s,places)]+[(u,n,-z) for u,z in zip(s,places)]
            raw=solve(n+1,base+pin)
            portable=all(places[v]-places[u]<=w for u,v,w in c.edges)
            assert (raw is not None)==portable
            if portable:
                assert all(c.lift(places)[u]==z for u,z in zip(s,places))
    # Simultaneous clearance requirements are individually feasible with the
    # uncoupled internal links but jointly violate the retained outer-span cap.
    base=[(0,3,Q(4)),(3,2,Q(0))]
    pending=[(1,0,Q(-3)),(2,1,Q(-3))]
    assert all(full_comparison(4,base,[0,1,2],[q]) is not None for q in pending)
    assert full_comparison(4,base,[0,1,2],pending) is None
    # One-edge distinguishability and a lawful loosening through a replaceable edge.
    assert full_comparison(4,base,[0,2],[(2,0,Q(-5))]) is None
    base10=[(0,3,Q(10)),(3,2,Q(0))]
    delta=[(2,0,Q(-7))]
    assert full_comparison(4,base10,[0,2],delta) is not None
    assert full_comparison(4,base10+[(0,2,Q(4))],[0,2],delta) is None
    count=[]
    for length in [12,80,500]:
        structural=[(i,i+1,Q(4,length)) for i in range(length)]
        split=length//2
        subs=[0,split,length]
        c=Cut(length+1,structural,subs)
        assert c.test([(split,0,Q(-3))]) is None  # half-span directed bound = 2
        assert c.test([(length,0,Q(-4))]) is not None
        count.append([len(structural)+1,len(c.edges)+1])
    grid=(Q(1),Q(3,2),Q(2))
    pairs=list(itertools.permutations(range(3),2))
    seen=set()
    for choice in itertools.product(grid,repeat=len(pairs)):
        base=[(u,v,c) for (u,v),c in zip(pairs,choice)]
        signature=tuple(solve(3,base+[(v,u,-r)]) is not None
                        for u,v in pairs for r in grid)
        assert signature not in seen
        seen.add(signature)
    assert len(seen)==729
    print(json.dumps(dict(full_graph_comparisons=matches,lifted_assignments=lifts,
        seeded_failures_in_joint_only=joint,distinct_three_terminal_signatures=len(seen),
        small_joint_only_failures="two individually viable local changes fail together",
        large_base_vs_boundary_edges=count),indent=2))


if __name__=="__main__":
    main()
