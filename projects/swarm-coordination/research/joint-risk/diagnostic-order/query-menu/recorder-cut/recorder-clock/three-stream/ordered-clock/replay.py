#!/usr/bin/env python3
"""Exact ordered acquisition bounds; includes independent permutation checks."""
from fractions import Fraction as Q
from itertools import product,permutations
import json
import random


def raw_bounds(anchor,stream,offset,eps):
    rows=[]
    for stamp,flag in sorted(stream):
        js=[i for i,s in enumerate(anchor,1) if abs(stamp-s-offset)<=eps]
        if not js:
            return None
        rows.append((js[0],js[-1],flag))
    return rows


def virtual_slots(anchor,stream,offset,eps):
    n=len(anchor)
    rows=raw_bounds(anchor,stream,offset,eps)
    if rows is None:
        return None
    failures=sum(p for _,_,p in rows)
    lower,upper=[],[]
    for r in range(n+1):
        force_f=sum(p and h<=r for l,h,p in rows)
        poss_f=sum(p and l<=r for l,h,p in rows)
        force_s=sum(not p and h<=r for l,h,p in rows)
        poss_s=sum(not p and l<=r for l,h,p in rows)
        lower.append(max(force_f,r-poss_s))
        upper.append(min(poss_f,r-force_s))
    if any(l>u for l,u in zip(lower,upper)):
        return None
    return [set(range(1+max(r for r,u in enumerate(upper) if u<k),
                      1+min(r for r,l in enumerate(lower) if l>=k)))
            for k in range(1,failures+1)],(lower,upper)


def cardinality(g):
    pos={}
    def add(i,seen):
        for p in g[i]:
            if p not in seen:
                seen.add(p)
                if p not in pos or add(pos[p],seen):
                    pos[p]=i
                    return True
        return False
    for i in range(len(g)):
        add(i,set())
    return len(pos)


def worst_from_slots(loc,initial):
    if any(x is None for x in loc):
        return None
    pool=[]
    for slots,_ in loc:
        if cardinality(slots)!=len(slots):
            return None
        pool.extend(g-initial for g in slots)
    return len(initial)+cardinality(pool)


def maximum(anchor,initial,streams,offset,eps):
    return worst_from_slots([virtual_slots(anchor,s,offset,eps) for s in streams],initial)


def bounds(anchor,initial,streams,offset,eps):
    loc=[virtual_slots(anchor,s,offset,eps) for s in streams]
    worst=worst_from_slots(loc,initial)
    if worst is None:
        return None
    frontier={(0,)*len(streams):(0,0)}
    for i in range(1,len(anchor)+1):
        nxt={}
        for prev,(a,b) in frontier.items():
            for bits in product((0,1),repeat=len(streams)):
                state=tuple(p+d for p,d in zip(prev,bits))
                if not all(l[i]<=x<=u[i] for x,(_, (l,u)) in zip(state,loc)):
                    continue
                tick=int(i in initial or any(bits))
                old=nxt.get(state,(a+tick,b+tick))
                nxt[state]=(min(old[0],a+tick),max(old[1],b+tick))
        frontier=nxt
    assert len(frontier)==1
    result=next(iter(frontier.values()))
    assert result[1]==worst
    return result


def exact_fixed(anchor,initial,streams,offset,eps):
    keys=[]
    n=len(anchor)
    for s in streams:
        masks=set()
        for p in permutations(range(n)):
            if all(abs(s[j][0]-anchor[i]-offset)<=eps for i,j in enumerate(p)):
                masks.add(frozenset(i+1 for i,j in enumerate(p) if s[j][1]))
        if not masks:
            return None
        keys.append(masks)
    score=[len(initial.union(*xs)) for xs in product(*keys)]
    return min(score),max(score)


def common_cells(anchor,streams,eps,lo,hi):
    breaks=sorted({lo,hi}|{t-s+delta for stream in streams for t,_ in stream
                            for s in anchor for delta in [-eps,eps] if lo<=t-s+delta<=hi})
    return sorted(breaks+[(x+y)/2 for x,y in zip(breaks,breaks[1:])])


def exact_shared(anchor,initial,streams,eps,lo,hi):
    """No cell decomposition: intersect every per-assignment offset range."""
    schedule=[]
    for s in streams:
        source=[]
        for p in permutations(range(len(anchor))):
            d=[s[j][0]-anchor[i] for i,j in enumerate(p)]
            left,right=max(lo,max(d)-eps),min(hi,min(d)+eps)
            if left<=right:
                source.append((left,right,{i+1 for i,j in enumerate(p) if s[j][1]}))
        schedule.append(source)
    values=[len(initial.union(*(t[2] for t in branch))) for branch in product(*schedule)
            if max(t[0] for t in branch)<=min(t[1] for t in branch)]
    return (min(values),max(values)) if values else None


def main():
    a=tuple(map(Q,[0,1,3]))
    ss=[[(Q(0),0),(Q(1,2),0),(Q(2),1)],
        [(Q(0),0),(Q(1),0),(Q(3),1)]]
    assert bounds(a,set(),ss,Q(0),Q(1))==(1,1)
    untyped=[set(range(l,h+1)) for s in ss for l,h,f in raw_bounds(a,s,Q(0),Q(1)) if f]
    assert cardinality(untyped)==2
    rng=random.Random(497)
    fixedfeasible=0
    for i in range(440):
        n=rng.randrange(1,6)
        a=sorted(Q(rng.randrange(-4,9),2) for _ in range(n))
        initial={i+1 for i in range(n) if rng.randrange(5)==0}
        ss=[[(Q(rng.randrange(-4,9),2),rng.randrange(2)) for _ in a]
            for _ in range(rng.randrange(1,5))]
        offset,eps=Q(rng.randrange(-3,4),2),Q(rng.randrange(9),2)
        got=bounds(a,initial,ss,offset,eps)
        assert got==exact_fixed(a,initial,ss,offset,eps)
        fixedfeasible+=got is not None
    for i in range(90):
        n=rng.randrange(1,5)
        a=sorted(Q(rng.randrange(9),2) for _ in range(n))
        initial={i+1 for i in range(n) if rng.randrange(5)==0}
        ss=[[(Q(rng.randrange(9),2),rng.randrange(2)) for _ in a]
            for _ in range(rng.randrange(1,4))]
        eps,lo,hi=Q(rng.randrange(5),2),Q(-2),Q(2)
        cells=[bounds(a,initial,ss,d,eps) for d in common_cells(a,ss,eps,lo,hi)]
        v=[t for t in cells if t is not None]
        got=(min(t[0] for t in v),max(t[1] for t in v)) if v else None
        assert got==exact_shared(a,initial,ss,eps,lo,hi)
    # 24 streams: only the polynomial path is run. Tight stamp intervals fix each pair.
    a=list(map(Q,range(60)))
    ss=[[(t,rng.randrange(10)==0) for t in a] for _ in range(24)]
    expected=sum(any(stream[i][1] for stream in ss) for i in range(len(a)))
    assert maximum(a,set(),ss,Q(0),Q(1,4))==expected
    print(json.dumps(dict(fixed_offset_cases=440,feasible_fixed=fixedfeasible,
        larger_matching_only={"streams":24,"episodes":60,"exact_worst":expected},
        shared_offset_cases=90,constrained_worst=1,discarding_success_intervals_worst=2),indent=2))


if __name__=='__main__':
    main()
