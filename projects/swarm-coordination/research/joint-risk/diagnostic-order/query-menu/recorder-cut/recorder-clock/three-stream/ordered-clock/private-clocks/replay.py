#!/usr/bin/env python3
"""Compare paired timestamp linkages and MaxSAT with exact rational arithmetic."""
from fractions import Fraction as Q
from itertools import permutations,product
import json
import random

EPS=Q(9,4)
LOW,HIGH=Q(0),Q(1)


def translate(numvars, clauses):
    assert all(not set(c).intersection(-x for x in c) for c in clauses)
    anchor=tuple([ (10*j,0),(10*j+2,1) ] for j in range(len(clauses)))
    streams=[]
    for x in range(1,numvars+1):
        stream=[]
        for j,clause in enumerate(clauses):
            h=10*j
            c=int(x in clause)
            stream.append([(h+c,0),(h+c+2,int(x in clause or -x in clause))])
        streams.append(stream)
    return anchor,streams


def breakpoints(anchor, streams):
    raw={LOW,HIGH}
    for stream in streams:
        for a,b in zip(anchor,stream,strict=True):
            for (s,_),(t,_) in product(a,b):
                raw.update(c for c in (t-s-EPS,t-s+EPS) if LOW<=c<=HIGH)
    v=sorted(raw)
    return sorted(v+[(a+b)/2 for a,b in zip(v,v[1:])])


def supports(anchor,stream,d):
    # Actual timestamps and flags, without consulting the formula or the intended offsets.
    result=set()
    all_small=tuple(permutations((0,1)))
    for pos,(a,b) in enumerate(zip(anchor,stream,strict=True)):
        good=[]
        for p in all_small:
            if all(abs(b[p[i]][0]-a[i][0]-d)<=EPS for i in (0,1)):
                good.append(b[p[0]][1])
        assert good, (a,b,d)
        if any(good):
            result.add(pos)
    return frozenset(result)


def raw_clock_score(numvars,clauses):
    anchor,streams=translate(numvars,clauses)
    allpts=breakpoints(anchor,streams)
    for stream in streams:
        # No eligible cross-block links, even after moving the offset anywhere in [0,1].
        for i,a in enumerate(anchor):
            for j,b in enumerate(stream):
                if i==j:
                    continue
                for (s,_),(t,_) in product(a,b):
                    assert max(LOW,Q(t-s)-EPS)>min(HIGH,Q(t-s)+EPS)
    families=[set(supports(anchor,s,d) for d in allpts) for s in streams]
    full=max(len(set().union(*ss)) for ss in product(*families))
    shared=max(len(set().union(*(supports(anchor,s,d) for s in streams))) for d in allpts)
    pooled=len(set().union(*(a for family in families for a in family)))
    return tuple(len(clauses)+z for z in (full,shared,pooled))


def truth_score(n,clauses):
    return max(sum(any(bool(b[abs(x)-1])==(x>0) for x in c) for c in clauses)
        for b in product((0,1),repeat=n))


def main():
    assert raw_clock_score(1,[(1,),(-1,)])==(3,3,4)
    assert raw_clock_score(2,[(1,),(-2,)])==(4,3,4)
    rng=random.Random(498)
    for test in range(300):
        n=rng.randrange(1,6)
        clauses=[]
        for j in range(rng.randrange(1,8)):
            variables=rng.sample(range(1,n+1),rng.randrange(1,min(n,3)+1))
            clauses.append(tuple(x if rng.randrange(2) else -x for x in variables))
        got=raw_clock_score(n,clauses)
        assert got[0]==len(clauses)+truth_score(n,clauses)
    # Separate single-stream control: feasible failure placements over private
    # offsets need not be bases of one matroid.
    a=(0,5,6,9)
    b=(1,5,16,17)
    placements={}
    for p in permutations(range(4)):
        d=[b[j]-a[i] for i,j in enumerate(p)]
        lo,hi=max(3,max(d)-7),min(7,min(d)+7)
        if lo<=hi:
            s=tuple(i for i,j in enumerate(p) if j in (0,2))
            placements.setdefault(s,set()).add((lo,hi))
    assert set(placements)=={(0,2),(0,3),(0,1),(1,2)}
    assert (1,3) not in placements and (2,3) not in placements
    print(json.dumps(dict(cnf_cases=300,one_clock_conflicting_literals=(3,3,4),
        private_clocks_allow_distinct_literals=(4,3,4),
        forbidden_basis_exchange_slots=[[0,3],[1,2]],placed_failure_sets=sorted(placements)),
        indent=2))


if __name__=='__main__':
    main()
