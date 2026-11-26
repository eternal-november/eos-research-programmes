#!/usr/bin/env python3
"""Exact frozen-left interface and singleton bit recovery."""
from fractions import Fraction as Q
from itertools import product
import json
import random


def debt(u,v,h):
    return max(Q(0),v-u)**2/(2*h)


def raw(left,v,h):
    return max(debt(u,v,h)-d for u,d in left)


def profile(left,V,h):
    return [( (V-u)/h, d-debt(u,V,h)) for u,d in left if u<V]


def eval_profile(lines,V,v,h):
    if v<=V:
        return Q(0)
    y=v-V
    return y*y/(2*h)+max([Q(0)]+[s*y-c for s,c in lines])


def replay():
    r=random.Random(516)
    scalar=joint=0
    for _ in range(480):
        h=Q(r.randrange(1,7))
        V=Q(r.randrange(17),8)
        q=Q(r.randrange(17),8)
        left=[(V,Q(0))]
        right=[(q,Q(0))]
        for j in range(r.randrange(2,12)):
            s=Q(r.randrange(17),8)
            t=Q(r.randrange(17),8)
            left.append((s,debt(s,V,h)+Q(r.randrange(4),64)))
            right.append((t,debt(q,t,h)+Q(r.randrange(4),64)))
        E=profile(left,V,h)
        for i in range(33):
            v=Q(i,16)
            assert eval_profile(E,V,v,h)==raw(left,v,h)
            scalar+=1
        expect=max(debt(u,v,h)-d-f for u,d in left for v,f in right)
        assert max(eval_profile(E,V,v,h)-f for v,f in right)==expect
        joint+=1
    total=queries=0
    for n in range(1,11):
        delta=Q(1,2*(n+1))
        eta=delta*delta/4
        ss=[i*delta for i in range(1,n+1)]
        outs=set()
        for bits in product((0,1),repeat=n):
            left=[(Q(1),Q(0))]+[(1-2*s,3*s*s/2+eta*b) for s,b in zip(ss,bits)]
            p=profile(left,Q(1),Q(2))
            ans=tuple(eval_profile(p,Q(1),1+s,Q(2)) for s in ss)
            for i,s in enumerate(ss):
                assert ans[i]==raw(left,1+s,Q(2))==3*s*s/4-eta*bits[i]
                # At this concrete threshold, b=1 accepts and b=0 refuses.
                assert (ans[i]<=3*s*s/4-eta/2)==bool(bits[i])
                queries+=1
            outs.add(ans)
            total+=1
        assert len(outs)==2**n
    return dict(scalar_queries=scalar, changed_right_profiles=joint,
                old_valid_stars=total, singleton_separation_queries=queries,
                max_independent_bits=10)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
