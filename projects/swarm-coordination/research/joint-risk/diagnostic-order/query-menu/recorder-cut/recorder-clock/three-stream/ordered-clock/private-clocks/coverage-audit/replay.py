#!/usr/bin/env python3
"""Exact weighted source oracle and finite-test LP certificates."""
from fractions import Fraction as Q
from itertools import permutations,product
from pathlib import Path
import importlib.util
import json
import random
import sys

from scipy.optimize import linprog


def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def weighted_slot_set(slots,weights):
    """Add episodes in weight order, augmenting their matches to failure slots."""
    phases=sorted(weights,key=lambda p:(-weights[p],p))
    by_phase={p:[i for i,ins in enumerate(slots) if p in ins] for p in phases}
    who={}
    def add(p,seen):
        for i in by_phase[p]:
            if i in seen:
                continue
            seen.add(i)
            if i not in who or add(who[i],seen):
                who[i]=p
                return True
        return False
    for p in phases:
        add(p,set())
    return frozenset(who.values())


def support(anchor,group,eps,lo,hi,beta,ordered):
    found=None
    for d in ordered.common_cells(anchor,group,eps,lo,hi):
        loc=[ordered.virtual_slots(anchor,s,d,eps) for s in group]
        if any(x is None or ordered.cardinality(x[0])!=len(x[0]) for x in loc):
            continue
        slots=[row for x in loc for row in x[0]]
        proof=weighted_slot_set(slots,beta)
        val=sum(beta[p] for p in proof)
        if found is None or val>found[0]:
            found=(val,d,proof)
    return found


def exact_plans(anchor,group,eps,lo,hi,unfailed):
    # Permutations are independent within a shared-offset group; intersect the
    # complete offset constraints before taking a union of the outcome sets.
    candidates=[]
    n=len(anchor)
    for stream in group:
        rows=[]
        for perm in permutations(range(n)):
            dd=[stream[j][0]-anchor[i] for i,j in enumerate(perm)]
            p,q=max(lo,max(dd)-eps),min(hi,min(dd)+eps)
            if p<=q:
                rows.append((p,q,{i+1 for i,k in enumerate(perm) if stream[k][1]}))
        candidates.append(rows)
    sets=set()
    for chosen in product(*candidates):
        if max(x[0] for x in chosen)<=min(x[1] for x in chosen):
            sets.add(frozenset(unfailed.intersection(set().union(*(x[2] for x in chosen)))))
    return sorted(sets,key=lambda s:(len(s),sorted(s)))


def sat_to_sources(n,clauses,private):
    a,ss=private.translate(n,clauses)
    anchor=[Q(t) for block in a for t,_ in block]
    groups=[[[ (Q(t),f) for block in s for t,f in block ]] for s in ss]
    return anchor,groups,{p for p in range(1,len(anchor)+1,2)}


def cover_lp(families,unfailed):
    ids=[(i,a) for i,g in enumerate(families) for a in g]
    m=len(ids)
    phases=sorted(unfailed)
    N=m+len(phases)
    eq=[]
    for i in range(len(families)):
        eq.append([int(j==i) for j,_ in ids]+[0]*len(phases))
    coeff=[]
    for j,p in enumerate(phases):
        coeff.append([-int(p in a) for _,a in ids]+[int(i==j) for i in range(len(phases))])
    raw=linprog([0]*m+[-1]*len(phases),A_ub=coeff,b_ub=[0]*len(phases),
                A_eq=eq,b_eq=[1]*len(eq),bounds=[(0,None)]*m+[(0,1)]*len(phases),
                method='highs')
    assert raw.success
    rat=lambda x: Q(float(x)).limit_denominator(10000)
    x=[rat(x) for x in raw.x]
    beta={p:min(Q(1),-rat(q)) for p,q in zip(phases,raw.ineqlin.marginals,strict=True)}
    assert all(Q(0)<=v<=Q(1) for v in beta.values())
    assert all(xi>=0 for xi in x) and all(sum(f*y for f,y in zip(row,x,strict=True))==1 for row in eq)
    assert all(xi<=1 for xi in x[m:])
    assert all(sum(f*y for f,y in zip(row,x,strict=True))<=0 for row in coeff)
    primal=sum(x[m:])
    dual=sum(1-v for v in beta.values())+sum(max(sum(beta[p] for p in a) for a in g) for g in families)
    assert primal==dual
    dist=[[] for _ in families]
    for z,(i,a) in zip(x[:m],ids,strict=True):
        if z>0:
            dist[i].append((z,a))
    return primal,beta,dist


def round_by_expectation(distributions,unfailed):
    def expectation(fixed,future):
        return sum((Q(1) if p in fixed else Q(1)-miss(p,future)) for p in unfailed)
    def miss(p,samples):
        q=Q(1)
        for g in samples:
            q*=sum(z for z,a in g if p not in a)
        return q
    fixed=set()
    expect=expectation(set(),distributions)
    for i,g in enumerate(distributions):
        fixed|=max((a for _,a in g),key=lambda a:expectation(fixed|a,distributions[i+1:]))
    assert len(fixed)>=expect
    return expect,len(fixed)


def validate_named(ordered,private):
    fixtures=[(1,[(1,),(-1,)],(1,1)), (2,[(1,),(-2,)],(2,2)),
              (2,[(1,2),(1,-2),(-1,2),(-1,-2)],(3,4))]
    output=[]
    for n,cl,expected in fixtures:
        anchor,groups,P=sat_to_sources(n,cl,private)
        fam=[exact_plans(anchor,g,Q(9,4),Q(0),Q(1),P) for g in groups]
        optimum=max(len(set().union(*ss)) for ss in product(*fam))
        value,beta,dist=cover_lp(fam,P)
        bound=sum(1-w for w in beta.values())
        for g in groups:
            w,_,_=support(anchor,g,Q(9,4),Q(0),Q(1),beta,ordered)
            bound+=w
        assert bound==value
        assert (optimum,bound)==expected
        e,L=round_by_expectation(dist,P)
        assert L<=optimum<=value
        output.append(dict(clause_instances=len(cl),optimum=optimum,certified_upper=str(value),
            rounded_lower=L,rounding_expectation=str(e),anchor_known_failures=len(cl),
            pooled_upper=len(P),certificate={p:str(q) for p,q in beta.items()}))
    return output


def main(directory):
    directory=Path(directory).resolve()
    ordered=module(Path(directory).parent/"replay.py","ordered_profile")
    private=module(Path(directory)/"replay.py","private_clock")
    rng=random.Random(499)
    for i in range(420):
        n=rng.randrange(1,5)
        anchor=sorted(Q(rng.randrange(-3,11),2) for _ in range(n))
        group=[[(Q(rng.randrange(-3,11),2),rng.randrange(2)) for _ in anchor]
               for _ in range(rng.randrange(1,4))]
        eps=Q(rng.randrange(9),2)
        beta={p:Q(rng.randrange(8),7) for p in range(1,n+1) if rng.randrange(5)!=0}
        exact=exact_plans(anchor,group,eps,Q(-1),Q(1),set(beta))
        want=max((sum(beta[p] for p in S) for S in exact),default=None)
        got=support(anchor,group,eps,Q(-1),Q(1),beta,ordered)
        assert (got[0] if got is not None else None)==want
    print(json.dumps(dict(weighted_clock_group_checks=420,
        exact_matching_lp_certificates=validate_named(ordered,private)),indent=2))


if __name__=='__main__':
    main(sys.argv[1])
