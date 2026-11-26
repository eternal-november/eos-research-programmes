from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod
import json

def char(a,x): return (-1)**((a&x).bit_count())

def p_law(n,menu,signs):
    d=len(menu)
    return {x:F(2*d+sum(s*char(t,x) for t,s in zip(menu,signs)),2*d*(1<<n))
            for x in range(1<<n)}

def marg(p,b):
    q=Counter()
    for x,w in p.items():q[x&b]+=w
    return dict(q)

def partitions(n):
    def rec(i,parts):
        if i==n:
            yield parts;return
        q=1<<i
        for j,p in enumerate(parts):
            yield from rec(i+1,parts[:j]+(p|q,)+parts[j+1:])
        yield from rec(i+1,parts+(q,))
    yield from rec(0,())

def assembled(p,parts,cache):
    for b in parts:
        if b not in cache:cache[b]=marg(p,b)
    return {x:prod(cache[b][x&b] for b in parts) for x in p}

def projection_checks():
    n=6
    menu=tuple(t for t in range(1<<n) if t&1 and t.bit_count()==3)
    d=len(menu)
    all_partitions=tuple(partitions(n))
    profiles=[(1,)*d,(-1,)*d,tuple((-1)**i for i in range(d)),
              *[tuple(-1 if i==j else 1 for i in range(d)) for j in range(d)]]
    rows=0
    for ss in profiles:
        p=p_law(n,menu,ss)
        cache={}
        weighted=Counter()
        support_counts=Counter()
        total=0
        for h,P in enumerate(all_partitions):
            got=assembled(p,P,cache)
            eligible=[(s,sgn) for s,sgn in zip(menu,ss) if any(s&b==s for b in P)]
            source={x:F(2*d+sum(sgn*char(s,x) for s,sgn in eligible),2*d*(1<<n))
                    for x in p}
            assert got==source and sum(got.values())==1
            for x in got:rows+=1
            wt=1+(h%7)
            total+=wt
            for s,_ in eligible:support_counts[s]+=wt
            for x,v in got.items():weighted[x]+=wt*v
        for s,sgn in zip(menu,ss):
            alpha=F(support_counts[s],total)
            read=sum(v*char(s,x) for x,v in weighted.items())/total
            assert read==alpha*F(sgn,2*d)
    return n,menu,all_partitions,rows

def report_checks():
    n,menu,all_parts,rows=projection_checks()
    d=len(menu)
    rho=F(1,2) # retention, not a dormant-risk probability in this study
    p=p_law(n,menu,(1,)*d)
    base_u=F(1,len(p))
    hl=[]
    tagged=[]
    for j in range(d):
        q=p_law(n,menu,tuple(-1 if i==j else 1 for i in range(d)))
        r0={x:rho*z+(1-rho)*base_u for x,z in p.items()}
        r1={x:rho*z+(1-rho)*base_u for x,z in q.items()}
        hl.append(sum((r1[x]-r0[x])**2/r0[x] for x in p))
        tagged.append(rho*sum((q[x]-p[x])**2/p[x] for x in p))
    assert max(hl)<=2*rho*rho/d**2 and max(tagged)<=2*rho/d**2
    # Same known outcome-dependent filter, same tags and rows,
    # yet the true first two decision bits under the cap are reversed.
    p0=p_law(n,menu,(1,-1)+((1,)*(d-2)))
    p1=p_law(n,menu,(-1,1)+((1,)*(d-2)))
    keep_set=[x for x in p0 if char(menu[0]^menu[1],x)==1]
    keep0={x:p0[x] for x in keep_set}
    keep1={x:p1[x] for x in keep_set}
    assert keep0==keep1 and sum(keep0.values())==rho
    residual=lambda p:{x:(p[x]-keep0.get(x,0))/(1-rho) for x in p}
    blocks=tuple(1<<i for i in range(n))
    rejected0=assembled(residual(p0),blocks,{})
    rejected1=assembled(residual(p1),blocks,{})
    assert rejected0==rejected1
    assert all(sum(p0[x]*char(a,x) for x in p0)==-sum(p1[x]*char(a,x) for x in p1)
               != 0 for a in menu[:2])
    d4=(3,12)
    v=p_law(4,d4,(1,1))
    r=assembled(v,d4,{})
    cross=sum(z*char(15,x) for x,z in r.items())
    assert cross==F(1,16) and sum(z*char(15,x) for x,z in v.items())==0
    return dict(sites=n,queries=d,partition_count=len(all_parts),
                exact_assembled_cells=rows,star_comparisons=d,
                hidden_chisq_observed=str(max(hl)),tagged_chisq_observed=str(max(tagged)),
                same_known_outcome_dependent_filter=True,
                outcome_dependent_retention=str(rho),all_tags_and_rows_alias=True,
                disjoint_cross_character=str(cross))

if __name__=="__main__":
    print(json.dumps(report_checks(),indent=2,sort_keys=True))
