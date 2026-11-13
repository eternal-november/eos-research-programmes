#!/usr/bin/env python3
"""Exact finite checks, not a proof of the categorical or infinite-state theorems."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
import json
from pathlib import Path

def kernels(rows, cols, d):
    cs = [tuple(F(v,d) for v in c) for c in product(range(d+1),repeat=rows) if sum(c)<=d]
    for columns in product(cs,repeat=cols):
        yield tuple(tuple(columns[j][i] for j in range(cols)) for i in range(rows))

def qual(k):
    n=len(k[0]) if k else 0
    return (tuple(tuple(v>0 for v in row) for row in k),tuple(sum(row[j] for row in k)<1 for j in range(n)))

def mul(g,f):
    return tuple(tuple(sum(g[i][t]*f[t][j] for t in range(len(f))) for j in range(len(f[0]))) for i in range(len(g)))

def solve(m,b):
    n=len(m)
    a=[list(m[i])+[b[i]] for i in range(n)]
    for c in range(n):
        p=next((r for r in range(c,n) if a[r][c]),None)
        assert p is not None, 'Singular good-state matrix'
        a[c],a[p]=a[p],a[c]
        s=a[c][c];a[c]=[x/s for x in a[c]]
        for r in range(n):
            if r!=c:
                s=a[r][c];a[r]=[x-s*y for x,y in zip(a[r],a[c])]
    return [a[i][-1] for i in range(n)]

def reach(k, starts, a,b,u):
    seen=set(starts); todo=list(starts)
    while todo:
        j=todo.pop()
        for v in range(u):
            x=a+v
            if k[b+v][j] and x not in seen:
                seen.add(x);todo.append(x)
    return seen

def trace(k,a,b,u):
    # backward good-state closure; row b+v and column a+v name same U state
    good={v for v in range(u) if any(k[y][a+v] for y in range(b))}
    while True:
        new=good|{v for v in range(u) if any(k[b+w][a+v] for w in good)}
        if new==good:break
        good=new
    g=sorted(good)
    m=[[F(v==w)-k[b+v][a+w] for w in g] for v in g]
    output=[[k[y][x] for x in range(a)] for y in range(b)]
    for x in range(a):
        visits=solve(m,[k[b+v][x] for v in g])
        for y in range(b):output[y][x]+=sum(k[y][a+v]*visits[i] for i,v in enumerate(g))
    return tuple(map(tuple,output)),good

def graph_trace(k,a,b,u):
    rel,deficit=qual(k)
    cols=[];ds=[]
    for x in range(a):
        reached=reach(k,[x],a,b,u)
        cols.append(tuple(any(rel[y][j] for j in reached) for y in range(b)))
        badlocal=any(deficit[j] for j in reached)
        # Independently inspect reachable vertices' exit paths, rather than numerical good set.
        trap=False
        for j in reached-{x}:
            downstream=reach(k,[j],a,b,u)
            if not any(rel[y][z] for y in range(b) for z in downstream):trap=True
        ds.append(badlocal or trap)
    return (tuple(tuple(cols[x][y] for x in range(a)) for y in range(b)),tuple(ds))

def exhaustive(a,b,u,d):
    groups={};counts=Counter();weight_outputs={};total=0;singular_traps=0
    for k in kernels(b+u,a+u,d):
        t,good=trace(k,a,b,u);q=qual(t);expected=graph_trace(k,a,b,u)
        assert q==expected,(k,t,q,expected)
        assert all(0<=sum(row[x] for row in t)<=1 for x in range(a))
        key=qual(k)
        assert key not in groups or groups[key]==q
        groups[key]=q;counts[key]+=1;weight_outputs.setdefault(key,set()).add(t)
        total+=1;singular_traps+=len(good)<u
    return dict(A=a,B=b,U=u,denominator=d,kernels=total,qualitative_groups=len(groups),multiple_weight_groups=sum(v>1 for v in counts.values()),groups_with_distinct_numerical_traces=sum(len(v)>1 for v in weight_outputs.values()),kernels_with_nonexit_states=singular_traps,passed=True)

def composition():
    ks=list(kernels(2,2,3));n=0
    for f,g in product(ks,repeat=2):
        rf,df=qual(f);rg,dg=qual(g)
        r=tuple(tuple(any(rg[z][y] and rf[y][x] for y in range(2)) for x in range(2)) for z in range(2))
        d=tuple(df[x] or any(rf[y][x] and dg[y] for y in range(2)) for x in range(2))
        assert qual(mul(g,f))==(r,d);n+=1
    return dict(kernels=len(ks),ordered_pairs=n,passed=True)

def direct_sum():
    ks=list(kernels(1,1,3));n=0
    for f,g in product(ks,repeat=2):
        k=((f[0][0],F(0)),(F(0),g[0][0]))
        assert qual(k)==(((f[0][0]>0,False),(False,g[0][0]>0)),(f[0][0]<1,g[0][0]<1));n+=1
    return dict(pairs=n,passed=True)

def vanishing():
    n=0
    for k in kernels(3,3,3):
        direct=trace(k,1,1,2)[0]
        staged=trace(trace(k,2,2,1)[0],1,1,1)[0]
        assert direct==staged
        n+=1
    return dict(kernels=n,passed=True)

def examples():
    trap=((F(1,2),F(0)),(F(1,2),F(1)))
    leaky=((F(0),F(1,2)),(F(1),F(1,2)))
    assert trace(trap,1,1,1)[0]==((F(1,2),),)
    assert trace(leaky,1,1,1)[0]==((F(1),),)
    nsection=0
    for den in range(2,31):
        for num in range(1,den):
            r=F(num,den)
            assert r*r+1-r-r==(1-r)**2>0;nsection+=1
    # Geometric partial exits stay deficient though exact first-exit is normalized.
    for n in range(1,31):assert 1-F(1,2)**n<1
    # A finite check of rational recurrence and finite-barrier closed form only.
    walk=0
    for p in [F(1,3),F(1,2),F(2,3)]:
        q=1-p
        for N in range(2,21):
            m=[[F(i==j)-(p if j==i-1 else q if j==i+1 else 0) for j in range(1,N)] for i in range(1,N)]
            h=solve(m,[p if i==1 else F(0) for i in range(1,N)])
            for i in range(1,N):
                v=F(N-i,N) if p==q else ((p/q)**i-(p/q)**N)/(1-(p/q)**N)
                assert h[i-1]==v;walk+=1
    # Square-functor example: mixed pullback positive 4 -> 4 <- 2(diagonal)
    # and negative pushout 16 <- 4(identity at right leg's negative map) -> 4.
    # For the negative square H(beta)'s right map is diagonal^2:4 ->16;
    # beta's left negative map is id4. Thus pushout is canonically16.
    two=tuple(range(2));four=tuple(product(two,repeat=2));sixteen=tuple(product(four,repeat=2))
    pb=[(x,y) for x in four for y in two if x==(y,y)]
    assert len(pb)==2
    assert len(sixteen)==16
    return dict(trap_exit='1/2',leaky_exit='1',no_section_rational_checks=nsection,geometric_partial_sums=30,finite_barrier_recurrence_entries=walk,finite_barrier_systems=57,square_functor_apex=[2,4],square_functor_composite_apex=[len(pb),len(sixteen)],infinite_limit_status='Analytic proof required; finite recurrence checks do not prove infinite-state limit.',passed=True)

def main():
    results=dict(arithmetic='fractions.Fraction; no floating point',feedback='direct-sum first exit, not compact tensor trace',exhaustive=[exhaustive(1,1,u,3) for u in range(3)]+[exhaustive(1,1,3,2),exhaustive(2,2,1,3)],vanishing=vanishing(),composition=composition(),direct_sum=direct_sum(),examples=examples())
    results['total_feedback_kernels']=sum(x['kernels'] for x in results['exhaustive'])
    output=json.dumps(results,indent=2,sort_keys=True)+'\n'
    Path(__file__).with_name('verification_results.json').write_text(output)
    print(output,end='')
if __name__=='__main__':main()
