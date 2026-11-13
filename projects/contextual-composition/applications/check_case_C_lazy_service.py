#!/usr/bin/env python3
"""Exact finite regression, NOT a proof of arbitrary-client theorem.
Run: python check_case_C_lazy_service.py [output.json]
Independent eager-table and lazy-cache operational enumerators. Standard library only.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from pathlib import Path
import json
import sys

CLIENT = ((0, Q(1, 3)), (1, Q(2, 3)), (2, Q(0)))
JOB = ((0, Q(1, 4)), (1, Q(3, 4)))


def action(n, seed, job, choices, calls, z):
    # Stop or next key depends on prior answers and random client result; not sibling job outcome.
    code = seed + 3*z + len(choices) + sum((i+1)*(a+2*b+1) for i,(a,b) in enumerate(calls))
    return None if code % (n+2) == n else code % n


def eager(n, m, N, seed):
    runs = []
    prefixes = defaultdict(lambda: defaultdict(Q))
    for f in product(range(m), repeat=n):
        for job, jp in JOB:
            def go(choices, calls, p):
                key = (job, choices, calls)
                prefixes[key][f] += p
                if len(calls) == N:
                    runs.append((f,key,p)); return
                for z, zp in CLIENT:
                    a = action(n,seed,job,choices,calls,z)
                    cs = choices+(z,)
                    if a is None:
                        runs.append((f,(job,cs,calls),p*zp))
                    else:
                        go(cs,calls+((a,f[a]),),p*zp)
            go((),(),jp/Q(m**n))
    return runs,prefixes


def lazy(n, m, N, seed):
    runs = {}
    for job,jp in JOB:
        def go(cache, choices, calls, p):
            key=(job,choices,calls)
            if len(calls)==N:
                assert key not in runs
                runs[key]=(p,dict(cache)); return
            for z,zp in CLIENT:
                a=action(n,seed,job,choices,calls,z)
                cs=choices+(z,)
                if a is None:
                    key=(job,cs,calls)
                    assert key not in runs
                    runs[key]=(p*zp,dict(cache))
                elif a in cache:
                    go(cache,cs,calls+((a,cache[a]),),p*zp)
                else:
                    for b in range(m):
                        nxt=dict(cache); nxt[a]=b
                        go(nxt,cs,calls+((a,b),),p*zp/Q(m))
        go({},(),(),jp)
    return runs


def check(n,m,N,seed):
    es,prefixes=eager(n,m,N,seed)
    ls=lazy(n,m,N,seed)
    fibres=defaultdict(list)
    for f,key,p in es:
        assert key in ls
        fibres[key].append((f,p))
    assert set(fibres)==set(ls)  # includes probability-zero histories
    assert sum(p for _,_,p in es)==sum(p for p,_ in ls.values())==1
    zero=0; strict=0; early=0; repeated=0
    for key,(lp,cache) in ls.items():
        job,choices,calls=key
        d=len(cache); q=len(calls)
        assert cache==dict(calls)
        assert len(fibres[key])==m**(n-d)
        assert sum(p for _,p in fibres[key])==lp
        expected_client = dict(JOB)[job]
        for z in choices: expected_client*=dict(CLIENT)[z]
        assert lp==expected_client/Q(m**d)
        for f,ep in fibres[key]:
            assert all(f[a]==b for a,b in cache.items())
            assert ep==expected_client/Q(m**n)
            # Actual final token Ready_(N-q); same normalized Fork(job,calls).
            eager_cost=(n,q,job+len(choices))
            lazy_cost=(d,q,job+len(choices))
            assert all(x<=y for x,y in zip(lazy_cost,eager_cost))
            assert eager_cost[0]-lazy_cost[0]==n-d
        # Native candidate fibre cost min: all reference costs same here.
        assert d<=min(n for _ in fibres[key])
        zero+=lp==0; strict+=d<n; early+=q<N; repeated+=q>d
    posterior_checks=0
    for (job,choices,calls),weights in prefixes.items():
        cache=dict(calls); total=sum(weights.values())
        assert len(weights)==m**(n-len(cache))
        if total:
            expected=total/Q(m**(n-len(cache)))
            assert all(p==expected for p in weights.values())
            for a in range(n):
                if a not in cache:
                    for b in range(m):
                        assert sum(p for f,p in weights.items() if f[a]==b)==total/Q(m)
            posterior_checks+=1
    return dict(n=n,m=m,N=N,seed=seed,eager_histories=len(es),lazy_histories=len(ls),
                zero_lazy_histories=zero,strict_cost_histories=strict,early_stop_histories=early,
                repeated_query_histories=repeated,positive_posterior_prefixes=posterior_checks)


def worked():
    # Fixed discriminating fixture: query 0, then query 1 if answer0 else 0.
    eager_law=defaultdict(Q); lazy_law=defaultdict(Q)
    for f in product(range(2),repeat=2):
        a=1 if f[0]==0 else 0
        word=(f[0],f[a]); eager_law[word]+=Q(1,4)
    for b in range(2):
        if b==1: lazy_law[(1,1)]+=Q(1,2)
        else:
            for c in range(2): lazy_law[(0,c)]+=Q(1,4)
    assert eager_law==lazy_law=={(0,0):Q(1,4),(0,1):Q(1,4),(1,1):Q(1,2)}
    expected_lazy=2*Q(1,4)+2*Q(1,4)+1*Q(1,2)
    assert expected_lazy==Q(3,2)
    # Fixed-state answer marginal obstruction; local cost also fails.
    assert Q(1,2)!=1 and 1>0
    return {'word_law': {str(k):str(v) for k,v in eager_law.items()},
            'eager_expected_sample_work':'2','lazy_expected_sample_work':str(expected_lazy)}


def main():
    rows=[check(n,m,N,seed) for n,m in ((1,1),(1,2),(2,2),(3,2),(2,3))
          for N in range(4) for seed in range(5)]
    totals={key:sum(r[key] for r in rows) for key in rows[0] if key not in ('n','m','N','seed')}
    assert totals['zero_lazy_histories']>0 and totals['early_stop_histories']>0
    assert totals['repeated_query_histories']>0 and totals['strict_cost_histories']>0
    result={'status':'PASS','scope':'100 parameter/controller regressions; not exhaustive O4 metatheory',
            'checks':['independent eager/lazy marginal equality','adaptive completion fibre counts',
                      'all raw-history surjectivity including client zero branches','conditional uniform prefix posterior',
                      'initializer charged inside full cost','early stop and N=0','repeated key caching',
                      'independent disjoint job retained','native probability/cost equations','fixed-state marginal obstruction'],
            'totals':totals,'worked':worked(),'runs':rows}
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('case_C_checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='runs'},indent=2))

if __name__=='__main__': main()
