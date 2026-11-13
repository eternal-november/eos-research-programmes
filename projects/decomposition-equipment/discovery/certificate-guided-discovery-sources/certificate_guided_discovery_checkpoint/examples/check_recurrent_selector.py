#!/usr/bin/env python3
"""Finite regression of persistent symbolic certificates, not the general proof."""
from itertools import product, combinations
import json

def whole(s,y,v):
    n=len(v)
    return ((s+1+y)%n, v[s], tuple(v[j]^(y & v[(j+1)%n]) for j in range(n)))

def local(s,y,v,S):
    n=len(v); T=set(range(n))-set(S)
    # Actual labeled messages; the receiver knows its incident coordinate map.
    incoming_p={j:v[j] for j in T}
    incoming_q=(y,{j:v[j] for j in S})
    pstate={j:v[j] for j in S}; qstate={j:v[j] for j in T}
    pv={**pstate,**incoming_p}; qv={**qstate,**incoming_q[1]}
    pout={j:pv[j]^(y & pv[(j+1)%n]) for j in S}
    qout={j:qv[j]^(incoming_q[0] & qv[(j+1)%n]) for j in T}
    nxt={**pout,**qout}
    return ((s+1+y)%n, pv[s], tuple(nxt[j] for j in range(n)))

checks=0; separation=0; budgets=[]; traces=0
for r in (2,3):
    n=2*r; vectors=list(product((0,1),repeat=n))
    for S in combinations(range(n),r):
        assert len(S)<=r+1 and 1+n-len(S)<=r+1
        for v in vectors:
            for s in range(n):
                for y in (0,1):
                    assert local(s,y,v,S)==whole(s,y,v)
                    checks+=1
        # Several repeated steps use exactly the same implementation witness.
        for start in [(0,0,vectors[-1]),(n-1,1,vectors[len(vectors)//3])]:
            a=b=start
            for _ in range(20):
                a=whole(*a); b=local(*b,S)
                assert a==b
                traces+=1
    # Every distinct peripheral state is separated by one central state.
    for a,b in combinations(vectors,2):
        j=next(j for j in range(n) if a[j]!=b[j])
        assert whole(j,0,a)[1]!=whole(j,0,b)[1]
        separation+=1
    budgets.append({'r':r,'parent_incoming_bits':r+1,
                    'central_refinement_minimum_bits':2*r,
                    'parent_cut_candidates':len(list(combinations(range(n),r))),
                    'whole_state_count':n*2**(n+1)})
print(json.dumps({'status':'PASS','one_step_certificate_checks':checks,
                  'iterated_step_checks':traces,'separating_pairs':separation,
                  'budgets':budgets},indent=2))
