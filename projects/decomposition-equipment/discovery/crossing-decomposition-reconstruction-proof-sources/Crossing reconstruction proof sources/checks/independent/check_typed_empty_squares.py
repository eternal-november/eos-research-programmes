#!/usr/bin/env python3
from itertools import product,permutations
from pathlib import Path
from collections import Counter
import json
count=Counter()

def expected(theta,L,R,V,W,dom,cod):
    # L,R entries carry b,c respectively; V entries c; W entries b.
    nv=len(V);adj=[set() for _ in range(nv+len(W))];vl=[set() for _ in V];wr=[set() for _ in W]
    for (v,r),idx in zip(dom,theta):
        l,w=cod[idx];adj[v].add(nv+w);adj[nv+w].add(v);vl[v].add(l);wr[w].add(r)
    unseen={i for i,a in enumerate(adj) if a}
    while unseen:
        seed=next(iter(unseen));cc={seed};stack=[seed]
        while stack:
            for j in adj[stack.pop()]:
                if j not in cc:cc.add(j);stack.append(j)
        unseen-=cc;vs=[x for x in cc if x<nv];ws=[x-nv for x in cc if x>=nv]
        bs={W[w] for w in ws};cs={V[v] for v in vs}
        if len(bs)!=1 or len(cs)!=1:return False
        b=next(iter(bs));c=next(iter(cs));ls={l for l,bb in enumerate(L) if bb==b};rs={r for r,cc in enumerate(R) if cc==c}
        if any(len(vl[v])!=1 for v in vs) or any(len(wr[w])!=1 for w in ws):return False
        if len(vs)!=len(ls) or len(ws)!=len(rs):return False
        if {next(iter(vl[v])) for v in vs}!=ls or {next(iter(wr[w])) for w in ws}!=rs:return False
        if not all(nv+w in adj[v] for v in vs for w in ws):return False
    # Because L_b,R_c cardinalities are 0 or1, nonempty one-sided tiling possible iff some supported opposite endpoint exists.
    for c in range(2):
        if c not in R and c in V and not L:return False
    for b in range(2):
        if b not in L and b in W and not R:return False
    return True

def realized(L,R,V,W,dom,cod):
    ans=set();codindex={x:i for i,x in enumerate(cod)}
    for ns in product(range(3),repeat=4):
        # Normalize doubly invisible fibres to empty; sufficient for existence.
        if any(ns[2*b+c] and b not in L and c not in R for b in range(2) for c in range(2)):continue
        U=[(b,c,k) for b in range(2) for c in range(2) for k in range(ns[2*b+c])]
        adom=[[(l,u) for l,b in enumerate(L) for u,(ub,uc,k) in enumerate(U) if b==ub and uc==c] for c in range(2)]
        bdom=[[(u,r) for u,(ub,uc,k) in enumerate(U) for r,c in enumerate(R) if ub==b and uc==c] for b in range(2)]
        vats=[[v for v,c0 in enumerate(V) if c0==c] for c in range(2)]
        wats=[[w for w,b0 in enumerate(W) if b0==b] for b in range(2)]
        if any(len(adom[i])!=len(vats[i]) or len(bdom[i])!=len(wats[i]) for i in range(2)):continue
        for vp0,vp1,wp0,wp1 in product(permutations(vats[0]),permutations(vats[1]),permutations(wats[0]),permutations(wats[1])):
            ai={v:lu for c,vp in enumerate((vp0,vp1)) for lu,v in zip(adom[c],vp)}
            beta={ur:w for b,wp in enumerate((wp0,wp1)) for ur,w in zip(bdom[b],wp)}
            theta=[]
            for v,r in dom:
                l,u=ai[v];w=beta[u,r];theta.append(codindex[l,w])
            ans.add(tuple(theta));count['actual_filler_presentations']+=1
    return ans

for lc,rc,vc,wc in product(product(range(2),repeat=2),product(range(2),repeat=2),product(range(3),repeat=2),product(range(3),repeat=2)):
    L=[b for b in range(2) for _ in range(lc[b])];R=[c for c in range(2) for _ in range(rc[c])]
    V=[c for c in range(2) for _ in range(vc[c])];W=[b for b in range(2) for _ in range(wc[b])]
    dom=[(v,r) for v,c in enumerate(V) for r,cc in enumerate(R) if c==cc]
    cod=[(l,w) for l,b in enumerate(L) for w,bb in enumerate(W) if b==bb]
    if len(dom)!=len(cod):continue
    fills=realized(L,R,V,W,dom,cod)
    for theta in permutations(range(len(cod))):
        assert expected(theta,L,R,V,W,dom,cod)==(theta in fills),(lc,rc,vc,wc,theta)
        count['typed_theta_cases']+=1
        if theta in fills:count['typed_liftable_theta_cases']+=1
        if 0 in lc or 0 in rc:count['theta_cases_with_empty_fibres']+=1
    count['typed_boundary_profiles']+=1
out={'status':'PASS','scope':'A,D singleton;B,C two named points;each L_b,R_c size0or1;each V_c,W_b size0,1,2;every actual endpoint-compatible theta bijection when whole counts agree. Rectangle+one-sided existence classification compared against direct U cardinalities0..2 and all alpha/beta presentations; doubly invisible fibres normalized empty only for existence. Does not enumerate unbounded invisible automorphism groups.','counts':dict(count)}
Path(__file__).with_name('Typed_Empty_Square_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
