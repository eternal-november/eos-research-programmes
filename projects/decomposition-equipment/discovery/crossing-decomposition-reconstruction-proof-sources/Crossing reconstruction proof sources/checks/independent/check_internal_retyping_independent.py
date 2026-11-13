#!/usr/bin/env python3
from itertools import product,permutations
from collections import Counter
from pathlib import Path
import json
counts=Counter()

def rectangle(theta,nv,nw,dom,cod,L,R,V,W):
    adj=[set() for _ in range(nv+nw)];vl=[set() for _ in V];wr=[set() for _ in W]
    for (v,r),ix in zip(dom,theta):
        l,w=cod[ix];adj[v].add(nv+w);adj[nv+w].add(v);vl[v].add(l);wr[w].add(r)
    unseen=set(range(nv+nw))
    while unseen:
        seen={next(iter(unseen))};todo=list(seen)
        while todo:
            for v in adj[todo.pop()]:
                if v not in seen:seen.add(v);todo.append(v)
        unseen-=seen;vs=[v for v in seen if v<nv];ws=[w-nv for w in seen if w>=nv]
        if not vs or not ws:return False
        bs={W[w] for w in ws};cs={V[v] for v in vs}
        if len(bs)!=1 or len(cs)!=1:return False
        b=next(iter(bs));c=next(iter(cs));ls={l for l,bb in enumerate(L) if bb==b};rs={r for r,cc in enumerate(R) if cc==c}
        if any(len(vl[v])!=1 for v in vs) or any(len(wr[w])!=1 for w in ws):return False
        if len(vs)!=len(ls) or len(ws)!=len(rs):return False
        if {next(iter(vl[v])) for v in vs}!=ls or {next(iter(wr[w])) for w in ws}!=rs:return False
        if not all(nv+w in adj[v] for v in vs for w in ws):return False
    return True

for l,r,u,n in ((2,2,1,2),(2,2,1,3),(2,2,2,2)):
    perms=list(permutations(range(n)));indices=list(product(range(l),range(u),range(r)))
    # Original L,R endpoints singleton. New L witnesses=(l,b),R=(c,r),V=(l,u,c),W=(b,u,r).
    Ldata=list(product(range(l),range(n)));Rdata=list(product(range(n),range(r)))
    Vdata=list(product(range(l),range(u),range(n)));Wdata=list(product(range(n),range(u),range(r)))
    L=[b for ll,b in Ldata];R=[c for c,rr in Rdata];V=[c for ll,uu,c in Vdata];W=[b for b,uu,rr in Wdata]
    dom=[(vi,ri) for vi,c in enumerate(V) for ri,cc in enumerate(R) if c==cc]
    cod=[(li,wi) for li,b in enumerate(L) for wi,bb in enumerate(W) if b==bb];ci={p:i for i,p in enumerate(cod)}
    li={v:i for i,v in enumerate(Ldata)};wi={v:i for i,v in enumerate(Wdata)}
    for choices in product(perms,repeat=len(indices)):
        lam=dict(zip(indices,choices));theta=[]
        for vi,ri in dom:
            ll,uu,c=Vdata[vi];_,rr=Rdata[ri];b=lam[ll,uu,rr][c]
            theta.append(ci[li[ll,b],wi[b,uu,rr]])
        assert sorted(theta)==list(range(len(cod)))
        fill=rectangle(theta,len(V),len(W),dom,cod,L,R,V,W)
        constant=all(lam[ll,uu,rr]==lam[0,uu,0] for ll,uu,rr in indices)
        assert fill==constant
        counts[f'lambda_cases_l{l}_r{r}_u{u}_n{n}']+=1
        counts[f'fillable_l{l}_r{r}_u{u}_n{n}']+=fill
# Compose first 2-sheet bijections and all second maps on two-point endpoints.
for lam in permutations(range(2)):
    for f,g in product(product(range(2),repeat=2),repeat=2):
        possibilities=[]
        for c in range(2):
            cs=[x for x in range(2) if g[x]==c];bs=[x for x in range(2) if f[x]==lam[c]]
            if len(cs)!=len(bs):break
            possibilities.append([dict(zip(cs,p)) for p in permutations(bs)])
        else:
            for mus in product(*possibilities):
                composite=tuple(mus[g[c]][c] for c in range(2))
                assert sorted(composite)==[0,1]
                # Two-stage hidden witnesses and endpoint maps equal direct after dropping middle c.
                two={(0,g[c],c,mus[g[c]][c]) for c in range(2)}
                one={(0,c,composite[c]) for c in range(2)}
                assert {(u,c,b) for u,mid,c,b in two}==one
                counts['valid_two_stage_retyping_cases']+=1
out={'status':'PASS','scope':'Original singleton endpoint fully visible rectangles; all perwholepath fibre permutations for listed l,r,u and equal retyping fibre n. Criterion compared to independently constructed typed incidence rectangle classification. All two-stage second endpoint maps on two-element interfaces with all compatible fibre bijections. Empty second-stage fibres included.','counts':dict(counts)}
Path(__file__).with_name('Internal_Retyping_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
