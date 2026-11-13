#!/usr/bin/env python3
"""Independently enumerate witness matchings and actual fillers on singleton endpoints."""
from itertools import permutations
from math import factorial
from pathlib import Path
import json

def generated_theta(l,r,u,alpha,beta):
    # alpha is actual map (L,U)->V; beta actual map (U,R)->W.
    inverse={v:divmod(i,u) for i,v in enumerate(alpha)} if u else {}
    out=[]
    for v in range(l*u):
        for rr in range(r):
            ll,uu=inverse[v]
            out.append(ll*(u*r)+beta[uu*r+rr])
    return tuple(out)

def classify(theta,l,r,u):
    nv=l*u;nw=u*r
    adj=[set() for _ in range(nv+nw)]
    vlabels=[set() for _ in range(nv)]
    wlabels=[set() for _ in range(nw)]
    edges=[]
    for idx,encoded in enumerate(theta):
        v,rr=divmod(idx,r);ll,w=divmod(encoded,nw)
        adj[v].add(nv+w);adj[nv+w].add(v)
        vlabels[v].add(ll);wlabels[w].add(rr)
        edges.append((v,w,ll,rr))
    local=all(len(x)==1 for x in vlabels+wlabels)
    if not local:return False,False,[]
    components=[];unused=set(range(nv+nw))
    while unused:
        seed=next(iter(unused));seen={seed};todo=[seed]
        while todo:
            for w in adj[todo.pop()]:
                if w not in seen:seen.add(w);todo.append(w)
        unused-=seen;components.append(seen)
    rectangle=True
    for cc in components:
        vs=[v for v in cc if v<nv];ws=[w-nv for w in cc if w>=nv]
        rectangle &= len(vs)==l and len(ws)==r
        rectangle &= {next(iter(vlabels[v])) for v in vs}==set(range(l))
        rectangle &= {next(iter(wlabels[w])) for w in ws}==set(range(r))
        rectangle &= all(nv+w in adj[v] for v in vs for w in ws)
    return local,bool(rectangle),[len(c) for c in components]

results=[]
for l,r,u in ((2,2,1),(2,2,2),(1,2,2),(2,1,2)):
    fills={generated_theta(l,r,u,a,b) for a in permutations(range(l*u)) for b in permutations(range(u*r))}
    counts={'total':0,'local_coverings':0,'rectangles':0,'locally_valid_nontrivial_coverings':0}
    for theta in permutations(range(l*u*r)):
        local,rectangle,components=classify(theta,l,r,u)
        assert rectangle==(theta in fills)
        counts['total']+=1;counts['local_coverings']+=local;counts['rectangles']+=rectangle
        counts['locally_valid_nontrivial_coverings']+=local and not rectangle
    assert counts['rectangles']==factorial(l*u)*factorial(u*r)//factorial(u)
    results.append({'l':l,'r':r,'u':u,**counts})
# Locally valid 2-sheet cover twisted on one base-square edge.
l=r=u=2
# V numbered (l,u), W numbered (u,r).
twist=tuple(ll*4+((uu^(ll*rr))*2+rr) for ll in range(2) for uu in range(2) for rr in range(2))
assert sorted(twist)==list(range(8))
local,rectangle,components=classify(twist,2,2,2)
assert local and not rectangle and components==[8]
# Lift l0-r0-l1-r1-l0 starting at sheet u=0: three edge matches trivial, final edge toggles.
def theta_map(ll,uu,rr):return uu^(ll*rr)
sheet=0
w0=theta_map(0,sheet,0)
sheet_at_l1=w0 # edge (1,0) is untwisted
w1=theta_map(1,sheet_at_l1,1)
returned=w1 # inverse edge (0,1) untwisted
assert returned==1
out={'status':'PASS','enumerations':results,'twist':{'permutation':twist,'connected_component_sizes':components,'local_covering':local,'filler':rectangle,'fundamental_cycle_sheet_0_image':returned},'scope':'Singleton endpoints; all actual theta bijections in listed sizes, independently compared against all alpha/beta fillers. Explicit locally valid twisted cover. Does not enumerate arbitrary endpoint typing or empty sectors.'}
Path(__file__).with_name('Witnessed_Square_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
