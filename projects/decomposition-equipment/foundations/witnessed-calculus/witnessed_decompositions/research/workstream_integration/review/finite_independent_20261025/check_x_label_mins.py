#!/usr/bin/env python3
from pathlib import Path
from dataclasses import replace
import json,hashlib,time
import check_noimport as I
P=Path(__file__).parent

def relocate(t,mapping):
    return replace(t,vertices=tuple(mapping[v] for v in t.vertices),edges=tuple((mapping[x],mapping[y]) for x,y in t.edges),children=tuple(relocate(c,mapping) for c in t.children))
def localize(t):return relocate(t,{v:i for i,v in enumerate(t.vertices)})
def abstract(q,rule):
    if rule=='R':addresses=((0,0),(0,1),(1,))
    elif rule=='UL':addresses=((1,),)
    elif rule=='UR':addresses=((0,),)
    elif rule=='D0':addresses=((0,),)
    elif rule=='DA':addresses=((0,0),)
    elif rule=='DL':addresses=((0,0),(1,))
    elif rule=='DR':addresses=((0,),(1,0))
    else:assert False
    terms=tuple(I.get(q,a) for a in addresses);bare=q
    for a,t in zip(addresses,terms):bare=I.alter(bare,a,I.leaf(t.vertices,t.edges,t.arrow))
    assert I.graft(bare,terms)==q
    return localize(bare)
def pairs(M):
    results=set()
    for p in I.SHAPES:
        for t in I.x_instances(p,M):
            for address,rule in I.redexes(t):
                l=abstract(I.get(t,address),rule);results.add((rule,l,I.rewrite(l,(),rule,M)))
    for rule,p in I.BARE:
        for l in I.x_instances(p,M):results.add((rule,l,I.rewrite(l,(),rule,M)))
    return sorted(results,key=repr)
def main():
    start=time.monotonic();per={}
    for name,M in I.TABLES.items():
        before=I.COUNT['MIn'];rows=pairs(M);per[name]={'bare_label_pairs':len(rows)}
        for rule,l,r in rows:
            I.min_checks(l,r,rule,M)
            for F in I.menu(l,M):
                a=I.graft(l,F);b=I.graft(r,F);assert I.rewrite(a,(),rule,M)==b;I.min_checks(a,b,rule,M)
        per[name]['MIn_squares']=I.COUNT['MIn']-before
    r={'status':'PASS','evidence':'independent supplement, no author imports','counts':dict(I.COUNT),'per_monoid':per,'elapsed_seconds':time.monotonic()-start,'domain_sha256':hashlib.sha256((P/'REVIEW_ADDENDUM_DOMAIN.md').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256((P/'check_noimport.py').read_bytes()).hexdigest()}
    (P/'ExpandedMInCertificate.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
