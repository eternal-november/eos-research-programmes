#!/usr/bin/env python3
"""Preflight subsets ONLY; never substitutes for the frozen full-domain run."""
import check_integration as d
from model import *
from pathlib import Path
import hashlib,json,time

def main():
    start=time.monotonic();d.named_controls();print('SMOKE named controls passed',flush=True)
    for M in MONOIDS:
        for row,p in enumerate(d.PATTERNS,1):
            vals=tuple(d.x_realizations(p,M));sel=(vals[0],vals[-1])
            for t in sel:d.check_term(t,M);d.explicit_join(t,row,M)
    print('SMOKE T (first/last X representative per row and monoid) passed',flush=True)
    catalogs={}
    for M in MONOIDS:
        extracted=set();bases=set()
        for rule,p in d.BARE:
            bases.update((rule,t) for t in d.x_realizations(p,M))
        for row,p in enumerate(d.PATTERNS,1):
            vals=tuple(d.x_realizations(p,M))
            for t in vals:
                for addr,rule,u in steps(t,M):
                    l,F=d.abstract_redex(d.at(t,addr),rule,M);extracted.add((rule,l))
            for t in (vals[0],vals[-1]):
                for addr,rule,u in steps(t,M):
                    for cname,host,prefix in d.contexts(t,M):
                        target=d.replace_at(host,prefix,u);menu=tuple(d.forest_menu(host,M))
                        for F in menu[:2]+menu[-2:]:d.check_mout(host,target,prefix+addr,rule,F,M)
        union=bases|extracted;catalogs[M.name]={'base':len(bases),'arising':len(extracted),'union':len(union),'additional':len(extracted-bases)}
        assert len(union)=={'Z3':147,'E2':102,'One':67}[M.name]
        for rule,l in sorted(union,key=repr):d.check_bare_case(rule,l,M,'smoke_union',smoke=True)
    print('SMOKE X catalog and selected forests passed',catalogs,flush=True)
    for M in MONOIDS:
        g=Graph(1);a=Arrow(1,1)
        for k in (0,1,2):
            for src in catalog(g,a,k,M):
                encoded={}
                for F,mid in tuple_encoder(src,2,M):encoded.setdefault(mid,set()).add(arrow_key(F))
                for l in range(3):
                    for tgt in catalog(g,a,l,M):assert hom_decode(src,tgt,M)==encoded.get(tgt,set())
                for F,mid in tuple_encoder(src,2,M):
                    for H,tgt in tuple_encoder(mid,2,M):d.check_raw_flat_pair(src,F,H,tgt,M,'smoke_Hcomp_raw_pairs')
    print('SMOKE H decoder/raw composition passed',flush=True)
    for M in MONOIDS:
        w=Flat(Graph(2,((0,1),)),Arrow(0,2),((0,),(),(1,),()),(Arrow(0,1),Arrow(1,1),Arrow(1,1),Arrow(1,2)),0)
        for v in range(M.size):
            wv=d.replace(w,value=v)
            for q in (2,3):
                for i in range(4-q+1):d.check_factor(wv,i,i+q,M)
    print('SMOKE F candidate encoder passed',flush=True)
    files=('model.py','check_integration.py','smoke_integration.py')
    out={'status':'PASS','kind':'NARROW_STAGE_PREFLIGHT_NOT_FULL_DOMAIN','domain_sha256':hashlib.sha256((d.HERE/'DOMAIN.md').read_bytes()).hexdigest(),'source_sha256':{x:hashlib.sha256((d.HERE/x).read_bytes()).hexdigest() for x in files},'catalogs':catalogs,'counts':dict(d.COUNTS),'elapsed_seconds':round(time.monotonic()-start,3)}
    (d.HERE/'SmokeCertificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
