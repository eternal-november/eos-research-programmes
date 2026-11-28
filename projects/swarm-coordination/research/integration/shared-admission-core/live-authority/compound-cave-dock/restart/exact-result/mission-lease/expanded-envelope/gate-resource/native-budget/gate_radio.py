#!/usr/bin/env python3
"""Use actual pinned broker accounting at the modeled release cut."""
import argparse
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
import hashlib
import heapq
import importlib.util
import json
from itertools import pairwise,product
from pathlib import Path
import re
from subprocess import check_output,run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
RDIR=next(p for p in [HERE,*HERE.parents] if (p/"robust.py").exists())
MDIR=next(p for p in [HERE,*HERE.parents] if (p/"mission.py").exists())
PINS={"robust.py":"28c0aab2cc727f1fae86dc6663eb616fa73ecf3b","mission.py":"94d832775272ac4deb099b7528e8f563c64156f3","lease.py":"c05f30f904448a8fb4ce02c1e6ed42370f6619dc"}
for p in (RDIR/"robust.py",MDIR/"mission.py",MDIR/"lease.py"):
    b=p.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==PINS[p.name]
sys.path.insert(0,str(MDIR))
import mission
import mission_geom as g
import lease

BOX=F(3505,10000)

def source_coordinates(path,clock,read_at):
    for a,b in pairwise(path):
        L=sum(D(x-y)**2 for x,y in zip(a,b)).sqrt()
        v=min(D(3),L.sqrt())
        t=L/v+v
        if clock<=read_at<=clock+t:
            delta=read_at-clock
            if delta<=v:s=delta**2/2
            elif delta>=t-v:s=L-(t-delta)**2/2
            else:s=v*delta-v*v/2
            return tuple(D(x)+D(y-x)*s/L for x,y in zip(a,b))
        clock+=t
    raise ValueError((clock,read_at))

def radio(work):
    graph={}
    for a,b,w in re.findall(r"(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]",(work/"world.dot").read_text()):
        a,b,w=map(int,(a,b,w))
        graph.setdefault(a,[]).append((b,w))
        graph.setdefault(b,[]).append((a,w))
    ids=sorted(graph)
    def ds(k):
        dist={k:0};q=[(0,k)]
        while q:
            t,a=heapq.heappop(q)
            if t!=dist[a]:continue
            for b,w in graph[a]:
                if t+w<dist.get(b,10**9):
                    dist[b]=t+w;heapq.heappush(q,(t+w,b))
        return " ".join(str(dist.get(x,10**9)) for x in ids)
    (work/"all-dist.tsv").write_text(str(len(ids))+"\n"+" ".join(map(str,ids))+"\n"+
                                   "\n".join(ds(k) for k in ids)+"\n")
    (work/"gate_radio.cpp").write_bytes((HERE/"gate_radio.cpp").read_bytes())
    run(["g++","-std=c++17","-O2","-Wno-return-type","gate_radio.cpp","-o","scope-radio"],
        cwd=work,check=True)

def verify(work,geom,pin,src):
    nominal=json.loads(check_output([sys.executable,"-B",str(RDIR/"robust.py"),
        "--geom",str(geom),"--source",str(src),"--paths",str(pin)],text=True))
    e,mesh,fences,*_=g.load(geom,pin)
    static=e.Map(mesh,fences)
    hubs=((51,25,6),(50,25,6))
    for node in hubs:assert static.certificate(node,node)>0
    radio_boxes=[(tuple(D(x)-D(".30") for x in node),
                  tuple(D(x)+D(".30") for x in node)) for node in hubs]
    test=[]
    keys=[]
    with localcontext() as cx:
        cx.prec=50
        for scen,gate,desk,code in [("A",e.GATE_B,(99,66,8),256),("B",e.GATE_A,(65,53,6),128)]:
            for arm in ("compact","full_wait"):
                x=nominal["cases"][scen+"/"+arm]
                assert x["actual_return"]==code
                path=nominal["paths"][str(code)]
                for q0,q1 in pairwise(path["path"]):
                    assert all(lease.slab(q0,q1,panel,BOX) is None for panel in radio_boxes)
                anchor=D(x["finish"])-D(path["travel"])
                _,t,_=lease.measure(path["path"],gate,anchor,BOX)
                slot=D(int(t*16)+1)/16
                assert slot>t
                q=[source_coordinates(path["path"],anchor,tg) for tg in
                     (slot,slot+1,slot+D(17)/16)]
                for cap,mode,sites in product((4,5),range(3),("confirmed","original")):
                    # Two fixed distinct control/inspection radios in
                    # the connected hub. Original endpoints retain the
                    # preliminary scope and are an actual mismatch control.
                    recipients=hubs if sites=="confirmed" else (desk,(100,75,8))
                    test.append(" ".join(str(k) for k in [cap,mode,slot,*q[0],*q[1],
                                             *q[2],*recipients[0],*recipients[1]]))
                    keys.append((scen,arm,cap,mode,slot,sites))
    transcript=check_output([work/"scope-radio"],cwd=work,text=True,
                                  input="\n".join(test)+"\n").splitlines()
    assert len(transcript)==len(keys)
    witnesses={}
    for row,key in zip(transcript,keys):
        cap,mode,slot,report,notice,tx=map(D,row.split())
        sc,arm,c,m,s,sites=key
        assert (cap,mode,slot)==(c,m,s)
        delta=D(17)/16 if cap==4 else D(0)
        if sites=="confirmed":
            assert (report,notice)==((slot,-1) if mode==0 else
                     (slot,slot+delta) if mode==1 else (slot+delta,slot)),(key,row)
        elif sc=="A":
            assert (report,notice)==(-1,-1) and tx>0
        else:
            # A failed notice still spends at Q; the unrelated report
            # is delayed under completion-first even though no notice arrived.
            assert (report,notice)==((slot+(delta if mode==2 else 0)),-1)
        if arm=="compact":
            witnesses[f"{sites}/{sc}/{c}/{m}"]={"independent_report":str(report),
                    "actual_clearance_notice":str(notice),"resolved_gate_cut":str(slot),
                    "final_live_sender_bytes":str(tx)}
    print(json.dumps(dict(cases=len(keys),witnesses=witnesses),sort_keys=True))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--paths",type=Path,default=HERE/"paths")
    a=p.parse_args()
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        mission.v.f.compile_native(a.geom,a.source,w)
        radio(w)
        verify(w,a.geom,a.paths,a.source)
if __name__=="__main__":main()
