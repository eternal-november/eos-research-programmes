#!/usr/bin/env python3
"""Replace a fragile path at the same source/radio cut under a larger body envelope."""
import argparse
import hashlib
import subprocess
import sys
from decimal import Decimal as D
from fractions import Fraction as F
from itertools import pairwise
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"mission.py").is_file() else HERE.parent
PINS={"mission.py":"94d832775272ac4deb099b7528e8f563c64156f3","mission_geom.py":"158b045681904d65c8b13edd32a78c387009d953","lease.py":"c05f30f904448a8fb4ce02c1e6ed42370f6619dc"}
for k,expected in PINS.items():
    x=(PARENT/k).read_bytes()
    assert hashlib.sha1(f"blob {len(x)}\0".encode()+x).hexdigest()==expected,k
sys.path.insert(0,str(PARENT))
import mission_geom as g
import lease
def body(pos):
    return tuple(D(x)-D(".30") for x in pos),tuple(D(x)+D(".30") for x in pos)
def expanded_type(e,r):
    class Expanded(e.Map):
        def clear(self,u,v):
            import numpy as np
            lo=np.minimum(u,v)-float(r)
            hi=np.maximum(u,v)+float(r)
            for a,b in self.fences:
                if all(float(a[i])<=hi[i] and float(b[i])>=lo[i] for i in range(3)):
                    return False
            ss=self.sub(lo,hi)
            return len(ss)==0 or e.visual_margin(self.F[ss],lo,hi)>1e-8
        def certificate(self,u,v):
            return super().certificate(u,v,r)
    return Expanded

def solve(geometry,paths):
    e,t,f,*_=g.load(geometry,paths)
    # P, S, D, observation M, and retired R are holding still from
    # the return cut. No new robot uncertainty is granted here.
    bodies=[body(p) for p in [(100,-25,6),(100,75,8),(75,100,6),g.PROBE,g.END_R]]
    _,_,positions=e.load_scene()
    nominal,_=g.solve(geometry,paths)
    out={}
    for code,closed,opened,spine in [
       (256,e.GATE_A,e.GATE_B,[16,6,8,3,2,39,9,4,0]),
       (128,e.GATE_B,e.GATE_A,[16,42,13,1,43,39,9,4,0])]:
        r=D(".3505")
        M=expanded_type(e,r)(t,f+bodies+[closed])
        misses=0
        for u,v in pairwise(nominal[code]["path"]):
            try:M.certificate(u,v)
            except AssertionError:misses+=1
        assert misses>0
        walk,n=e.search(M,g.ANCHOR,g.GOAL,spine,positions,width=7)
        assert walk is not None,(code,r,n)
        # Compressing collinear grid edges retains their swept union.
        # Chords are checked afresh against the larger swept boxes.
        rr,dt,gap=g.chord(M,e.compress(walk))
        assert all(M.certificate(a,b)>0 for a,b in pairwise(rr))
        guard=lease.measure(rr,opened,D(0),F(r))
        assert guard[2]<200
        out[code]=dict(missed_nominal_certificates=misses,expanded_half_box=str(r),
                       new_legs=len(rr)-1,graph_search_labels=n,
                       travel=str(round(dt,8)),clear_offset=str(round(guard[1],8)),new_margin=round(gap,8),path=rr)
    return out

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--paths",type=Path,default=HERE/"paths")
    a=p.parse_args()
    z=json.loads(subprocess.check_output([sys.executable,"-B",str(PARENT/"mission.py"),
        "--geom",str(a.geom),"--source",str(a.source),"--paths",str(a.paths)],text=True))
    paths=solve(a.geom,a.paths)
    cases={}
    for k,v in z["cases"].items():
        if v.get("hold"):
            cases[k]={"hold":True}
            continue
        path=paths[v["returned"]]
        start=D(v["returned_at"])
        finish=start+D(path["travel"])
        assert finish<200
        cases[k]={"finish":str(finish),"clear":str(start+D(path["clear_offset"])),
            "actual_return":v["returned"]}
    for side in ("A","B"):
        x=cases[side+"/compact"]
        y=cases[side+"/full_wait"]
        assert D(y["finish"])-D(x["finish"])==1 and D(y["clear"])-D(x["clear"])==1
    print(json.dumps(dict(paths=paths,cases=cases),sort_keys=True))
