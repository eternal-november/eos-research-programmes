#!/usr/bin/env python3
"""A second obligation spends the gate mode after the first has cleared."""
import argparse
from decimal import Decimal as D, ROUND_FLOOR, localcontext
from fractions import Fraction as F
import hashlib
import json
from itertools import pairwise
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROBUST=HERE if (HERE/"robust.py").is_file() else HERE.parent
MISSION=ROBUST if (ROBUST/"mission_geom.py").is_file() else ROBUST.parent
PINS={"robust.py":"28c0aab2cc727f1fae86dc6663eb616fa73ecf3b","lease.py":"c05f30f904448a8fb4ce02c1e6ed42370f6619dc","mission_geom.py":"158b045681904d65c8b13edd32a78c387009d953"}

def verify(p):
    x=p.read_bytes()
    assert hashlib.sha1(f"blob {len(x)}\0".encode()+x).hexdigest()==PINS[p.name],p.name
for p in [ROBUST/"robust.py",MISSION/"lease.py",MISSION/"mission_geom.py"]:verify(p)
sys.path.insert(0,str(MISSION))
import mission_geom as g
import lease

R=F(3505,10000)
DT=D(1)/16

def strictly_after(t):
    return (int((t/DT).to_integral_value(rounding=ROUND_FLOOR))+1)*DT

def box(p,q):
    r=D(R.numerator)/D(R.denominator)
    return tuple(D(min(a,b))-r for a,b in zip(p,q)),tuple(D(max(a,b))+r for a,b in zip(p,q))
def disjoint(a,b):
    return any(x>v or u>y for x,y,u,v in zip(*a,*b))
def stationary(p):
    return tuple(D(x)-D(".30") for x in p),tuple(D(x)+D(".30") for x in p)

def normal(q, gate, at):
    into,out,done=lease.measure(q,gate,at,R)
    assert into<out<done
    return into,out,done

def bounds(q,own_gate,at,d,where):
    i,o,done=normal(q,own_gate,at)
    # Each prescribed leg begins and ends at rest. Upstream
    # wait at an existing rest point shifts contact; downstream
    # wait at an existing rest point leaves it unchanged.
    hits=[i for i,(a,b) in enumerate(pairwise(q)) if lease.slab(a,b,own_gate,R)]
    assert len(hits)==1 and 0<hits[0]<len(q)-2
    stop=hits[0] if where=="before" else hits[0]+1
    assert lease.slab(q[stop],q[stop],own_gate,R) is None
    if where=="before":return i+d,o+d,done+d
    return i,o,done+d

def pass_window(w, gate, flip, gamma):
    enter,clear,finish=normal(w,gate,D(0))
    # Move continuously from a rest endpoint toward the gate.
    # Hold until the first contact will occur at an authorized
    # time. Order is "open, then crossing" in this fixture.
    start=flip+gamma-enter
    assert start>=0 and enter>0
    eps=D(".001")
    assert not lease.contains_at(w,gate,start,flip+gamma-eps,R)
    assert lease.contains_at(w,gate,start,flip+gamma+eps,R)
    return start,flip+gamma,flip+gamma+(finish-enter)

def show(z):return str(round(z,8))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--paths",type=Path,default=HERE/"paths")
    a=p.parse_args()
    mission=json.loads(subprocess.check_output([sys.executable,"-B",str(ROBUST/"robust.py"),
           "--geom",str(a.geom),"--source",str(a.source),"--paths",str(a.paths)],text=True))
    e,mesh,fences,*_=g.load(a.geom,a.paths)
    blockers=[stationary(x) for x in [(100,-25,6),(100,75,8),(75,100,6),g.PROBE,g.END_R]]
    out={}
    tested=0
    with localcontext() as c:
        c.prec=60
        for scenario,active,open_q,w,code in [
            ("A",e.GATE_A,e.GATE_B,[(99,66,8),(99,61,8)],256),
            ("B",e.GATE_B,e.GATE_A,[(65,53,6),(60,53,6)],128)]:
            m=e.Map(mesh,fences+blockers+[open_q])
            r=D(R.numerator)/D(R.denominator)
            assert m.certificate(*w,r)>0
            assert g.exact_cross(*w,active)
            q=mission["paths"][str(code)]["path"]
            # Separate bodies even with simultaneous motion and waits.
            assert all(disjoint(box(*w),box(x,y)) for x,y in pairwise(q))
            for arm,offset in [("compact",D(".9375")),("full_wait",D("1.9375"))]:
                native=mission["cases"][scenario+"/"+arm]
                assert native["actual_return"]==code
                at=D(native["finish"])-D(mission["paths"][str(code)]["travel"])
                assert at==offset
                enter,out_q,done=normal(q,open_q,at)
                assert abs(out_q-D(native["clear"]))<D(".00000001")
                # The model declares egress must be complete by 200, not
                # a deadline tailored to W's benefit. W exposes a full
                # service frontier against motion-confirmed release.
                for gamma in [D(0),D(".0625"),D(1)]:
                    for where in ("before","after"):
                        for duration in (D(0),D(".125"),D(".5"),D(2)):
                            i,o,f=bounds(q,open_q,at,duration,where)
                            flip=strictly_after(o)
                            early_slot=strictly_after(out_q)
                            start,wu,finish=pass_window(w,active,flip,gamma)
                            _,_,whole=pass_window(w,active,strictly_after(f),gamma)
                            assert flip>o and wu>=flip and f<D(200)
                            assert whole-finish>D(60)
                            assert (early_slot>o)==(where=="after" or duration==0)
                            begun=lease.slab(*w,active,R)
                            assert begun is not None
                            close_mid=early_slot if i<early_slot<o else (i+o)/2
                            if where=="before" and duration>D(0):
                                assert i<close_mid<o and close_mid>early_slot-DT
                            if duration==0 and gamma==1 and where=="before":
                                out[scenario+"/"+arm]={"q_clear":show(o),"q_finish":show(f),
                                  "gate_flip":show(flip),"w_first_gate_contact":show(wu),
                                  "w_start_rolling":show(start),"w_finish":show(finish),
                                  "whole_egress_release_finish":show(whole),
                                  "saved_over_whole_egress":show(whole-finish)}
                            tested+=1
    print(json.dumps(dict(cases=out,finite_schedule_checks=tested),sort_keys=True))
if __name__=="__main__":main()
