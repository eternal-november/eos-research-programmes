#!/usr/bin/env python3
"""Calculate the required gate lease from the actual callback and chosen path."""
import argparse
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import pairwise
import json
from pathlib import Path
import subprocess
import sys
import mission_geom as g

HERE=Path(__file__).resolve().parent

def slab(start,end,gate,r=F(3005,10000)):
    lo,hi=F(0),F(1)
    for a,b,l,h in zip(start,end,*gate):
        u,v=F(l)-r,F(h)+r
        if a==b:
            if not u<=a<=v:return None
            continue
        i,j=sorted(((u-a)/(b-a),(v-a)/(b-a)))
        lo,hi=max(lo,i),min(hi,j)
    return (lo,hi) if lo<=hi else None

def measure(route,opened,clock, radius=F(3005,10000)):
    periods=[]
    for a,b in pairwise(route):
        L=sum(D(x-y)**2 for x,y in zip(a,b)).sqrt()
        peak=min(D(3),L.sqrt())
        T=L/peak+peak
        boundary=peak**2/2
        def inverse(lam):
            p=L*D(lam.numerator)/D(lam.denominator)
            if p<=boundary:return (2*p).sqrt()
            if p>=L-boundary:return T-(2*(L-p)).sqrt()
            return peak+(p-boundary)/peak
        s=slab(a,b,opened,radius)
        if s is not None:
            enter,exit=s
            periods.append((clock+inverse(enter),clock+inverse(exit)))
        clock+=T
    assert periods
    enter,last=periods[0][0],periods[-1][-1]
    assert enter<last<clock
    return enter,last,clock

def contains_at(route,gate,clock,cut,radius=F(3005,10000)):
    for a,b in pairwise(route):
        L=sum(D(x-y)**2 for x,y in zip(a,b)).sqrt()
        peak=min(D(3),L.sqrt())
        T=L/peak+peak
        if clock<=cut<=clock+T:
            s=cut-clock
            if s<=peak:progress=s*s/2
            elif s>=T-peak:progress=L-(T-s)**2/2
            else:progress=peak*s-peak*peak/2
            pose=[D(x)+D(y-x)*progress/L for x,y in zip(a,b)]
            r=D(radius.numerator)/D(radius.denominator)
            return all(D(lo)-r<at<D(hi)+r for lo,hi,at in zip(*gate,pose))
        clock+=T
    return False

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--geom",type=Path,default=HERE/"geometry")
    a.add_argument("--source",type=Path,default=HERE/"source")
    a.add_argument("--paths",type=Path,default=HERE/"paths")
    z=a.parse_args()
    native=json.loads(subprocess.check_output([
            sys.executable,"-B",str(HERE/"mission.py"),
            "--geom",str(z.geom),"--source",str(z.source),"--paths",str(z.paths)
        ],text=True))
    lib,_=g.solve(z.geom,z.paths)
    e,*_=g.load(z.geom,z.paths)
    out={}
    with localcontext() as c:
        c.prec=60
        for k,v in native["cases"].items():
            if v.get("hold"):continue
            opened=e.GATE_B if v["returned"]==256 else e.GATE_A
            lo,hi,done=measure(lib[v["returned"]]["path"],opened,D(v["returned_at"]))
            assert abs(done-D(v["egress"]))<D(".00000001")
            # Adversarial withdrawal just inside this nonempty window
            # collides; withdrawal after the last interval is harmless.
            assert hi-lo>D(".0001")
            assert done-hi>D(60)
            path=lib[v["returned"]]["path"]
            start=D(v["returned_at"])
            assert contains_at(path,opened,start,(lo+hi)/2)
            assert not contains_at(path,opened,start,hi+D(".0001"))
            out[k]={"enter":str(round(lo,8)),"clear":str(round(hi,8)),
                    "swap_mid_contact_witness":True,"done":str(round(done,8)),
                    "beyond_clear":str(round(done-hi,8))}
    for blocked in ("A","B"):
        t=out[blocked+"/compact"];u=out[blocked+"/full_wait"]
        assert D(u["clear"])-D(t["clear"])==1
    print(json.dumps(out,sort_keys=True))
if __name__=="__main__":main()
