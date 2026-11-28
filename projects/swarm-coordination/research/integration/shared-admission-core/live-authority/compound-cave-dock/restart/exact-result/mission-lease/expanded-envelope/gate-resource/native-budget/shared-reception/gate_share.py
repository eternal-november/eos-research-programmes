#!/usr/bin/env python3
"""Pinned dispatch and typed, local reuse of an inspection receipt."""
import argparse
from decimal import Decimal as D, localcontext
from itertools import product
import hashlib
import json
from pathlib import Path
from subprocess import check_output,run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=next(x for x in (HERE,*HERE.parents) if (x/"gate_radio.py").is_file())
p=PARENT/"gate_radio.py"
raw=p.read_bytes()
assert hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="7f2e9fd733f7cf8452f513503c7cf8d819bacc1a"
sys.path.insert(0,str(PARENT))
import gate_radio as r

def verify(w,geom,src,paths):
    r.radio(w) # reuse the parent's exact world DOT projection and source manifest
    staged=(w/"staged_replay.inc").read_text()
    before="  return receiver->OnMessageRos(r,res);"
    assert staged.count(before)==1
    (w/"staged_roles.inc").write_text(staged.replace(" bool Request(const std::string&,subt::msgs::Datagram msg){",
        " std::map<std::string,CommsClient*> roles;\n"
        " bool Request(const std::string& who,subt::msgs::Datagram msg){")
      .replace(before,"  return (roles.count(who)?roles.at(who):receiver)->OnMessageRos(r,res);"))
    (w/"gate_share.cpp").write_bytes((HERE/"gate_share.cpp").read_bytes())
    (w/"gate_receipt.hpp").write_bytes((HERE/"gate_receipt.hpp").read_bytes())
    run(["g++","-std=c++17","-O2","-Wno-return-type","gate_share.cpp","-o","gate-share"],
      cwd=w,check=True)
    robust=json.loads(check_output([sys.executable,"-B",str(r.RDIR/"robust.py"),
      "--geom",str(geom),"--source",str(src),"--paths",str(paths)],text=True))
    e,*_=r.g.load(geom,paths)
    sites=((51,25,6),(50,25,6))
    tests=[]
    with localcontext() as c:
        c.prec=50
        for layout,code,gate in (("A",256,e.GATE_B),("B",128,e.GATE_A)):
            route=robust["paths"][str(code)]
            for arm in ("compact","full_wait"):
                result=robust["cases"][f"{layout}/{arm}"]
                assert result["actual_return"]==code
                anchor=D(result["finish"])-D(route["travel"])
                first,last,_=r.lease.measure(route["path"],gate,anchor,r.BOX)
                slot=D(int(last*16)+1)/16
                inside=last-min((last-first)/4,D(1)/64)
                assert r.lease.contains_at(route["path"],gate,anchor,inside,r.BOX)
                # Actual path prefix delayed by a lawful hold at its initial rest cut.
                # The same scheduled radio send happens while still in contact.
                delay=slot-inside
                assert delay>0
                assert r.lease.contains_at(route["path"],gate,anchor+delay,slot,r.BOX)
                assert slot>last
                assert not r.lease.contains_at(route["path"],gate,anchor,slot,r.BOX)
                assert not r.lease.contains_at(route["path"],gate,anchor+delay,slot+1,r.BOX)
                for cap,mode,profile,head in product((4,5,8),range(3),range(4),range(2)):
                    # profile 0: no gate authority at joint host; 1: fresh scoped source;
                    # 2: ordinary buffered report from before clearance;
                    # 3: correctly issued for an old epoch (scope mismatch).
                    # head 1: held at the initial rest cut until the source is late.
                    issued=inside+head*delay if profile==2 else slot
                    clear=last+head*delay
                    live_epoch,issued_epoch=7,6 if profile==3 else 7
                    usable=issued>clear and issued_epoch==live_epoch
                    scope=0 if profile==0 else 1 if usable else 2
                    q=r.source_coordinates(route["path"],anchor+head*delay,slot)
                    record=(cap,mode,int(profile!=0),issued_epoch,live_epoch,issued,clear,slot,*q,*sites[0],*sites[1])
                    tests.append((layout,arm,profile,head,scope,record))
    packet="".join(" ".join(map(str,record))+"\n" for *_,record in tests)
    result=check_output([w/"gate-share"],cwd=w,text=True,input=packet).splitlines()
    assert len(result)==len(tests)
    witnesses={}
    for (layout,arm,profile,head,scope,(cap,mode,_,_,_,_,_,slot,*_)),line in zip(tests,result):
        report,desk,gate,local,tx,base_rx,desk_rx=got=tuple(map(int,line.split()))
        want_report=int(mode!=1 or cap>=8)
        want_desk=int(mode==1 or mode==0 and cap>=8)
        want_local=int(mode==2 and scope!=0)
        assert got==(want_report,want_desk,int((scope==1 or profile==0 and head==0) and (want_desk or want_local)),
                     want_local,4*(want_report+want_desk),4*want_report,4*want_desk), (layout,arm,profile,head,cap,mode,got)
        if arm=="compact" and layout=="B" and (profile==1 or mode==2 and cap==4):
            witnesses[f"cap={cap}/mode={mode}/profile={profile}/delay={head}"]=[str(slot),*got]
    print(json.dumps({"cases":len(tests),"columns":["time","report","desk","open","local_handoff",
      "tx","report_rx","desk_rx"],"witnesses":witnesses},sort_keys=True))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--paths",type=Path,default=HERE/"paths")
    a=p.parse_args()
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        r.mission.v.f.compile_native(a.geom,a.source,w)
        verify(w,a.geom,a.source,a.paths)
if __name__=="__main__":main()
