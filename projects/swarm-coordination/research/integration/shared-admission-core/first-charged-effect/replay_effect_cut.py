#!/usr/bin/env python3
"""Native RWARE and SubT probes for a common serialized read-and-commit rule."""
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from collections import Counter

HERE=Path(__file__).resolve().parent
PINS={"staged_replay.inc":"d7dd3aee6bc8577ed6b6499693d4bc1ae31bd0eb",
      "extract_radio.py":"3763e755ff46b57e79d760a0f400f978fcff910e",
      "visibility_shim.hpp":"8eea2a6c06b246da42a4aa61eab0d27e004f2a03",
      "extract_visible.py":"c529046ba85224f53228e6a1647f501860dfcb4b",
      "support.py":"b0e6c09b6ba593ccd373371541f0d20a0ff8a414"}

def read(pin):
    b=pin.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==PINS[pin.name]
    return b

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    args=p.parse_args()
    read(args.support)
    sys.path.insert(0,str(args.support.resolve().parent))
    import support,physical_effect as p
    with tempfile.TemporaryDirectory() as tmp:
        w=Path(tmp)
        for name in ("extract_radio.py","visibility_shim.hpp"):
            (w/name).write_bytes(read(args.source/name))
        (w/"extract_visible.py").write_bytes(read(args.source/"extract_visible.py"))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc","Vector3.hh","world.dot","world.sdf","broker.cc"):
            shutil.copyfile(args.source/name,w/name)
        subprocess.run([sys.executable,"-B","extract_visible.py"],cwd=w,check=True)
        read(w/"staged_replay.inc")
        for i in range(6):
            shutil.copyfile(args.source/f"src{i}",w/f"src{i}")
        subprocess.run([sys.executable,"-B","extract_radio.py"],cwd=w,check=True)
        for name in ("radio_effect.cc","first_effect.hpp","bridge.cc"):
            shutil.copyfile(HERE/name,w/name)
        subprocess.run(["g++","-std=c++17","-O2","-Wno-return-type","radio_effect.cc","-o","radio"],cwd=w,check=True)
        subprocess.run(["g++","-std=c++17","-O2","-fPIC","-shared","bridge.cc","-o","bridge.so"],cwd=w,check=True)
        choose=p.bridge(w/"bridge.so")
        iso,n=support.load(args.warehouse)
        physical={}
        for case in product(range(2),range(3),range(5)):
            pre,post,arm=case
            expect=int(post!=2 and (arm in (0,4) or (arm==1 and pre==post)
                                      or (arm==2 and post==1) or (arm==3 and post==0)))
            count=int(post!=2 or arm not in (0,4))
            physical[case]=p.episode(iso,n,choose,*case)
            assert physical[case]==(expect,1,count),(case,physical[case])
        cases=list(product(range(2),range(3),range(5),(4,5,7,8),(0,1),(4,5,8),(0,1)))
        x=subprocess.check_output([w/"radio"],cwd=w,text=True,input=
            "".join(" ".join(map(str,t))+"\n" for t in cases))
        out=[tuple(map(int,row.split())) for row in x.splitlines()]
        assert len(out)==len(cases)
        witnesses={}
        radio=Counter()
        for z,(paid,side,spent) in zip(cases,out):
            pre,post,arm,cap,retry,side_bytes,edge=z
            blocked=side_bytes+4>cap
            late=set(range(2)) if post==2 else {post}
            eligible={k for k in range(2)
                  if side_bytes*((k in late)+(edge and k==pre))+4<=cap}
            if arm in (0,4):
                expect=int(bool(eligible));debit=4*expect
            else:
                first=(1-pre if blocked else 0) if arm==1 else arm-2
                second=1-first
                success=first in eligible
                send_again=not success and retry and cap>=8
                expect=int(success or send_again and second in eligible)
                debit=4*(1+send_again)
            assert (paid,side,spent)==(expect,3 if post==2 else 2,debit),(z,out)
            radio[arm]+=paid
            if (cap,retry,side_bytes)==(4,1,4) and pre==0:
                witnesses[str((post,arm,edge))]=(paid,side,spent)
        assert radio[0]==radio[4]
    print(json.dumps(dict(radio_cases=len(cases),radio_paid=dict(radio),physical_cases=len(physical),
          physical_paid={a:sum(v[0] for k,v in physical.items() if k[2]==a) for a in range(5)},
          witness_columns=["old duty paid","unrelated reports credited","tx payload bytes debited"],
          tight_cut_witnesses=witnesses),sort_keys=True))

if __name__=="__main__":main()
