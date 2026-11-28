#!/usr/bin/env python3
"""Joined native source fixture, with a synchronous local adapter in each arm."""
import argparse
from itertools import product
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
import shutil
import subprocess as sp
import sys
import tempfile
import numpy as np

HERE=Path(__file__).resolve().parent
PARENT=next(x for x in (HERE,*HERE.parents) if (x/"replay_effect_cut.py").is_file())
sys.path.insert(0,str(PARENT))
import replay_effect_cut as setup

def pin(path,digest):
    b=path.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==digest
    return b

pin(PARENT/"replay_effect_cut.py","c599a366c8c4e0e5969314d858f7c0ca1d169ffd")


import motion_journal as j

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    args=p.parse_args()
    setup.read(args.support)
    sys.path.insert(0,str(args.support.resolve().parent))
    import support
    with tempfile.TemporaryDirectory() as tmp:
        w=Path(tmp)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (w/name).write_bytes(setup.read(args.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(args.source/name,w/name)
        for name in ("extract_visible.py","extract_radio.py"):
            sp.run([sys.executable,"-B",name],cwd=w,check=True)
        setup.read(w/"staged_replay.inc")
        shutil.copyfile(HERE/"journal_effect.cc",w/"journal_effect.cc")
        (w/"first_effect.hpp").write_bytes(pin(PARENT/"first_effect.hpp","1e1624f0de957d627ea57182d94dbbb28d06c8a4"))
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","journal_effect.cc","-o","join"],cwd=w,check=True)
        iso,n=support.load(args.warehouse)
        runs=Counter()
        examples={}
        traces={}
        plant=j.Plant(iso,n)
        with sp.Popen([w/"join"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as p:
            def emit(*a):p.stdin.write(" ".join(map(str,a))+"\n");p.stdin.flush()
            for prior,blocked,after,arm,edge in product(range(2),range(2),range(4),range(4),range(2)):
                case=(prior,blocked,after,arm,edge)
                path=w/("native-"+"-".join(map(str,case))+".sqlite")
                db=j.connect(path)
                assert j.apply(db,plant,None,3)==("new",[1,3,3,4])
                db.close()
                prior_key=j.OLD if prior else j.SAME_PHYSICAL_UNRELATED
                proc=sp.run([sys.executable,"-B",HERE/"motion_journal.py",path,prior_key,args.warehouse.resolve()],
                            capture_output=True,text=True,env={**os.environ,"PYTHONPATH":str(args.support.resolve().parent)})
                assert proc.returncode==77 and not proc.stdout and not proc.stderr,(case,proc)
                db=j.connect(path)
                if blocked:assert j.apply(db,plant,None,2)==("new",[3,2,2,2])
                pre=plant.native(db); old_tick=pre._cur_steps
                motions=list(db.execute("select * from motion"))
                existing=j.resolved(db,j.OLD)
                assert existing==([2,0,2,1] if prior else None)
                if prior:assert traces.pop(case[1:])==(motions,plant.snapshot(pre))
                else:traces[case[1:]]=(motions,plant.snapshot(pre))
                result=None
                emit(0,after,arm,edge)
                while True:
                    line=p.stdout.readline().split()
                    assert line
                    if line[0]=="P":emit(1)
                    elif line[0]=="I":
                        k=int(line[1])
                        allow=(existing is not None or not pre.grid[0,k+1,2])
                        if arm==2:allow=not pre.grid[0,k+1,2] # suppress keyed evidence before dispatch
                        emit(int(allow))
                    elif line[0]=="M":
                        k=int(line[1])
                        status,result=j.apply(db,plant,j.OLD,k)
                        emit({"blocked":0,"new":1,"cached":2}[status])
                    else:
                        assert line[0]=="O";break
                paid,rx,side,tx,reads,outcome=map(int,line[1:])
                rad=set(range(2))-({0,1} if after==2 else set() if after==3 else {after})-({0} if edge else set())
                mov={1} if not blocked else set()
                propose=rad&({0,1} if prior else mov) if arm<2 else rad&mov if arm==2 else rad
                k=min(propose,default=-1)
                expected=0 if k<0 else 2 if prior else int(k in mov)
                assert (outcome,paid,rx,tx)==(expected,int(expected>0),int(k>=0),int(k>=0)*4)
                assert (expected==0 and result is None
                     or expected==2 and result==[2,0,2,1]
                     or expected==1 and result==[old_tick+1,1,2,2])
                assert plant.native(db)._cur_steps==old_tick+int(expected==1)
                assert len(list(db.execute("select * from receipt where key=?",(j.OLD,))))==int(prior or expected==1)
                runs[f"paid/{arm}"]+=paid
                runs[f"cached/{arm}"]+=int(expected==2)
                runs[f"charge_without_effect/{arm}"]+=int(tx>0 and not paid)
                if after==0 and not edge:
                    examples[str((prior,blocked,arm))]=[paid,rx,tx,result]
                db.close()
            p.stdin.close();assert p.wait()==0
        assert not traces and runs["paid/0"]==runs["paid/1"]
    print(json.dumps({"cases":sum(1 for _ in product(range(2),range(2),range(4),range(4),range(2))),
        "results":dict(runs),"columns":["credited","radio_received","q_tx","returned_record"],"witnesses":examples},sort_keys=True))
if __name__=="__main__":main()
