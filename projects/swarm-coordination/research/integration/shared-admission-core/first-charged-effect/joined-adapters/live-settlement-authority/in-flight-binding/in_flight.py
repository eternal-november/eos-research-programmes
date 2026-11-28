#!/usr/bin/env python3
"""A fixed dock address with either prebound or locally late-bound physical actor."""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse
import json
import shutil
import subprocess as sp
import sys
import tempfile
import numpy as np

HERE=Path(__file__).resolve().parent
P=next(x for x in (HERE,*HERE.parents) if (x/"replay_effect_cut.py").is_file())
sys.path.insert(0,str(P))
import replay_effect_cut as setup

def native(support,iso,n,block):
    w=iso.make(n,False)
    w.shelfs=[];w.goals=[];w.request_queue=[]
    n.Agent.counter=0
    w.agents=[
      n.Agent(1,1,n.Direction.RIGHT,0),n.Agent(1,2,n.Direction.RIGHT,0),
      n.Agent(3,1,n.Direction.LEFT,0),n.Agent(3,2,n.Direction.LEFT,0),
      n.Agent(4,4,n.Direction.LEFT,0)]
    w.n_agents=5;w.grid=np.zeros((2,5,5),dtype=int);w._recalc_grid()
    a=n.Action
    def step(who):
        commands=[a.NOOP.value]*5;commands[who]=a.FORWARD.value
        n.step(w,commands)
    step(4)
    assert support.pos(w.agents[4])==(3,4)
    def open_cells():return [int(w.grid[0,k+1,2])==0 for k in (0,1)]
    assert open_cells()==[True,True]
    def second():
        if block<2:step(2+block)
        if block==3:step(2);step(3)
        return open_cells()
    def issue(actor):
        assert open_cells()[actor]
        step(actor)
        assert support.pos(w.agents[actor])==(2,actor+1)
    return second,issue

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    setup.read(a.support)
    sys.path.insert(0,str(a.support.resolve().parent));import support
    iso,n=support.load(a.warehouse)
    totals=Counter();res={};pairs={}
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (w/name).write_bytes(setup.read(a.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/name,w/name)
        for name in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",name],cwd=w,check=True)
        setup.read(w/"staged_replay.inc");shutil.copyfile(HERE/"in_flight.cc",w/"in_flight.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","in_flight.cc","-o","flight"],cwd=w,check=True)
        with sp.Popen([w/"flight"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for initial,block,regrant,side_to,reply_first,cap,arm in product(
                range(2),range(4),range(2),range(3),range(2),(4,8),range(3)):
                second,issue=native(support,iso,n,block)
                emit(initial,side_to,reply_first,cap,arm)
                chosen=[];callback=False;live=2
                while True:
                    row=proc.stdout.readline().split();assert row
                    if row[0]=="L":
                        assert not callback
                        callback=True;cells=second()
                        live=initial if cells[initial] else (1-initial if regrant and cells[1-initial] else 2)
                        emit(live)
                    elif row[0]=="M":
                        k=int(row[1]);assert callback and k==live and not chosen
                        issue(k);chosen.append(k);emit(1)
                    else:
                        assert row[0]=="O";break
                budget=not (side_to==0 and not reply_first and cap==4)
                effected=budget and live<2 and (arm!=0 or live==initial)
                reply=effected and not (side_to==1 and not reply_first)
                expected=[int(effected),int(budget and not effected),int(side_to<2),int(reply),
                          int(effected),int(budget),4*int(budget),4*int(effected)]
                got=list(map(int,row[1:]));assert got==expected and callback==budget
                assert len(chosen)==int(effected)
                for k,v in zip(("settled","refused","side","replied"),got[:4]):totals[f"{k}/{arm}"]+=v
                totals[f"cases/{arm}"]+=1
                res[(initial,block,regrant,side_to,reply_first,cap,arm)]=got
                if (initial,regrant,side_to,reply_first,cap)==(0,1,2,0,4):pairs[str((block,arm))]=[got,chosen]
            proc.stdin.close();assert proc.wait()==0
    for k,v in res.items():
        if k[-1]==1:assert v==res[k[:-1]+(2,)]
    print(json.dumps({"counts":dict(totals),
      "columns":["settled","refused","side","reply","actual_moves","received","Q_tx","D_tx"],
      "witness":pairs},sort_keys=True))
if __name__=="__main__":main()
