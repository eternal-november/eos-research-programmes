#!/usr/bin/env python3
"""Joined native source fixture, with a synchronous local adapter in each arm."""
import argparse
from itertools import product
import hashlib
import json
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


def plant(support,iso,n,before,after):
    w=iso.make(n,False)
    w.shelfs=[];w.goals=[];w.request_queue=[]
    w.n_agents=6
    n.Agent.counter=0
    q,a,b,u,late_a,late_b=(
        n.Agent(2,before+1,n.Direction.DOWN if before==0 else n.Direction.UP,0),
        n.Agent(1,1,n.Direction.RIGHT,0),n.Agent(1,2,n.Direction.RIGHT,0),
        n.Agent(4,4,n.Direction.LEFT,0),
        n.Agent(3,1,n.Direction.LEFT,0),n.Agent(3,2,n.Direction.LEFT,0))
    w.agents=[q,a,b,u,late_a,late_b];w.grid=np.zeros((2,5,5),dtype=int);w._recalc_grid()
    s=n.Action
    def step(idx,act=s.FORWARD):
        actions=[s.NOOP.value]*6
        if idx>=0:actions[idx]=act.value
        n.step(w,actions)
    def stage():
        step(3)
        assert support.pos(u)==(3,4)
        if after==3:
            step(0,s.LEFT);step(0,s.LEFT);step(0)
            assert support.pos(q)==(2,3*before)
        else:
            step(5-before if after==2 else 0 if before!=after else -1)
        for i in range(2):
            assert free(i)==(after==3 or i==1-after)
    def free(i):return int(w.grid[0,i+1,2])==0
    def effect(i,unheld):
        if unheld:
            assert free(i)
            step(4+i)
            assert not free(i)
        step(i+1)
        return int(support.pos(w.agents[i+1])==(2,i+1))
    return stage,free,effect

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
        shutil.copyfile(HERE/"joined_effect.cc",w/"joined_effect.cc")
        (w/"first_effect.hpp").write_bytes(pin(PARENT/"first_effect.hpp","1e1624f0de957d627ea57182d94dbbb28d06c8a4"))
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","joined_effect.cc","-o","join"],cwd=w,check=True)
        iso,n=support.load(args.warehouse)
        runs=Counter()
        examples={}
        paid={}
        with sp.Popen([w/"join"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as p:
            def emit(*a):p.stdin.write(" ".join(map(str,a))+"\n");p.stdin.flush()
            for rb,ra,wb,wa,arm,edge in product(range(2),range(4),range(2),range(4),range(6),range(2)):
                stage,free,effect=plant(support,iso,n,wb,wa)
                emit(rb,ra,arm,edge)
                committed=[];seen=[]
                while True:
                    line=p.stdout.readline().split()
                    assert line
                    if line[0]=="P":stage();emit(1)
                    elif line[0]=="I":
                        k=int(line[1]);seen.append(k);emit(int(free(k)))
                    elif line[0]=="M":
                        k=int(line[1]);committed.append(k);emit(effect(k,arm==5))
                    else:
                        assert line[0]=="O";break
                old,rx,side,tx,nread=map(int,line[1:])
                rad=set(range(2))-({0,1} if ra==2 else set() if ra==3 else {ra})-({rb} if edge else set())
                phys={1-wa} if wa<2 else {0,1} if wa==3 else set()
                admiss=rad & phys
                candidates=[admiss,rad,phys,admiss,{1-rb},admiss][arm]
                k=min(candidates,default=-1)
                assert (old,rx,side,tx,nread)==(
                    int(k in admiss and arm!=5),int(k in rad),3 if ra==2 else 2,
                    0 if k<0 else 4,len(seen)), (rb,ra,wb,wa,arm,edge,line)
                assert len(committed)==rx and len(seen)<=2
                runs[f"paid/{arm}"]+=old
                runs[f"charged_without_settlement/{arm}"]+=int(not old and tx>0)
                paid[(rb,ra,wb,wa,arm,edge)]=old
                if (rb,wb,edge)==(0,0,0) and ((ra<2 and wa<2) or (ra,wa) in {(0,3),(3,0),(3,3)}):
                    examples[str((ra,wa,arm))]=[old,rx,tx]
            p.stdin.close();assert p.wait()==0
        for rb,ra,wb,wa,edge in product(range(2),range(4),range(2),range(4),range(2)):
            assert paid[(rb,ra,wb,wa,0,edge)]==paid[(rb,ra,wb,wa,3,edge)]
    print(json.dumps({"cases":len(paid),"results":dict(runs),"columns":["settled","rx","spent"],"examples":examples},sort_keys=True))
if __name__=="__main__":main()
