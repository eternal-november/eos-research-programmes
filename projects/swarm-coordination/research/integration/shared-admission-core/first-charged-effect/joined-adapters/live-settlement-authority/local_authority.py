#!/usr/bin/env python3
"""Native grant delivery, rolling radio debit and downstream movement."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess as sp
import sys
import tempfile
import numpy as np

HERE=Path(__file__).resolve().parent
def parent(name):
    return next(x for x in (HERE,*HERE.parents) if (x/name).is_file())
P=parent("replay_effect_cut.py")
sys.path.insert(0,str(P))
import replay_effect_cut as setup

def pinned(p,digest):
    b=p.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==digest
    return b

def plant(support,iso,n,initial,after,block):
    w=iso.make(n,False)
    w.shelfs=[];w.goals=[];w.request_queue=[]
    n.Agent.counter=0
    w.agents=[
        n.Agent(2,initial+1,n.Direction.DOWN if initial==0 else n.Direction.UP,0),
        n.Agent(1,1,n.Direction.RIGHT,0),n.Agent(1,2,n.Direction.RIGHT,0),
        n.Agent(4,4,n.Direction.LEFT,0),
        n.Agent(3,1,n.Direction.LEFT,0),n.Agent(3,2,n.Direction.LEFT,0)]
    w.n_agents=6;w.grid=np.zeros((2,5,5),dtype=int);w._recalc_grid()
    a=n.Action
    def step(idx,kind=a.FORWARD):
        actions=[a.NOOP.value]*6
        if idx>=0:actions[idx]=kind.value
        n.step(w,actions)
    def free(k):return int(w.grid[0,k+1,2])==0
    def first():
        step(3)
        if after==3:
            step(0,a.LEFT);step(0,a.LEFT);step(0)
        elif after==2:step(5-initial)
        else:step(0 if initial!=after else -1)
        assert support.pos(w.agents[3])==(3,4)
        assert [free(k) for k in (0,1)]==[after==3 or k==1-after for k in (0,1)]
        # Declared lease policy: retain the previous physical route if it
        # remains clear; otherwise transfer to the other open route.
        return next((k for k in (1-initial,initial) if free(k)),2)
    def second():
        if block<2:step(4+block)
        if block==3 and w.agents[0].y in (1,2):
            prior_y=w.agents[0].y
            away=n.Direction.UP if prior_y==1 else n.Direction.DOWN
            if w.agents[0].dir!=away:step(0,a.LEFT);step(0,a.LEFT)
            assert w.agents[0].dir==away
            step(0)
            assert w.agents[0].y==(0 if prior_y==1 else 3)
    def move(k):
        step(k+1)
        return int(support.pos(w.agents[k+1])==(2,k+1))
    return first,second,free,move

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    setup.read(a.support)
    sys.path.insert(0,str(a.support.resolve().parent));import support
    iso,n=support.load(a.warehouse)
    sums=Counter();res={};witness={};pair={}
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (w/name).write_bytes(setup.read(a.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/name,w/name)
        for name in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",name],cwd=w,check=True)
        setup.read(w/"staged_replay.inc")
        (w/"first_effect.hpp").write_bytes(pinned(P/"first_effect.hpp","1e1624f0de957d627ea57182d94dbbb28d06c8a4"))
        shutil.copyfile(HERE/"local_authority.cc",w/"local_authority.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","local_authority.cc","-o","lease"],cwd=w,check=True)
        with sp.Popen([w/"lease"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for old,first,block,late,mode,cap,edge,arm in product(range(2),range(4),range(4),range(4),range(3),(4,5),range(2),range(4)):
                first_step,second_step,free,move=plant(support,iso,n,old,first,block)
                emit(old,late,mode,cap,edge,arm)
                actual=[]
                while True:
                    row=proc.stdout.readline().split();assert row
                    if row[0]=="P":
                        owner=first_step();emit(owner)
                    elif row[0]=="L":
                        second_step()
                        visible=[free(k) for k in (0,1)]
                        emit(1)
                    elif row[0]=="I":emit(int(free(int(row[1]))))
                    elif row[0]=="M":
                        k=int(row[1]);actual.append(k);emit(move(k))
                    else:
                        assert row[0]=="O";break
                out=list(map(int,row[1:]))
                expected_owner=(1-old if first==3 else 1-first if first<2 else 2)
                assert owner==expected_owner
                packet=owner<2 and mode!=1
                valid=packet and mode==0
                open_now={k for k in (0,1) if (first==3 or k==1-first) and block!=k}
                if block==3:open_now=({old} if first==2 else {0,1})
                assert visible==[k in open_now for k in (0,1)]
                if old==0 and first<2 and block==3 and late==3 and mode==0 and cap==5 and edge==0 and arm==0:
                    pair[first]={"prior_owner":1-old,"local_open":visible,"actual_holder":owner,"executed":actual}
                    assert open_now=={0,1} and actual==[owner]
                radio={k for k in (0,1) if 4+4*int(late==k or late==2)+int(packet and owner==k and not edge)<=cap}
                entitled={owner} if valid else set()
                if arm<2:possible=radio&open_now&entitled
                elif arm==2:possible=radio&open_now&{1-old}
                else:possible=radio&entitled
                chosen=min(possible,default=-1)
                go=chosen in entitled
                settled=go and chosen in open_now
                assert actual==([chosen] if go else [])
                expect=[int(settled),int(packet),int(chosen!=-1 and not go),int(go),3 if late==2 else 2,4*int(chosen!=-1)]
                assert out==expect,(old,first,block,late,mode,cap,edge,arm,out,expect)
                if arm<2:assert not out[2] and out[0]==out[3]
                sums[f"settled/{arm}"]+=out[0];sums[f"refused_at_actuator/{arm}"]+=out[2];sums[f"failed_motion/{arm}"]+=out[3]-out[0]
                sums[f"cases/{arm}"]+=1;res[(old,first,block,late,mode,cap,edge,arm)]=out
                example=(old==0 and first==1 and late==3 and block==2)
                if example: witness[str((mode,cap,edge,arm))]=out
            proc.stdin.close();assert proc.wait()==0
    for k,r in res.items():
        if k[-1]==0:assert r==res[k[:-1]+(1,)]
    assert pair[0]["local_open"]==pair[1]["local_open"]==[True,True] and pair[0]["executed"]!=pair[1]["executed"]
    print(json.dumps({"same_occupancy_pair":pair,"counts":dict(sums),"columns":["settled","received_grant_frame","fence_refusal","motion_calls","independent_reports","request_bytes"],"witness":witness},sort_keys=True))
if __name__=="__main__":main()
