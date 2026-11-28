#!/usr/bin/env python3
"""Finite two-cut causal-policy synthesis with native transition witnesses."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import argparse
import json
import shutil
import subprocess as sp
import sys
import tempfile
import numpy as np

HERE=Path(__file__).resolve().parent
P=next(x for x in (HERE,*HERE.parents) if (x/"replay_effect_cut.py").is_file())
sys.path.insert(0,str(P));import replay_effect_cut as setup

def plant(support,iso,n,blocked):
    w=iso.make(n,False);w.shelfs=[];w.goals=[];w.request_queue=[]
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
    def site():return [int(w.grid[0,i+1,2])==0 for i in (0,1)]
    assert site()==[True,True]
    def admit():
        step(2+blocked)
        x=site()
        assert sum(x)==1
        return x.index(True)
    def run(actor):
        assert site()[actor]
        step(actor)
        assert support.pos(w.agents[actor])==(2,actor+1)
    return admit,run

def intersections(rows):
    early=sorted({e for _,_,e in rows})
    out=[]
    for rc in product((0,1),repeat=len(early)):
        plan=dict(zip(early,rc))
        cells={};viable=True
        for world,rs in rows.items():
            r=plan[world[2]];o=rs[r]
            if not o["arrived"]:
                viable=False;break
            key=(r,o["view"])
            if key not in cells:cells[key]={0,1}
            cells[key]&=o["good"]
        if viable and all(cells.values()):
            out.append((plan,{key:min(allowed) for key,allowed in cells.items()}))
    return out

def direct(rows):
    early=sorted({e for _,_,e in rows})
    keys=list(product((0,1),(0,1,2)))
    out=[]
    for rc in product((0,1),repeat=len(early)):
        plan=dict(zip(early,rc))
        for ac in product((0,1),repeat=len(keys)):
            act=dict(zip(keys,ac))
            if all(rs[plan[e]]["arrived"] and
                   act[plan[e],rs[plan[e]]["view"]] in rs[plan[e]]["good"]
                   for (*_,e),rs in rows.items()):
                out.append(rc);break
    return out

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    setup.read(a.support);sys.path.insert(0,str(a.support.resolve().parent));import support
    iso,n=support.load(a.warehouse)
    counts=0;results={}
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (root/name).write_bytes(setup.read(a.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/name,root/name)
        for name in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",name],cwd=root,check=True)
        setup.read(root/"staged_replay.inc");shutil.copyfile(HERE/"two_cut.cc",root/"two_cut.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","two_cut.cc","-o","two-cut"],cwd=root,check=True)
        with sp.Popen([root/"two-cut"],cwd=root,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            def replay(world,plan,reveal,policy):
                nonlocal counts
                counts+=1
                b,side,e=world;first,move=plant(support,iso,n,b)
                emit(side,e)
                obs=None
                while True:
                    row=proc.stdout.readline().split();assert row
                    if row[0]=="E":
                        got=int(row[1]);assert got==e
                        r=plan[got];emit(r)
                    elif row[0]=="L":
                        dock=int(row[1]);assert dock==r
                        actor=first()
                        obs=actor if reveal[dock] else 2
                        a=policy.get((dock,obs),2)
                        if a==actor:move(a);emit(a)
                        else:emit(2)
                    else:
                        assert row[0]=="O";break
                done,arrived,effects,reply,tx=map(int,row[1:])
                assert done==1 and arrived==int(r>=0 and r!=side)
                assert effects==reply and tx==4*int(r>=0)
                return bool(arrived),obs,bool(reply)
            # Paired histories and observation functions are fixed before
            # enumeration. Receiver observations are granted per route.
            for name,worlds,reveal in [
              ("common-dock",[(0,0,2),(1,0,2)],(True,True)),
              ("erased-actor",[(0,2,2),(1,2,2)],(False,False)),
              ("split-reachability",[(0,0,2),(1,1,2)],(True,True)),
              ("shadow-receiver",[(0,2,2),(1,2,2)],(False,True)),
              ("early-label-merged",[(0,0,0),(1,0,1)],(False,False)),
              ("route-as-signal",[(0,2,0),(1,2,1)],(False,False)),
            ]:
                rows={}
                for world in worlds:
                    rows[world]={}
                    for route in (0,1):
                        good=set()
                        for a in (0,1):
                            arrived,obs,replied=replay(world,{0:route,1:route,2:route},reveal,{(route,o):a for o in (0,1,2)})
                            if replied:good.add(a)
                        rows[world][route]={"arrived":arrived,"view":obs,"good":good}
                policies=intersections(rows)
                assert [tuple(s[k] for k in sorted(s)) for s,_ in policies]==direct(rows)
                oracle=all(any(r["good"] for r in v.values()) for v in rows.values())
                assert oracle
                if policies:
                    plan,act=policies[0]
                    for world in worlds:
                        assert replay(world,plan,reveal,act)[2]
                else:
                    for world in worlds:assert not replay(world,{0:-1,1:-1,2:-1},reveal,{})[2]
                results[name]={"clairvoyant_worlds_all":oracle,
                    "locally_valid_sender_maps":[p for p,_ in policies],
                    "example":{str(key):v for key,v in policies[0][1].items()} if policies else {}}
            proc.stdin.close();assert proc.wait()==0
    assert results["common-dock"]["locally_valid_sender_maps"]==results["shadow-receiver"]["locally_valid_sender_maps"]==[{2:1}]
    assert not any(results[k]["locally_valid_sender_maps"] for k in ("erased-actor","split-reachability","early-label-merged"))
    assert results["route-as-signal"]["locally_valid_sender_maps"]==[{0:0,1:1},{0:1,1:0}]
    print(json.dumps({"native_replays":counts,"results":results},sort_keys=True))
if __name__=="__main__":main()
