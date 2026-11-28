#!/usr/bin/env python3
"""Finite joint-cut causal-policy synthesis with native transition witnesses."""
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

def plant(support,iso,n):
    w=iso.make(n,False);w.shelfs=[];w.goals=[];w.request_queue=[]
    n.Agent.counter=0
    w.agents=([n.Agent(1,y,n.Direction.RIGHT,0) for y in (1,2,3)]
        +[n.Agent(3,y,n.Direction.LEFT,0) for y in (1,2,3)]
        +[n.Agent(4,4,n.Direction.LEFT,0)])
    w.n_agents=7;w.grid=np.zeros((2,5,5),dtype=int);w._recalc_grid()
    def step(who):
        a=n.Action
        cmd=[a.NOOP.value]*7;cmd[who]=a.FORWARD.value
        n.step(w,cmd)
    step(6)
    assert support.pos(w.agents[6])==(3,4)
    def available(k):return int(w.grid[0,k+1,2])==0
    def move(k):
        assert available(k)
        step(k)
        assert support.pos(w.agents[k])==(2,k+1)
    return available,step,move

A=frozenset(range(3))
def joint(rows):
    policies={}
    for r in range(2):
        rs=[entry[r] for entry in rows.values()]
        if not all(x[0] for x in rs):continue
        cells={}
        for _,view,good in rs:cells[view]=cells.get(view,A)&good
        if all(cells.values()):policies[r]={view:min(good) for view,good in cells.items()}
    return policies

def direct(rows):
    out=[]
    for r in range(2):
        for acts in product(range(3),repeat=3):
            if all(entry[r][0] and acts[entry[r][1]] in entry[r][2] for entry in rows.values()):
                out.append(r);break
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
        setup.read(root/"staged_replay.inc");shutil.copyfile(HERE/"joint_cut.cc",root/"joint_cut.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","joint_cut.cc","-o","joint-cut"],cwd=root,check=True)
        with sp.Popen([root/"joint-cut"],cwd=root,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):
                proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            def replay(block,side,cap,probe,traffic,fresh,route,policy):
                nonlocal counts
                counts+=1
                avail,step,move=plant(support,iso,n)
                if fresh:step(3+block)
                emit(side,cap,probe,traffic,fresh)
                assert proc.stdout.readline().strip()=="E"
                emit(route)
                observed=None
                while True:
                    line=proc.stdout.readline().split();assert line
                    if line[0]=="S":
                        assert int(line[1])==route
                        # This bit is a real read of one native site, not a
                        # label looked up by the policy from the eventual world.
                        emit(int(not avail(0)))
                    elif line[0]=="L":
                        assert int(line[1])==route
                        observed=int(line[2])
                        if not fresh:step(3+block)
                        assert [k for k in A if not avail(k)]==[block]
                        candidate=policy.get(observed,3)
                        if candidate in A and avail(candidate):
                            move(candidate);emit(candidate)
                        else:emit(3)
                    else:
                        assert line[0]=="O";break
                sidework,diagnostic,arrived,effect,reply,tx=map(int,line[1:])
                assert sidework==traffic and effect==reply and tx==4*int(route>=0)
                return arrived,observed,reply,diagnostic
            cases=[
              ("blank",2,4,0,0,1),
              ("read-costs-last-byte",2,4,3,0,1),
              ("fresh-bit",2,5,3,0,1),
              ("stale-bit",2,5,3,0,0),
              ("mixed-docks",0,5,1,1,1),
              ("shadow-read",0,5,3,1,1),
              ("both-fit",0,9,3,1,1),
            ]
            for name,*args in cases:
                rows={};diagnostics={}
                for b in A:
                    rows[b]={}
                    for r in range(2):
                        good=set()
                        for a in A:
                            arrived,view,ok,seen=replay(b,*args,r,{o:a for o in range(3)})
                            assert view is None or view in range(3)
                            if ok:good.add(a)
                        rows[b][r]=(arrived,view,frozenset(good))
                        diagnostics[b,r]=seen
                plans=joint(rows)
                assert list(plans)==direct(rows)
                pairs={f"{x},{y}":direct({k:rows[k] for k in (x,y)})
                       for x,y in ((0,1),(0,2),(1,2))}
                if plans:
                    for r,acts in plans.items():
                        for b in A:assert replay(b,*args,r,acts)[2]
                else:
                    for b in A:assert not replay(b,*args,-1,{})[2]
                for pair,routes in pairs.items():
                    pair_worlds=[int(x) for x in pair.split(",")]
                    pair_policy=joint({k:rows[k] for k in pair_worlds})
                    assert list(pair_policy)==routes
                    if name=="blank":
                        for route,acts in pair_policy.items():
                            for b in pair_worlds:assert replay(b,*args,route,acts)[2]
                results[name]=dict(routes=list(plans),pair_routes=pairs,
                    witness=plans,rows={str(b):[[p,q,sorted(g)] for p,q,g in v.values()]
                                         for b,v in rows.items()},
                    accepted_diagnostics=sum(diagnostics.values()))
            proc.stdin.close();assert proc.wait()==0
    expect={"blank":[],"read-costs-last-byte":[],"fresh-bit":[0,1],
            "stale-bit":[],"mixed-docks":[],"shadow-read":[1],"both-fit":[0,1]}
    assert {k:v["routes"] for k,v in results.items()}==expect, results
    assert list(results["blank"]["pair_routes"].values())==[[0,1]]*3
    assert results["read-costs-last-byte"]["accepted_diagnostics"]==6
    assert results["fresh-bit"]["witness"]=={0:{1:1,0:0},1:{1:1,0:0}}
    print(json.dumps(dict(native_replays=counts,results=results),sort_keys=True))
if __name__=="__main__":main()
