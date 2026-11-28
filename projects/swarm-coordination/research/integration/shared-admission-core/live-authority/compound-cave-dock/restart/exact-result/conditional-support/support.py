#!/usr/bin/env python3
"""Derive finite return support from two actual selected warehouse histories."""
import argparse
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import numpy as np

HERE=Path(__file__).resolve().parent
OLD=(14,15)
NEW=(15,15)
def pos(a):return(a.x,a.y)
def value(p):return 1+p[0]+16*p[1]

def load(d):
    path=d/"isolated.py"
    x=path.read_bytes()
    assert hashlib.sha1(f"blob {len(x)}\0".encode()+x).hexdigest()==\
           "610a81b316a9b3538106387467c4e2f4437b28f4"
    mod=importlib.util.spec_from_file_location("native_fixture",path)
    o=importlib.util.module_from_spec(mod)
    sys.modules["native_fixture"]=o
    mod.loader.exec_module(o)
    return o,o.load_native(d/"native_source.py")

def make(iso,n,blocked):
    w=iso.make(n,False)
    w.grid_size=(16,16);w.grid=np.zeros((2,16,16),dtype=int)
    w.highways=np.zeros((16,16),dtype=bool);w.shelfs=[];w.goals=[]
    w.request_queue=[];w.max_steps=1000
    p,b=w.agents
    p.x,p.y,p.dir=0,0,n.Direction.RIGHT
    b.x,b.y=OLD;b.dir=n.Direction.RIGHT
    w._recalc_grid()
    if blocked==NEW:
        n.step(w,[n.Action.NOOP.value,n.Action.FORWARD.value])
    assert pos(b)==blocked and pos(p)==(0,0)
    return w

def successors(iso,n,blocked):
    w=make(iso,n,blocked)
    p,b=w.agents
    start=p.x,p.y,p.dir
    seen={start:None};q=deque([start]);count=0
    actions=(n.Action.LEFT,n.Action.RIGHT,n.Action.FORWARD)
    while q:
        state=q.popleft()
        for act in actions:
            p.x,p.y,p.dir=state
            w._cur_steps=w._cur_inactive_steps=0
            w._recalc_grid()
            # No alternate mover in this component; every step calls
            # the pinned native transition. Reset only P for graph search.
            n.step(w,[act.value,n.Action.NOOP.value])
            count+=1
            over=(p.x,p.y,p.dir)
            assert pos(b)==blocked and pos(p)!=blocked
            if over not in seen:
                seen[over]=(state,act)
                q.append(over)
    return seen,count

def native_witness(iso,n,block,seen,to):
    path=[]
    k=next(s for s in seen if s[:2]==to)
    while seen[k] is not None:
        k,act=seen[k];path.append(act)
    w=make(iso,n,block)
    for act in reversed(path):
        n.step(w,[act.value,n.Action.NOOP.value])
    return pos(w.agents[0]), len(path)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    a=p.parse_args()
    i,n=load(a.warehouse)
    first,steps1=successors(i,n,OLD);second,steps2=successors(i,n,NEW)
    before={value(k[:2]) for k in first}|{0}
    after={value(k[:2]) for k in second}|{0}
    assert (len(before),len(after),len(before|after),len(before&after))==(256,256,257,255)
    assert after-before=={255} and before-after=={256}
    (a,x),(b,y)=native_witness(i,n,NEW,second,OLD),native_witness(i,n,OLD,first,NEW)
    assert a==OLD and b==NEW
    # Compare both codebooks on every reachable outcome, including
    # pending; a post-change observer can choose the right pinned one.
    for support,excluded in [(before,255),(after,256)]:
        e=lambda k:k if k<excluded else k-1
        d=lambda wire:wire if wire<excluded else wire+1
        assert {e(k) for k in support}==set(range(256))
        assert all(d(e(k))==k for k in support)
    print(json.dumps(dict(stationary_support=len(before),moved_support=len(after),
        union_support=len(before|after),first_missing=min(set(range(257))-before),
        later_missing=min(set(range(257))-after),native_steps=steps1+steps2,
        newly_available_path_steps=x,old_only_path_steps=y,old_priority_decode_255=256),
        sort_keys=True))
if __name__=="__main__":main()
