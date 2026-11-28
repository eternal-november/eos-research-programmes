#!/usr/bin/env python3
"""Fixed-basis lower and upper bound for an exact query selected after retirement."""
from itertools import permutations
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import json
from math import prod
import sqlite3
import sys
import tempfile
import numpy as np
HERE=Path(__file__).resolve().parent

def cardinal(k,r):return prod(range(k-r+1,k+1))
def rank(signature,k):
    free=list(range(k));x=0
    for item in signature:
        x=x*len(free)+free.index(item)
        free.remove(item)
    return x

def unrank(x,k,r):
    digits=[]
    for base in range(k-r+1,k+1):
        x,i=divmod(x,base);digits.append(i)
    assert x==0
    free=list(range(k))
    return tuple(free.pop(i) for i in reversed(digits))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    b=a.support.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="b0e6c09b6ba593ccd373371541f0d20a0ff8a414"
    sys.path.insert(0,str(a.support.resolve().parent));import support
    iso,n=support.load(a.warehouse)
    w=iso.make(n,False);w.shelfs=[];w.goals=[];w.request_queue=[]
    n.Agent.counter=0
    w.grid_size=(8,8);w.grid=np.zeros((2,8,8),dtype=int);w.highways=np.zeros((8,8),dtype=bool)
    w.agents=[n.Agent(1,i,n.Direction.RIGHT,0) for i in range(7)];w.n_agents=7
    w._recalc_grid()
    rows=[]
    for i in range(7):
        cmds=[n.Action.NOOP.value]*7;cmds[i]=n.Action.FORWARD.value
        n.step(w,cmds)
        x,y=support.pos(w.agents[i]);assert (x,y)==(2,i)
        rows.append((i+1,i,x,y))
    counts=Counter();ex={}
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)
        server=sqlite3.connect(path/"producer")
        receiver=sqlite3.connect(path/"recipient")
        server.execute("create table assoc(key integer primary key, ordinal integer unique)")
        receiver.execute("create table motion(row integer primary key,value text)")
        receiver.executemany("insert into motion values (?,?)",
                             [(i,json.dumps(row)) for i,row in enumerate(rows)])
        receiver.commit();receiver.close()
        receiver=sqlite3.connect(path/"recipient")
        distinct={r:set() for r in (1,3,4,6)}
        colliding=None
        # All keys have individually been acknowledged. The permitted
        # audit query is supplied only after this encoding.
        for pairing in permutations(range(6)):
            with server:
                server.execute("delete from assoc")
                server.executemany("insert into assoc values (?,?)",enumerate(pairing))
            for r in (1,3,4,6):
                authoritative=tuple(v for (v,) in server.execute(
                    "select ordinal from assoc where key < ? order by key",(r,)))
                x=rank(authoritative,6)
                assert 0<=x<cardinal(6,r)
                decoded=unrank(x,6,r)
                assert decoded==authoritative
                distinct[r].add(x)
                for q in range(r):
                    val=receiver.execute("select value from motion where row=?",(decoded[q],)).fetchone()
                    assert tuple(json.loads(val[0]))==rows[pairing[q]]
                    counts[r]+=1
                assert tuple(json.loads(receiver.execute("select value from motion where row=6").fetchone()[0]))==rows[6]
                if r==4 and x==256:
                    colliding=decoded
        assert colliding is not None and colliding!=unrank(0,6,4)
        for r,s in distinct.items():
            assert s==set(range(cardinal(6,r)))
            ex[str(r)]=[len(s),counts[r],(len(s)-1).bit_length()]
        server.close();receiver.close()
    print(json.dumps({"assignments":720,"native_rows":len(rows),"columns":["classes","exact_queries","minimum_fixed_bits"],"scope":ex,
        "truncated_octet_collision":[unrank(0,6,4),colliding]},sort_keys=True))
if __name__=="__main__":main()
