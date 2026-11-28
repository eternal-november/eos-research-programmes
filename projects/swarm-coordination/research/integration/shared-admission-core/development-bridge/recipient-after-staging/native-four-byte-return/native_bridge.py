#!/usr/bin/env python3
"""Native masked preparation and post-arrival receiver selection."""
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import shutil
import sqlite3
import subprocess as sp
import sys
import tempfile
import numpy as np

HERE=Path(__file__).resolve().parent
def ancestor(name):
    return next(p for p in (HERE,*HERE.parents) if (p/name).is_file())
def pin(path,digest):
    b=path.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==digest
PIN="6b2881248f3f09b6bfe2a45161500d486773728c"
def codeword(lane,payload,compact):
    assert lane in (0,1) and len(payload)==4
    if not compact:
        return bytes([lane,*payload])
    return bytes([payload[0]|(lane<<7),*payload[1:]]) if payload[0]<128 else None

def decode(wire,compact):
    if compact:
        assert len(wire)==4
        return wire[0]>>7,[wire[0]&127,*wire[1:]]
    assert len(wire)==5 and wire[0] in (0,1)
    return wire[0],list(wire[1:])

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--delay", choices=("none","equal","past"), default="none")
    a.add_argument("--compact", action="store_true")
    a.add_argument("--source",type=Path,default=HERE/"source")
    a.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    a.add_argument("--support",type=Path,default=HERE/"support.py")
    a.add_argument("--journal",type=Path,default=HERE/"motion_journal.py")
    a.add_argument("--model",type=Path,default=ancestor("development.js")/"development.js" if (HERE/"development.js").exists() or (HERE.parent/"development.js").exists() else None)
    args=a.parse_args()
    compact=args.compact
    delay={"none":0,"equal":1,"past":2}[args.delay]
    assert not (delay and compact)
    pin(args.journal,"19447b46bd35310370ddd386ed2c29b3a60f60b5")
    pin(args.model,PIN)
    sys.path[:0]=[str(ancestor("replay_effect_cut.py")),str(args.journal.resolve().parent),str(args.support.resolve().parent)]
    import replay_effect_cut as setup
    setup.read(args.support)
    import support,motion_journal as j
    iso,n=support.load(args.warehouse)
    class Plant(j.Plant):
        def start(self):
            w=super().start()
            N=self.n
            w.grid_size=(8,8);w.highways=np.zeros((8,8),dtype=bool);w.grid=np.zeros((2,8,8),dtype=int)
            N.Agent.counter=0
            w.agents=[N.Agent(1,y,N.Direction.RIGHT,0) for y in range(1,6)]+[
              N.Agent(3,y,N.Direction.LEFT,0) for y in range(3,6)]+[N.Agent(4,6,N.Direction.LEFT,0)]
            w.n_agents=len(w.agents);w._recalc_grid()
            return w
        def step(self,w,actor):
            commands=[n.Action.NOOP.value]*w.n_agents
            commands[actor]=n.Action.FORWARD.value
            n.step(w,commands)
            x,y=support.pos(w.agents[actor])
            return w._cur_steps,actor,x,y
    plant=Plant(iso,n)
    def busy0(w):
        return bool(w.grid[0,3,2])
    def basis(db):
        return [json.loads(row) for (row,) in db.execute("select result from motion where tick<=2 order by tick")]
    with tempfile.TemporaryDirectory() as tmp:
        wd=Path(tmp)
        for f in args.source.iterdir():
            if f.is_file():shutil.copyfile(f,wd/f.name)
        for s in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):setup.read(wd/s)
        for s in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",s],cwd=wd,check=True)
        setup.read(wd/"staged_replay.inc")
        shutil.copyfile(HERE/"native_bridge.cc",wd/"native_bridge.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","native_bridge.cc","-o","bridge"],cwd=wd,check=True)
        # Same raw movement prefix in two durable journals, distinct old key binding.
        for h in (0,1):
            donor=j.connect(wd/f"source{h}.db")
            for actor in (0,1):
                assert j.apply(donor,plant,j.OLD if actor==h else j.SAME_PHYSICAL_UNRELATED,actor)[0]=="new"
            donor.close()
        def donor(h):
            return j.connect(wd/f"source{h}.db")
        dbs=[donor(h) for h in (0,1)]
        assert basis(dbs[0])==basis(dbs[1])
        assert j.resolved(dbs[0],j.OLD)!=j.resolved(dbs[1],j.OLD)
        # Put the shared native rows at both possible successors; force close/reopen.
        # No donor key or result association is copied.
        for d in (0,1):
            bx=j.connect(wd/f"basis{d}.db")
            bx.executemany("insert into motion values (?,?,?)",dbs[0].execute("select * from motion"))
            bx.close()
        replacing=[j.connect(wd/f"basis{d}.db") for d in (0,1)]
        assert all(j.resolved(db,j.OLD) is None for db in replacing)
        # Exhaustive check on the only altered byte; other bytes pass unchanged.
        assert len({codeword(l,[t,0,255,127],True) for l,t in product(range(2),range(128))})==256
        assert all(decode(codeword(l,[t,0,255,127],True),True)==(l,[t,0,255,127]) for l,t in product(range(2),range(128)))
        assert all(codeword(l,[t,0,255,127],True) is None for l,t in product(range(2),range(128,256)))
        native=0
        with sp.Popen([wd/"bridge"],cwd=wd,stdin=sp.PIPE,stdout=sp.PIPE,text=True,bufsize=1) as p:
            def emit(*xs):
                p.stdin.write(" ".join(map(str,xs))+"\n");p.stdin.flush()
            def replay(w,s,mask,choose):
                nonlocal native
                native+=1
                side,h,blocked=w
                cap,hint,measure=s
                db=sqlite3.connect(":memory:",isolation_level=None)
                replacing[0].backup(db)
                old=j.resolved(dbs[h],j.OLD)
                assert old is not None and len(old)==4
                assert j.apply(db,plant,None,8)==("new",[3,8,3,6])
                assert not busy0(plant.native(db))
                assert j.apply(db,plant,None,5+blocked)==("new",[4,5+blocked,2,3+blocked])
                assert busy0(plant.native(db))==(blocked==0)
                sample=int(busy0(plant.native(db))) if measure==2 else 0 if measure==1 else -1
                emit(cap,side,mask,hint,sample,bytes(old).hex(),delay)
                z=p.stdout.readline().split()
                assert z[0]=="C";view=[int(z[1])]
                assert view==[side if hint else -1]
                dock=choose(view)
                emit(dock if dock is not None else -1)
                reply=b""; effected=False
                while True:
                    z=p.stdout.readline().split()
                    if z[0]=="O":break
                    assert z[0]=="L"
                    bit=int(z[1]);payload=[] if z[2]=="-" else list(bytes.fromhex(z[2]))
                    # Actual next operation reads only the callback's bits and
                    # its own immediate guard. Read-only disclosure is preauthorized.
                    candidate=codeword(bit,payload,compact) if bit in (0,1) and len(payload)==4 else None
                    if measure==2 and candidate is not None and payload in basis(db):
                        move=bit
                        if not plant.native(db).grid[0,3+move,2]:
                            assert j.apply(db,plant,None,2+move)==("new",[5,2+move,2,3+move])
                            reply=candidate;effected=True
                    emit(reply.hex() or "-")
                assert int(z[1])==1 and int(z[5])==0 and int(z[6])==view[0]
                if effected:
                    assert int(z[2])==1
                    if cap==5 and hint==1 and not compact and delay!=2:
                        # Incoming notice is still live at Q. The source
                        # checks received debit using each sender's cap.
                        assert z[3]=="-" and int(z[4])==1
                    else:
                        assert z[3]==reply.hex() and int(z[4])==len(reply)+int(hint==1 and delay!=2)
                assert j.resolved(db,j.OLD) is None
                actual=plant.native(db)
                assert actual._cur_steps==4+int(effected)
                assert support.pos(actual.agents[8])==(3,6)
                returned=bytes.fromhex(z[3]) if z[3]!="-" else b""
                accepted=bool(returned and decode(returned,compact)==(1-blocked,old))
                # 'blocked' enumerates which lane is obstructed; the bit
                # published is whether lane zero is obstructed.
                db.close()
                return view,accepted
            worlds=list(product(range(2),range(2),range(2)))
            plans=list(range(4))
            actions=[0,1]
            result={}
            for cap,hint,measure in product((4,5,6,8,9),range(3),range(3)):
                scope=cap,hint,measure
                matrix=[]
                for w in worlds:
                    opts=[]
                    for mask in plans:
                        a=[replay(w,scope,mask,lambda _,d=d:d) for d in actions]
                        assert a[0][0]==a[1][0]
                        opts.append(dict(view=a[0][0],winners=[d for d,(_,ok) in zip(actions,a) if ok]))
                    matrix.append(opts)
                req=json.dumps(dict(worlds=matrix,plans=plans,actions=actions))
                checked=json.loads(sp.check_output(["node",str(HERE/"native_policy.js"),str(args.model.resolve()),PIN],input=req,text=True))
                want=[] if measure!=2 or cap<5 or (cap==5 and hint==1 and not compact and delay!=2) else [1,2,3] if cap>=9 else [3] if hint else []
                assert [index for index,_ in checked]==want,(scope,checked)
                for i,table in checked:
                    assert all(replay(w,scope,i,lambda v:next(d for vv,d in table if v==vv))[1] for w in worlds)
                if not checked:
                    assert all(not replay(w,scope,0,lambda _:None)[1] for w in worlds)
                result[f"{cap}/{int(hint)}/{measure}"]=checked
            p.stdin.close();assert p.wait()==0
    print(json.dumps(dict(runs=native,result=result),sort_keys=True))
if __name__=="__main__":main()
