#!/usr/bin/env python3
"""Development conformance replay. Bound native methods, authored clock and authority."""
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
def main():
    a=argparse.ArgumentParser()
    a.add_argument("--source",type=Path,default=HERE/"source")
    a.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    a.add_argument("--support",type=Path,default=HERE/"support.py")
    a.add_argument("--journal",type=Path,default=HERE/"motion_journal.py")
    a.add_argument("--model",type=Path,default=ancestor("development.js")/"development.js" if (HERE/"development.js").exists() or (HERE.parent/"development.js").exists() else None)
    a.add_argument("--expected-model",type=Path,default=ancestor("EXPECTED.json")/"EXPECTED.json")
    args=a.parse_args()
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
        native=0
        with sp.Popen([wd/"bridge"],cwd=wd,stdin=sp.PIPE,stdout=sp.PIPE,text=True,bufsize=1) as p:
            def emit(*xs):
                p.stdin.write(" ".join(map(str,xs))+"\n");p.stdin.flush()
            def replay(w,s,plan,decide):
                nonlocal native
                native+=1
                blocked,h,outage=w
                cap,side,near,grant,stale,no_early,no_loss=s
                d,probe,fmt,stage=plan
                bx=replacing[max(d,0)]
                db=sqlite3.connect(":memory:",isolation_level=None)
                bx.backup(db)
                old=j.resolved(dbs[h],j.OLD)
                assert old is not None and len(old)==4
                k=basis(db).index(old)
                wire=bytes([2*k+int(stale)]) if fmt=="ordinal" else bytes(old) if fmt=="full" else b""
                # ASCII digits used only by independent occupancy source.
                def hexword(v):return v.hex() if v else "-"
                assert j.apply(db,plant,None,8)==("new",[3,8,3,6])
                before=busy0(plant.native(db))
                assert not before
                assert j.apply(db,plant,None,5+blocked)==("new",[4,5+blocked,2,3+blocked])
                after=busy0(plant.native(db))
                assert after==(blocked==0)
                bit=(int(after) if probe=="fresh" else int(before)) if probe!="none" and (d==1 or near) else -1
                emit(cap,side,d,bit,int(probe=="fresh"),int(outage),hexword(wire) if stage=="early" else "-",
                    hexword(wire) if stage=="late" else "-")
                view=None;act=None;out=b""
                while True:
                    line=p.stdout.readline().split();assert line
                    if line[0]=="L":
                        sample=int(line[1]);payload=b"" if line[2]=="-" else bytes.fromhex(line[2])
                        view=[d,sample,grant,payload.hex()]
                        desired=decide(view)
                        if desired is not None:
                            move,key=desired
                            # Both concrete guards are applied before a native move.
                            # This callback is serialized and its plant is journal-owned.
                            row=None
                            if grant and len(payload)==1 and payload[0] in (0,2):
                                row=basis(db)[payload[0]//2]
                            if grant and len(payload)==4:
                                permissible=basis(db)
                                if list(payload) in permissible:row=list(payload)
                            plant_view=plant.native(db)
                            if row is not None and row==basis(db)[key] and not plant_view.grid[0,3+move,2]:
                                assert j.apply(db,plant,None,2+move)==("new",[5,2+move,2,3+move])
                                act=move
                                out=bytes([move,*row])
                        emit(hexword(out))
                    else:
                        assert line[0]=="O";break
                independent,arrived,reply,qt,pt,active,traffic=line[1:]
                assert int(independent)==1 and int(arrived)==int(view is not None)
                assert int(qt)==4*int(d>=0)
                assert j.resolved(db,j.OLD) is None
                native_state=plant.native(db)
                assert native_state._cur_steps==4+int(act is not None)
                assert support.pos(native_state.agents[8])==(3,6)
                result=bool(out and reply==out.hex() and list(out[1:])==old)
                db.close()
                return view,result,int(active),int(traffic)
            actions=[(m,h) for m in range(3) for h in (0,1)]
            regimes={
              "five-early":(5,2,True,True,False,False,False),
              "five-late-only":(5,2,True,True,False,True,True),
              "six-late-only":(6,2,True,True,False,True,True),
              "occupied-dock":(5,0,True,True,False,False,False),
              "lost-diagnostic-peer":(5,1,False,True,False,False,False),
              "no-authority":(5,2,True,False,False,False,False),
              "stale-ordinal":(5,2,True,True,True,False,False),
              "source-loss-late-only":(9,2,True,True,False,True,False),
            }
            result={}
            for name,s in regimes.items():
                worlds=list(product(range(3),range(2),(False,) if s[6] else (False,True)))
                plans=[(d,probe,fmt,stage) for d,probe in product((0,1),("none","stale","fresh"))
                       for fmt in ("none","ordinal","full")
                       for stage in (("none",) if fmt=="none" else ("late",) if s[5] else ("early","late"))]
                rows=[]
                for w in worlds:
                    row=[]
                    for plan in plans:
                        view=None;winners=[]
                        for action in actions:
                            actual,ok,_,_=replay(w,s,plan,lambda _,a=action:a)
                            if view is None:view=actual
                            assert view==actual
                            if ok:winners.append(json.dumps(action,separators=(",",":")))
                        row.append(dict(view=view,winners=winners))
                    rows.append(row)
                req=json.dumps(dict(worlds=rows,plans=plans,
                    actions=[json.dumps(a,separators=(",",":")) for a in actions]))
                found=json.loads(sp.check_output(["node",str(HERE/"native_policy.js"),str(args.model.resolve()),PIN],input=req,text=True))
                sent=[]
                for no,decisions in found:
                    def decide(v):
                        key=next(a for vv,a in decisions if vv==v)
                        return json.loads(key)
                    actual=[replay(w,s,plans[no],decide) for w in worlds]
                    assert all(o[1] for o in actual)
                    sent.append(max(o[-1] for o in actual))
                if not found:
                    assert all(not replay(w,s,(-1,"none","none","none"),lambda _:None)[1] for w in worlds)
                result[name]=[len(worlds),len(plans),sent,[plans[i] for i,_ in found]]
            p.stdin.close();assert p.wait()==0
    expect={"five-early":4,"five-late-only":0,"six-late-only":2,"occupied-dock":2,
        "lost-diagnostic-peer":0,"no-authority":0,"stale-ordinal":2,"source-loss-late-only":0}
    assert {k:len(v[-1]) for k,v in result.items()}==expect
    assert all(p[0]==1 for p in result["occupied-dock"][-1])
    assert all(p[2]=="full" for p in result["stale-ordinal"][-1])
    assert result["five-early"][2]==[15,18,15,18]
    match={"five-early":"one-more","five-late-only":"late-only-pair","six-late-only":"late-only-joint-fit",
        "occupied-dock":"near-occupied","lost-diagnostic-peer":"near-no-probe","no-authority":"missing-grant",
        "stale-ordinal":"bad-ordinal","source-loss-late-only":"no-early"}
    model=json.loads(args.expected_model.read_text())["joint"]
    for k,m in match.items():
        worlds,plans,sent,ps=result[k]
        assert (worlds,plans)==(model[m]["worlds"],model[m]["plans"])
        assert [["/".join(map(str,p)),b] for p,b in zip(ps,sent)]==model[m]["budgets"]
    print(json.dumps(dict(runs=native,model_regimes_matched=len(match),columns=["worlds","plans","max_payload_bytes","admitted_plans"],result=result),sort_keys=True))
if __name__=="__main__":main()
