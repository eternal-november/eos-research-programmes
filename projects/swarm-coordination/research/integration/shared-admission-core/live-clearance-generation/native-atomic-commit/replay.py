"""The local journal, not the shadow simulator, is the publication authority."""
from pathlib import Path
from itertools import product
from collections import Counter
import importlib.util
import json
import os
import sqlite3
import subprocess
import sys
import tempfile

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location("fixture",up/"isolated.py")
iso=importlib.util.module_from_spec(spec);spec.loader.exec_module(iso)
n=iso.load_native(up/"native_source.py")
A=n.Action

def make():
    g=iso.make(n,False)
    g.max_steps=1000
    return g

def step(g,payload):
    _,r,done,truncated,_=n.step(g,list(payload))
    assert not done and not truncated
    return tuple(int(round(x*2)) for x in r)

def state(g):
    return dict(agents=[(a.x,a.y,a.dir.value,
                        None if a.carrying_shelf is None else a.carrying_shelf.id,
                        a.has_delivered) for a in g.agents],
                shelves=[(s.id,s.x,s.y) for s in g.shelfs],
                request=[s.id for s in g.request_queue],
                tick=g._cur_steps,inactive=g._cur_inactive_steps)

def encode(x):
    return json.dumps(x,separators=(",",":"),sort_keys=True)

def open_db(path):
    d=sqlite3.connect(path,isolation_level=None)
    assert d.execute("pragma journal_mode=wal").fetchone()[0]=="wal"
    d.execute("pragma synchronous=full")
    d.executescript("""
        CREATE TABLE IF NOT EXISTS log (
            tick INTEGER PRIMARY KEY, payload TEXT NOT NULL, result TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS receipt (
            intent TEXT PRIMARY KEY, payload TEXT NOT NULL,
            tick INTEGER NOT NULL UNIQUE, result TEXT NOT NULL
        );
    """)
    return d

def reconstruct(d):
    g=make()
    for idx,payload,result in d.execute("select tick,payload,result from log order by tick"):
        assert g._cur_steps+1==idx
        assert encode(step(g,json.loads(payload)))==result
    return g

def crash(phase,wanted):
    if phase==wanted:
        os._exit(77)

def apply(d,intent,payload,phase,variant):
    ep=encode(payload)
    d.execute("begin immediate")
    seen=d.execute("select payload,tick,result from receipt where intent=?",(intent,)).fetchone()
    if seen is not None:
        d.rollback()
        if seen[0]!=ep:return {"conflict":True}
        return {"tick":seen[1],"result":json.loads(seen[2]),"cached":True}
    g=reconstruct(d)
    crash(phase,"before-native")
    outcome=step(g,payload)  # private evaluation, not a published transition
    er=encode(outcome)
    t=g._cur_steps
    crash(phase,"after-native")
    d.execute("insert into log values (?,?,?)",(t,ep,er))
    if variant=="bundled":
        d.execute("insert into receipt values (?,?,?,?)",(intent,ep,t,er))
    crash(phase,"after-stage")
    d.commit()
    crash(phase,"after-commit")
    if variant=="split":
        # Comparator: published transition precedes volatile response and
        # separately durable application receipt. No intent in native log.
        d.execute("insert into receipt values (?,?,?,?)",(intent,ep,t,er))
    return {"tick":t,"result":list(outcome),"cached":False}

def plan():
    g=make()
    log=[]
    tags={}
    def add(a,b=A.NOOP):
        payload=(a.value,b.value)
        log.append(payload)
        return step(g,payload)
    def walk(pos):
        cmds=iso.route(n,g,0,pos,set())
        assert cmds is not None
        for a in cmds:
            if add(a)[0]:
                tags[f"accept{'A' if len(tags)==1 else 'B'}"]=len(log)-1
    add(A.NOOP,A.FORWARD)
    tags["independent"]=len(log)-1
    assert (g.agents[1].x,g.agents[1].y)==(2,1)
    # Park the independently moving carrier off A's cell first.
    add(A.NOOP,A.RIGHT)
    add(A.NOOP,A.FORWARD)
    for shelf in g.shelfs:
        home=(shelf.x,shelf.y)
        walk(home)
        assert add(A.TOGGLE_LOAD)==(0,0)
        walk((4,1))
        assert g.agents[0].has_delivered
        walk(home)
        assert add(A.TOGGLE_LOAD)==(1,0)
        if shelf.id==1: tags["unloadA"]=len(log)-1
    assert list(tags)==["independent","acceptA","unloadA","acceptB"], tags
    return log,tags

def worker(dfile,intent,payload,phase,variant):
    d=open_db(dfile)
    print(encode(apply(d,intent,json.loads(payload),phase,variant)),flush=True)
    d.close()

def child(dfile,intent,payload,phase,variant):
    run=subprocess.run([sys.executable,"-B",__file__,str(up),"worker",dfile,intent,
                        encode(payload),phase,variant],capture_output=True,text=True)
    if phase!="none":
        assert run.returncode==77 and run.stdout=="",(phase,run)
        return
    assert run.returncode==0,run.stderr
    return json.loads(run.stdout)

def main():
    log,tags=plan()
    counts={k:Counter() for k in ("bundled","split")}
    witness={}
    phases=("before-native","after-native","after-stage","after-commit")
    for (tag,index),phase,arm in product(tags.items(),phases,counts.keys()):
        g=make()
        predictions=[step(g,move) for move in log[:index+1]]
        expect=state(g)
        with tempfile.TemporaryDirectory() as loc:
            path=str(Path(loc)/"plant.sqlite")
            d=open_db(path)
            for i,move in enumerate(log[:index]):
                out=apply(d,f"run:{i}",move,"none",arm)
                assert out["result"]==list(predictions[i])
            d.close()
            token=f"run:{index}"
            child(path,token,log[index],phase,arm)
            d=open_db(path)
            recovered=state(reconstruct(d))
            assert recovered["tick"]==index+int(phase=="after-commit")
            during=d.execute("select tick,result from receipt where intent=?",(token,)).fetchone()
            assert bool(during)==(phase=="after-commit" and arm=="bundled")
            d.close()
            retried=child(path,token,log[index],"none",arm)
            d=open_db(path)
            actual=state(reconstruct(d))
            equal=actual==expect and retried["result"]==list(predictions[-1])
            assert equal==(phase!="after-commit" or arm=="bundled")
            if arm=="bundled":
                assert apply(d,token,log[index],"none",arm)["cached"]
                wrong=list(log[index])
                wrong[0]=(wrong[0]+1)%len(A)
                assert apply(d,token,wrong,"none",arm)=={"conflict":True}
                if index+1<len(log):
                    fresh=apply(d,f"run:{index+1}",log[index+1],"none",arm)
                    assert not fresh["cached"] and fresh["tick"]==index+2
            d.close()
            counts[arm].update(cases=1,exact=int(equal),
                               emitted_duplicate=int(actual["tick"]>expect["tick"]))
            if phase=="after-commit":
                witness[f"{tag}/{arm}"]={"motion":actual["agents"],"tick":actual["tick"],
                    "retry":retried,"reference_reward":predictions[-1],
                    "reference_motion":expect["agents"],"reference_tick":expect["tick"]}
    assert counts["bundled"]["exact"]==16 and counts["split"]["exact"]==12
    # Two independent replacement subprocesses race one durable command key.
    with tempfile.TemporaryDirectory() as loc:
        path=str(Path(loc)/"overlap.sqlite")
        open_db(path).close()
        cmd=[sys.executable,"-B",__file__,str(up),"worker",path,"runner:0",
             encode(log[0]),"none","bundled"]
        workers=[subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
                 for _ in range(2)]
        out=[]
        for w in workers:
            answer,err=w.communicate()
            assert w.returncode==0,err
            out.append(json.loads(answer))
        assert sorted(o["cached"] for o in out)==[False,True]
        d=open_db(path)
        final=state(reconstruct(d))
        assert final["tick"]==1 and final["agents"][1][:2]==(2,1)
        d.close()
    print(encode({"summary":counts,"witness":witness,
                  "concurrent":{"cached":sum(r["cached"] for r in out),
                                "committed_ticks":final["tick"]}}))

if __name__=="__main__":
    if len(sys.argv)>2:
        _,_,_,db,token,payload,phase,arm=sys.argv
        worker(db,token,payload,phase,arm)
    else:
        main()
