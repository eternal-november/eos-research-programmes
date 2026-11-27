"""Managed native simulation: recover the historical assignment at its publication cut."""
from contextlib import closing
from pathlib import Path
from itertools import product
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
from same_queue import start,A,D,move,first_output

def text(x):return json.dumps(x,separators=(",",":"),sort_keys=True)
def conn(p):
    c=sqlite3.connect(p,isolation_level=None)
    c.execute("pragma journal_mode=WAL")
    c.execute("pragma synchronous=full")
    return c
def create(db,seed,pose):
    with closing(conn(db)) as c:
        c.executescript("""
          create table origin(id text not null, seed integer not null, pose integer not null);
          create table ticks(t integer primary key, cmd text not null, projection text not null);
          create table dispatch(t integer primary key, previous integer not null, assigned integer not null);
          create table probe(t integer primary key, source_cut integer not null, requested integer not null);
        """)
        c.execute("insert into origin values(?,?,?)",("station-A:era-1",seed,pose))

def apply(w,code):
    before=tuple(o.id for o in w.request_queue)
    obs,reward=move(w,*(A[x] for x in code))
    after=tuple(o.id for o in w.request_queue)
    return (before,after,obs,reward)

def reconstruct(c):
    origin,seed,pose=c.execute("select id,seed,pose from origin").fetchone()
    w=start(pose,seed)
    for t,cmd,projection in c.execute("select * from ticks order by t"):
        event=apply(w,json.loads(cmd))
        assert w._cur_steps==t and text(event)==projection
        if event[0]!=event[1]:
            assert c.execute("select previous,assigned from dispatch where t=?",(t,)).fetchone()==(event[0][0],event[1][0])
    return w,origin

def submit(db,t,code,phase):
    with closing(conn(db)) as c:
        c.execute("begin immediate")
        cached=c.execute("select cmd,projection from ticks where t=?",(t,)).fetchone()
        if cached is not None:
            assert cached[0]==text(code)
            c.rollback()
            return "returned",json.loads(cached[1])[1]
        w,origin=reconstruct(c)
        assert w._cur_steps==t-1
        before,after,obs,reward=apply(w,code)
        c.execute("insert into ticks values(?,?,?)",(t,text(code),text((before,after,obs,reward))))
        if before!=after:
            assert len(before)==len(after)==1 and sum(reward)==.5
            c.execute("insert into dispatch values(?,?,?)",(t,before[0],after[0]))
        if t==2:
            # This adapter records both the observer output and the exact
            # source revision governing it under the same source transaction.
            e=c.execute("select t from dispatch order by t desc limit 1").fetchone()[0]
            flag=int(any(x["shelf_requested"][0] for x in obs["sensors"]))
            c.execute("insert into probe values(?,?,?)",(t,e,flag))
        if phase=="after-stage":os._exit(84)
        c.commit()
        if phase=="after-commit":os._exit(84)
        return "applied",list(after)

def evidence(db,t,read="named"):
    with closing(conn(db)) as c:
        c.execute("begin")
        w,origin=reconstruct(c)
        assert w._cur_steps==t
        p=c.execute("select t,source_cut,requested from probe").fetchone()
        if read=="named":
            row=c.execute("select t,previous,assigned from dispatch where t=?",(p[1],)).fetchone()
        elif read=="latest":
            row=c.execute("select t,previous,assigned from dispatch order by t desc limit 1").fetchone()
        else:row=None
        current=(origin,t,tuple(x.id for x in w.request_queue),first_output(w))
        c.rollback()
        return current,(origin,*p),None if row is None else (origin,*row)

def authorized_turn(current,probe,receipt):
    if not receipt or current[0]!=probe[0] or probe[0]!=receipt[0] or probe[2]!=receipt[1] or not receipt[1]<probe[1]:
        return None
    if receipt[2]!=3 or receipt[3] not in (1,2):return None
    return "LEFT" if bool(probe[3])==(receipt[3]==1) else "RIGHT"

N="NOOP"
def command(a=N,b=N,c=N):return a,b,c
def prefix(db,mode):
    for t,a in enumerate([command(b="FORWARD"),command(a="FORWARD"),command(a="LEFT"),command(a="LEFT"),command(a="FORWARD")],1):
        if t==1 and mode!="none":
            proc=subprocess.run([sys.executable,"-B",__file__,"worker",str(db),str(t),text(a),mode],text=True,capture_output=True)
            assert proc.returncode==84 and proc.stdout=="",proc
            with closing(conn(db)) as c:
                raw=c.execute("select t,previous,assigned from dispatch").fetchall()
                assert bool(raw)==(mode=="after-commit")
        status,q=submit(db,t,a,"none")
        if t==1:
            assert status==("returned" if mode=="after-commit" else "applied")
            mark=q[0]
    assert mark in (1,2)
    left,right=("LEFT","RIGHT") if mark==1 else ("RIGHT","LEFT")
    for t,a in enumerate((right,"FORWARD",left,"FORWARD","TOGGLE_LOAD","LEFT","LEFT","FORWARD",right,"FORWARD"),6):
        submit(db,t,command(c=a),"none")

def trial(root,seed,pose,mode):
    db=root/"sink.db";create(db,seed,pose)
    prefix(db,mode)
    cur,probe,receipt=evidence(db,15)
    assert cur[2]==(4,) and probe[1:3]==(2,1) and receipt[1:3]==(1,3)
    assert authorized_turn(*evidence(db,15,"latest")) is None
    assert authorized_turn(*evidence(db,15,"missing")) is None
    assert authorized_turn(cur,probe,("stale:era",*receipt[1:])) is None
    chosen=authorized_turn(cur,probe,receipt)
    assert chosen==("LEFT" if pose==2 else "RIGHT")
    submit(db,16,command(a=chosen),"none");submit(db,17,command(a="FORWARD"),"none")
    with closing(conn(db)) as c:
        w,_=reconstruct(c)
        assert w._cur_steps==17 and (w.agents[0].x,w.agents[0].y)==(3,3)
        assert c.execute("select count(*) from dispatch").fetchone()==(2,)
    return cur,probe,receipt,chosen

def main():
    checks={}
    for mode in ("none","after-stage","after-commit"):
      for seed,pose in product((14,9),(2,4)):
        with tempfile.TemporaryDirectory() as t:checks[mode,seed,pose]=trial(Path(t),seed,pose,mode)
      for x,y in ((2,4),(4,2)):
        p,q=checks[mode,14,x],checks[mode,9,y]
        assert p[:2]==q[:2] and p[2]!=q[2] and p[3]!=q[3]
    print(text({"native_completed":len(checks),"worker_exit_trials":8,
        "negative_controls_per_case":["latest","missing","stale-origin"],
        "chosen_turns":[[mode,seed,pose,k[3]] for (mode,seed,pose),k in checks.items()]}))
if __name__=="__main__":
    if len(sys.argv)>1:
        m,db,t,code,p=sys.argv[1:];assert m=="worker"
        print(text(submit(Path(db),int(t),json.loads(code),p)))
    else:main()
