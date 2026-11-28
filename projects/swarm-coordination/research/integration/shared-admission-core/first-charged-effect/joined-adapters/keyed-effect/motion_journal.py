"""Bounded simulator plant. SQLite publishes the authoritative native action."""
import json
import os
from pathlib import Path
import sqlite3
import sys
import numpy as np

def enc(x):
    return json.dumps(x,separators=(",",":"),sort_keys=True)

class Plant:
    def __init__(self,iso,n):
        self.iso,self.n=iso,n
    def start(self):
        n=self.n
        w=self.iso.make(n,False)
        w.shelfs=[];w.goals=[];w.request_queue=[]
        w.n_agents=4
        n.Agent.counter=0
        # A and B head toward distinct gates. Z subsequently can block B.
        w.agents=[
          n.Agent(1,1,n.Direction.RIGHT,0),
          n.Agent(1,2,n.Direction.RIGHT,0),
          n.Agent(3,2,n.Direction.LEFT,0),
          n.Agent(4,4,n.Direction.LEFT,0)]
        w.grid=np.zeros((2,5,5),dtype=int)
        w._recalc_grid()
        return w
    def step(self,world,actor):
        act=self.n.Action
        a=[act.NOOP.value]*4
        if actor>=0:a[actor]=act.FORWARD.value
        self.n.step(world,a)
        target=world.agents[actor] if actor>=0 else None
        return (world._cur_steps,actor,None if target is None else target.x,
                None if target is None else target.y)
    def snapshot(self,world):
        return [world._cur_steps,[(a.x,a.y,a.dir.value) for a in world.agents]]
    def native(self,db):
        w=self.start()
        for tick,actor,result in db.execute("select tick,actor,result from motion order by tick"):
            assert w._cur_steps+1==tick
            observed=self.step(w,actor)
            assert enc(observed)==result
        return w

def connect(path):
    db=sqlite3.connect(path,isolation_level=None)
    db.execute("pragma journal_mode=wal")
    db.execute("pragma synchronous=full")
    db.executescript("""
    CREATE TABLE IF NOT EXISTS motion(
       tick INTEGER PRIMARY KEY, actor INTEGER NOT NULL, result TEXT NOT NULL);
    CREATE TABLE IF NOT EXISTS receipt(
       key TEXT PRIMARY KEY, law TEXT NOT NULL,
       tick INTEGER NOT NULL UNIQUE, result TEXT NOT NULL);
    """)
    return db

OLD="old-42"
SAME_PHYSICAL_UNRELATED="reference-pass"
LAW="old-gate-duty:epoch7:{A,B}"

def resolved(db,key):
    row=db.execute("select law,result from receipt where key=?",(key,)).fetchone()
    if row is None:return None
    assert row[0]==LAW
    return json.loads(row[1])

def apply(db,plant,key,actor,termination=False):
    '''Compare stable intent law before selecting candidate payload.
    Runs in declared local source loop; object state is journal-owned.
    '''
    db.execute("begin immediate")
    got=resolved(db,key) if key else None
    if got is not None:
        db.rollback()
        return ("cached",got)
    w=plant.native(db)
    if key:
        # In this scope either successor may discharge exactly this old
        # duty by actual entry into its own gate. An ambient move isn't
        # considered a discharge merely because it leads to the same pose.
        assert actor in (0,1)
        if w.grid[0,actor+1,2]:
            db.rollback()
            return ("blocked",None)
    result=plant.step(w,actor)
    if key:
        assert result[2:]==(2,actor+1)
    tick=result[0]
    db.execute("insert into motion values (?,?,?)",(tick,actor,enc(result)))
    if key:
        db.execute("insert into receipt values (?,?,?,?)",(key,LAW,tick,enc(result)))
    db.commit()
    if termination:os._exit(77)
    return "new",list(result)

if __name__=="__main__":
    # A real worker exit after the durable commit, before replying.
    import support
    iso,n=support.load(Path(sys.argv[3]))
    d=connect(sys.argv[1])
    apply(d,Plant(iso,n),sys.argv[2],0,True)
