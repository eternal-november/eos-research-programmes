"""Actual WAL snapshots around native RWARE source progress."""
import archive as a
from contextlib import closing
import json
from pathlib import Path
import sqlite3
import tempfile

s=a.ns; j=a.native; A=s["A"]; key=s["KEY"]
def lookup(conn):
  return conn.execute("select tick, result from receipt where intent=?",(key,)).fetchone()
def tick(conn):
  return conn.execute("select max(tick) from log").fetchone()[0]
def record(row):
  return {"plant":"warehouse","key":key,"epoch":7,"at":1,
          "result":json.loads(row[1]) if row else None,"fence":False,"permit":False}

def movement(db):
  with closing(s["open_station"](db)) as d:
    assert d.execute("select can_apply from authority").fetchone()[0]==1
    g=j.reconstruct(d)
    g1=g.agents[1]; before=(g1.x,g1.y)
    # Current published simulation state, a distinct side intent. Choose the
    # first reachable neighboring unoccupied cell with the native route shim.
    route=None;goal=None
    for dx,dy in ((1,0),(0,1),(-1,0),(0,-1)):
      pt=(before[0]+dx,before[1]+dy)
      if not (0<=pt[0]<g.grid.shape[-1] and 0<=pt[1]<g.grid.shape[-2]): continue
      r=j.iso.route(j.n,g,1,pt,set())
      if r:
        route=r;goal=pt;break
    assert route
    for q,action in enumerate(route):
      j.apply(d,f"side:{q}",(A.NOOP.value,action.value),"none","bundled")
    h=j.reconstruct(d); after=(h.agents[1].x,h.agents[1].y)
    assert after==goal and before!=after
    return [before,after,len(route)]

def trace(root,committed):
    old=root/"source.db";out=root/"archive.db";s["init"](old,True)
    if committed: assert s["run"](old,1)["status"]=="applied"
    # Another actual write connection may commit while this view stays open.
    with closing(sqlite3.connect(old,isolation_level=None)) as r:
        r.execute("begin")
        original=lookup(r);old_tick=tick(r)
        assert bool(original)==committed
        a.archive(out,record(original))
        if not committed:
            assert s["run"](old,1)["status"]=="applied"
        side=movement(old)
        repeated=lookup(r)
        assert repeated==original and tick(r)==old_tick
        with closing(sqlite3.connect(old,isolation_level=None)) as fresh:
            visible=lookup(fresh);new_tick=tick(fresh)
        assert visible==(8,'[1,0]') and new_tick>old_tick
        r.execute("rollback")
    answer=a.decide(out,"warehouse",key,7)
    assert answer==("return" if committed else "refuse")
    with closing(s["open_station"](old)) as current:
        live_shelf=j.reconstruct(current).agents[0].carrying_shelf.id
    assert live_shelf==1
    original_owner=s["run"](old,1)
    assert original_owner["status"]=="cached" and original_owner["tick"]==8
    return dict(read_at=old_tick,repeated_at=old_tick,latest=new_tick,
                later_result=visible[0],side=side,decision=answer,after_side_shelf=live_shelf,
                writer_remains_enabled=s["state"](old)["writable"])


def current_use(root):
    old=root/"source.db";out=root/"archive.db";s["init"](old,True)
    assert s["run"](old,1)["status"]=="applied"
    with closing(s["open_station"](old)) as d:
        first=lookup(d)
        before=j.reconstruct(d).agents[0].carrying_shelf.id
        a.archive(out,record(first))
        plan,tags=j.plan()
        for i,act in enumerate(plan[tags["acceptA"]+1:tags["unloadA"]+1]):
            j.apply(d,f"return:{i}",act,"none","bundled")
        assert j.reconstruct(d).agents[0].carrying_shelf is None
        assert lookup(d)==first and before==1
    assert a.decide(out,"warehouse",key,7)=="return"
    return dict(receipt_ticked=first[0],before_shelf=before,after_shelf=None,
                current_tick=s["state"](old)["tick"])

out={}
with tempfile.TemporaryDirectory() as d:out["changed_consumer"]=current_use(Path(d))
for old in (False,True):
    with tempfile.TemporaryDirectory() as d: out["positive" if old else "absence"]=trace(Path(d),old)
print(json.dumps(out,sort_keys=True))
