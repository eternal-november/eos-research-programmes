"""Consume current native custody at the action cut, not the archived event."""
import archive as a
from contextlib import closing
from pathlib import Path
import tempfile
import json

s=a.ns; j=a.native; A=s["A"]; key=s["KEY"]
plan,tags=j.plan()
moves=plan[tags["acceptA"]+1:tags["acceptA"]+4]
assert all(int(pair[0])!=A.TOGGLE_LOAD.value for pair in moves)

def pose(g):
    q=g.agents[0];return [q.x,q.y,q.dir.value]
def holds(g):
    q=g.agents[0].carrying_shelf
    return q is not None and q.id==1
def side(d):
    g=j.reconstruct(d);r=j.iso.route(j.n,g,1,(3,2),set());assert r
    for i,b in enumerate(r):j.apply(d,f"side:{i}",[A.NOOP.value,b.value],"none","bundled")
    g=j.reconstruct(d)
    assert [g.agents[1].x,g.agents[1].y]==[3,2]
def unload_return(d,initial):
    for i,b in enumerate(plan[tags["acceptA"]+1:tags["unloadA"]+1]):
        j.apply(d,f"unload:{i}",b,"none","bundled")
    g=j.reconstruct(d);r=j.iso.route(j.n,g,0,tuple(initial[:2]),set());assert r
    for i,b in enumerate(r):j.apply(d,f"return:{i}",[b.value,A.NOOP.value],"none","bundled")
    for i in range(4):
        if pose(j.reconstruct(d))==initial:break
        j.apply(d,f"turn:{i}",[A.RIGHT.value,A.NOOP.value],"none","bundled")
    assert pose(j.reconstruct(d))==initial and not holds(j.reconstruct(d))

def atomic(db,evidence,expected):
    with closing(s["open_station"](db)) as d:
        d.execute("begin immediate")
        g=j.reconstruct(d)
        before=g._cur_steps
        # Witness of prior operation is a different consumer from current shelf.
        if a.decide(evidence,"warehouse",key,7)!="return":
            d.rollback()
            return ("refused",before,before,pose(g))
        seen=list(d.execute("select intent,payload from receipt where intent like 'follow:%' order by intent"))
        if seen:
            assert seen==[(f"follow:{i}",j.encode(m)) for i,m in enumerate(moves)]
            d.rollback()
            return ("cached",before,before,pose(g))
        owner=d.execute("select era,can_apply from authority where scope=0").fetchone()
        if owner!=(1,1) or not holds(g) or pose(g)!=expected:
            d.rollback()
            return ("refused",before,before,pose(g))
        # Bound operations contain only turns and an old lawful path
        # segment. Persist all fixture effects at the tested write cut.
        for i,m in enumerate(moves):
            result=j.step(g,m);t=g._cur_steps
            assert holds(g)
            d.execute("insert into log values(?,?,?)",(t,j.encode(m),j.encode(result)))
            d.execute("insert into receipt values(?,?,?,?)",(f"follow:{i}",j.encode(m),t,j.encode(result)))
        d.commit()
        return ("applied",before,g._cur_steps,pose(g))

def branch(root,arm):
    db=root/"source.db";out=root/"archive.db";s["init"](db,True)
    assert s["run"](db,1)["status"]=="applied"
    with closing(s["open_station"](db)) as d:
        g=j.reconstruct(d);p=pose(g)
        assert holds(g)
        captured=d.execute("select tick,result from receipt where intent=?",(key,)).fetchone()
        assert captured==(8,"[1,0]")
        a.archive(out,{"plant":"warehouse","key":key,"epoch":7,"at":1,
             "result":json.loads(captured[1]),"fence":False,"permit":False})
        if arm=="side": side(d)
        else: unload_return(d,p)
        now=j.reconstruct(d)
        z=pose(now)
        assert z==p and a.decide(out,"warehouse",key,7)=="return"
        current=holds(now)
    x=atomic(db,out,p)
    assert current==(arm=="side") and x[0]==("applied" if current else "refused")
    if current:assert x[3][:2]!=p[:2] and x[2]==x[1]+3
    else:assert x[1]==x[2] and x[3]==p
    retry=atomic(db,out,p)
    assert retry[0]==("cached" if current else "refused") and retry[1]==retry[2]==x[2]
    return dict(shared_pose=p,known_old=True,current=current,controller=x,retry=retry)
ret={}
for arm in ("side","unloaded"):
  with tempfile.TemporaryDirectory() as d:ret[arm]=branch(Path(d),arm)
print(json.dumps(ret,sort_keys=True))
