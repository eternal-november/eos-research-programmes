"""Native managed-simulator station moves to a different durable file."""
from collections import Counter
from contextlib import closing
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import os
import sqlite3
import subprocess
import sys
import tempfile

import journal
from core import Row, Event, check

KEY="run:7"
A=journal.A
plan,tags=journal.plan()
i=tags["acceptA"]
assert i==7
PAYLOAD=plan[i]

def open_station(path):
    d=journal.open_db(path)
    d.executescript("""
        create table if not exists authority (scope integer primary key,
          era integer not null, can_apply integer not null);
        create table if not exists permit (intent text primary key, payload text not null);
    """)
    return d

def authorized_step(db,era,phase):
    d=open_station(db)
    d.execute("begin immediate")
    right=d.execute("select payload from permit where intent=?",(KEY,)).fetchone()
    owner=d.execute("select era,can_apply from authority where scope=0").fetchone()
    if owner!=(era,1) or right!=(journal.encode(PAYLOAD),):
        d.rollback()
        d.close()
        return {"status":"refused"}
    found=d.execute("select tick,result from receipt where intent=?",(KEY,)).fetchone()
    if found:
        d.rollback()
        d.close()
        return {"status":"cached","tick":found[0],"result":json.loads(found[1])}
    if phase=="held":
        print("held",flush=True)
        assert sys.stdin.readline()=="go\n"
    g=journal.reconstruct(d)
    journal.crash(phase,"before-native")
    outcome=journal.step(g,PAYLOAD)
    journal.crash(phase,"after-native")
    v=journal.encode(outcome)
    t=g._cur_steps
    d.execute("insert into log values(?,?,?)",(t,journal.encode(PAYLOAD),v))
    d.execute("insert into receipt values(?,?,?,?)",(KEY,journal.encode(PAYLOAD),t,v))
    journal.crash(phase,"after-stage")
    d.commit()
    journal.crash(phase,"after-commit")
    d.close()
    return {"status":"applied","tick":t,"result":list(outcome)}

def run(path,era,phase="none",abort=False):
    c=subprocess.run([sys.executable,"-B",__file__,sys.argv[1],"worker",str(path),str(era),phase],
                     capture_output=True,text=True)
    if abort:
        assert c.returncode==77 and c.stdout=="",(c.stdout,c.stderr)
        return {"status":"silent"}
    assert c.returncode==0,c.stderr
    return json.loads(c.stdout)

def init(db,permit):
    with closing(open_station(db)) as d:
        d.execute("insert into authority values(0,1,1)")
        for j,act in enumerate(plan[:i]):
            journal.apply(d,f"pref:{j}",act,"none","bundled")
        if permit:d.execute("insert into permit values (?,?)",(KEY,journal.encode(PAYLOAD)))

def tag(d):
    # Canonical stable semantic projection, separate from SQLite file bytes.
    # Include permission and completion, not merely currently visible pose.
    s=journal.encode([list(d.execute(q)) for q in (
        "select * from authority order by scope","select * from permit order by intent",
        "select * from log order by tick","select * from receipt order by intent")])
    return sha256(s.encode()).hexdigest()

def fence(db):
    with closing(open_station(db)) as d:
        d.execute("begin immediate")
        assert d.execute("update authority set can_apply=0 where scope=0 and era=1 and can_apply=1").rowcount==1
        v=tag(d)
        d.commit()
        return v

def transfer(src,dst):
    with closing(open_station(src)) as s, closing(open_station(dst)) as d:
        s.backup(d)
        assert d.execute("pragma quick_check").fetchone()==("ok",)
        size=d.execute("pragma page_count").fetchone()[0]*d.execute("pragma page_size").fetchone()[0]
    assert not os.path.samefile(src,dst)
    return size

def install(db,expected,typed):
    with closing(open_station(db)) as d:
        d.execute("begin immediate")
        a=d.execute("select era,can_apply from authority where scope=0").fetchone()
        genuine=(a==(1,0) and tag(d)==expected and expected is not None)
        if typed and not genuine:
            d.rollback()
            return False
        d.execute("update authority set era=2,can_apply=1 where scope=0")
        d.commit()
        return True

def world_has_right(db):
    with closing(open_station(db)) as d:
        return d.execute("select * from permit where intent=?",(KEY,)).fetchone() is not None

def check_start(closed,complete,carries,mode):
    # Candidates prove permission and install/consuming barrier, not a solved outcome.
    req={x for x,b in (("authorized",carries),("frozen",closed),("coherent",complete)) if b}
    direct=closed and complete and carries
    ev=Event(1,0,need=frozenset(("authorized","frozen","coherent")),paid=("old",))
    typed=check(Row((),frozenset(req),(),{"retry":(ev,)}),"retry",1,{"old":1})
    assert typed==direct
    return typed if mode=="core" else direct

def state(db):
    with closing(open_station(db)) as d:
        return dict(tick=journal.reconstruct(d)._cur_steps, native=journal.state(journal.reconstruct(d)),
                    has=d.execute("select result from receipt where intent=?",(KEY,)).fetchone(),
                    writable=d.execute("select can_apply from authority").fetchone()[0])

def exercise(root,permit,phase,mode):
    src=root/"old.db"
    dst=root/"new.db"
    init(src,permit)
    moved=0
    if mode=="stale":
        moved=transfer(src,dst) # consistent, but before final publication/fence
    if permit:
        first=run(src,1,phase,True)
    else:
        assert run(src,1)=={"status":"refused"}
        first={"status":"silent"} # lifecycle return erased at client's boundary
    after=state(src)
    assert (after["tick"]==8)==(permit and phase=="after-commit")
    # The physically separate side job progresses in native RWARE during the
    # migration window and never reads either journal's authority.
    side=journal.iso.make(journal.n,False)
    side_actor=side.agents[1]
    journal.n.step(side,[A.NOOP.value,A.FORWARD.value])
    assert (side_actor.x,side_actor.y)==(2,1)
    token=None if mode in ("no-fence","unavailable") else fence(src)
    if mode not in ("stale","unavailable"):moved=transfer(src,dst)
    if mode=="lost-result":
        with closing(open_station(dst)) as d: d.execute("delete from receipt where intent=?",(KEY,))
    installed=False
    if mode!="unavailable":
        installed=install(dst,token,mode in ("core","direct"))
    if mode in ("core","direct"):
        go=check_start(token is not None,installed,world_has_right(dst),mode)
        answer=run(dst,2) if go else {"status":"refused"}
    elif installed:
        answer=run(dst,2)
    else:
        answer={"status":"refused"}
    old_late=run(src,1) if mode!="unavailable" else {"status":"unreachable"}
    if mode in ("core","direct"):
        assert installed and old_late=={"status":"refused"}
        if permit:
            assert answer["result"]==[1,0] and answer["tick"]==8
            assert answer["status"]==("cached" if phase=="after-commit" else "applied")
        else:assert answer=={"status":"refused"}
        assert state(dst)["tick"]==(8 if permit else 7)
    if mode=="stale" and permit and phase=="after-commit":
        assert after["has"] is not None and answer["status"]=="applied"
    if mode=="lost-result" and permit and phase=="after-commit":
        assert after["has"] is not None and answer["status"]=="applied" and answer["tick"]==9
    if mode=="no-fence" and permit and phase!="after-commit":
        assert answer["status"]==old_late["status"]=="applied"
    crossed=(answer["status"]=="applied" and
             (after["has"] is not None or old_late["status"]=="applied"))
    return dict(symptom=first["status"],reply=answer,old_late=old_late,
                final_donor=state(src)["tick"],moved_pages_bytes=moved,side=(side_actor.x,side_actor.y),
                duplicate_native_publication=crossed)

def typed_rejections(root):
    src=root/"s.db"
    dst=root/"n.db"
    lost=root/"l.db"
    init(src,True)
    transfer(src,dst)
    assert run(src,1,"after-commit",True)["status"]=="silent"
    t=fence(src)
    assert not install(dst,t,True)
    transfer(src,lost)
    with closing(open_station(lost)) as s:
        s.execute("delete from receipt where intent=?",(KEY,))
    assert not install(lost,t,True)
    assert not install(lost,None,True)

def concurrent_order(root,old_first):
    src=root/"old.db"
    dst=root/"new.db"
    init(src,True)
    if old_first:
        cmd=[sys.executable,"-B",__file__,sys.argv[1],"worker",str(src),"1","held"]
        p=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
        assert p.stdout.readline()=="held\n"
        # A different connection can verify that the worker holds the write
        # cut before the fencer is allowed to obtain its own.
        with closing(sqlite3.connect(src,timeout=0,isolation_level=None)) as d:
            try:d.execute("begin immediate")
            except sqlite3.OperationalError as e:
                assert e.sqlite_errorcode==sqlite3.SQLITE_BUSY
            else:raise AssertionError("no transaction barrier")
        f=subprocess.Popen([sys.executable,"-B",__file__,sys.argv[1],"fencer",str(src)],
                           stdout=subprocess.PIPE,text=True)
        assert f.stdout.readline()=="fencing\n"
        a,_=p.communicate("go\n",timeout=15)
        b,_=f.communicate(timeout=15)
        assert p.returncode==f.returncode==0
        old=json.loads(a)
        tok=b.strip()
    else:
        tok=fence(src)
        old=run(src,1)
    transfer(src,dst)
    assert install(dst,tok,True)
    new=run(dst,2)
    assert (old["status"],new["status"])==(
        ("applied","cached") if old_first else ("refused","applied"))
    return old,new

def keyed_projections(root):
    outputs={}
    projections=[]
    for old in (KEY,"sibling:7"):
        src=root/(old.replace(":","-")+".db")
        dst=root/(old.replace(":","-")+".new")
        init(src,True)
        # Two admissible commands can request the same native step under
        # distinct app identities. Setup publishes the sibling explicitly.
        with closing(open_station(src)) as conn:
            acquired=journal.apply(conn,old,PAYLOAD,"none","bundled")
            projections.append((state(src)["native"],list(conn.execute("select * from log"))))
            assert acquired["result"]==[1,0]
        t=fence(src)
        transfer(src,dst)
        assert install(dst,t,True)
        outputs[old]=run(dst,2)
    assert projections[0]==projections[1]
    assert outputs[KEY]["status"]=="cached" and outputs[KEY]["tick"]==8
    assert outputs["sibling:7"]["status"]=="applied" and outputs["sibling:7"]["tick"]==9
    return outputs

def sweep():
    out={}
    witness={}
    cases=[(True,phase) for phase in ("before-native","after-native","after-stage","after-commit")]
    cases += [(False,"before-native")]
    for permit,phase in cases:
        rows={}
        for arm in ("core","direct","stale","lost-result","no-fence","unavailable"):
            with tempfile.TemporaryDirectory() as d:
                x=rows[arm]=exercise(Path(d),permit,phase,arm)
            out.setdefault(arm,Counter()).update(cases=1,side=1,
                copies_bytes=x["moved_pages_bytes"],
                duplicate=int(x["duplicate_native_publication"]),
                active_service=int(x["reply"]["status"] in ("applied","cached")))
        assert rows["core"]==rows["direct"]
        if phase in ("after-stage","after-commit") or not permit:
            witness[f"{int(permit)}/{phase}"]=rows
    with tempfile.TemporaryDirectory() as d:typed_rejections(Path(d))
    with tempfile.TemporaryDirectory() as d:identity=keyed_projections(Path(d))
    writes={}
    for first in (False,True):
        with tempfile.TemporaryDirectory() as d:
            writes["old-first" if first else "fence-first"]=concurrent_order(Path(d),first)
    print(json.dumps({"arms":out,"witness":witness,"verified_rejections":3,
                      "overlap_order":writes,"identity":identity},sort_keys=True))

if len(sys.argv)>2 and sys.argv[2]=="fencer":
    print("fencing",flush=True)
    print(fence(sys.argv[3]))
elif len(sys.argv)>2:
    assert sys.argv[2]=="worker"
    print(journal.encode(authorized_step(sys.argv[3],int(sys.argv[4]),sys.argv[5])))
else:
    sweep()
