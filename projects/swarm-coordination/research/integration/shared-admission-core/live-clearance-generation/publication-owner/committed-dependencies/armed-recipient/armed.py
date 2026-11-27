"""Prepared/armed recipient replacement on pinned native station bodies.

The local paths and identities are an explicitly trusted simulation fixture.
All cancellation replies are retrieved from the affected local effect store.
"""
from contextlib import closing
from itertools import product
from pathlib import Path
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import grant as one
import overlap as model
from trace_queries import source

def regopen(p):
    return sqlite3.connect(p,isolation_level=None)
class Setup:
    def __init__(self,root):
        self.src,self.cut,self.dest,_,self.names=one.prepare(root)
        self.reg=root/"armed-registry.db"
        self.a,self.b=self.names
        with closing(regopen(self.reg)) as c:
            c.executescript("pragma journal_mode=WAL; pragma synchronous=full;"
                "create table choice(k int primary key check(k=1), gen int not null, candidate text not null, armed int not null);")
            c.execute("insert into choice values(1,1,?,0)",(self.a,))
        for p in self.dest.values():
            with closing(source.open_station(p)) as c:
                c.executescript("create table activation(k int primary key check(k=1), blocked int not null, installed int not null);"
                    "insert into activation values(1,0,0);")
    def read(self):
        with closing(regopen(self.reg)) as c:
            return c.execute("select gen,candidate,armed from choice").fetchone()

def arm(reg,want,identity,crash=None):
    with closing(regopen(reg)) as c:
        c.execute("begin immediate")
        a=c.execute("select gen,candidate,armed from choice").fetchone()
        if a[:2]!=(want,identity):
            c.rollback();return False
        c.execute("update choice set armed=1")
        if crash=="before-arm-commit":os._exit(79)
        c.commit()
        if crash=="after-arm-commit":os._exit(79)
        return (want,identity)

def seal(c):
    era=c.execute("select era,can_apply from authority where scope=0").fetchone()[0]
    return source.tag(c),model.seal_sidecar(c),era

def local_activate(db,cut,identity,ticket,blocked_check=True):
    # Trusted in-process witness in this harness, not a credential parser.
    if not ticket or ticket[1]!=identity:return False
    with closing(source.open_station(db)) as c:
        c.execute("begin immediate")
        row=c.execute("select blocked,installed from activation").fetchone()
        got=c.execute("select era,can_apply from authority where scope=0").fetchone()
        if (blocked_check and row!=(0,0)) or got!=(cut[2],0) or seal(c)!=cut:
            c.rollback();return False
        c.execute("update authority set era=?,can_apply=1 where scope=0",(cut[2]+1,))
        c.execute("update source_identity set id=?",(identity,))
        c.execute("update activation set installed=1")
        c.commit()
        return True

def local_close(q,who,gen):
    p=q.dest[who]
    with closing(source.open_station(p)) as c:
        c.execute("begin immediate")
        old=c.execute("select era,can_apply from authority where scope=0").fetchone()
        was=c.execute("select blocked,installed from activation").fetchone()
        assert (old,was) in (((1,0),(0,0)),((2,1),(0,1)))
        c.execute("update activation set blocked=1")
        if was[1]:c.execute("update authority set can_apply=0 where scope=0 and era=2")
        ans=(who,gen,seal(c),bool(was[1]))
        c.commit()
        return ans

def reassign(q,proof=None):
    with closing(regopen(q.reg)) as c:
        c.execute("begin immediate")
        gen,who,armed=c.execute("select gen,candidate,armed from choice").fetchone()
        if who!=q.a or (armed and (proof is None or proof[:2]!=(who,gen))):
            c.rollback();return False
        c.execute("update choice set gen=gen+1,candidate=?,armed=0",(q.b,))
        c.commit()
        return True

def cooperative_retirement(q,proof):
    # New receiver carries the actual closed source state, not just the old donor image.
    cut=q.cut if proof is None else proof[2]
    if proof and proof[3]:
        source.transfer(q.dest[q.a],q.dest[q.b])
        # This trusted fixture selects a fresh B store. Copied application data and
        # old A's physical executor gate are distinct scopes.
        with closing(source.open_station(q.dest[q.b])) as c:
            c.execute("update activation set blocked=0,installed=0")
    ticket=arm(q.reg,2,q.b)
    assert local_activate(q.dest[q.b],cut,q.b,ticket)
    return cut[2]+1

def side_step():
    g=source.journal.iso.make(source.journal.n,False)
    actor=g.agents[1]
    source.journal.n.step(g,[source.A.NOOP.value,source.A.FORWARD.value])
    assert (actor.x,actor.y)==(2,1)

def execute(root,stage,accessible):
    q=Setup(root)
    received=None
    ticket=None
    if stage!="no-arm":
        # Simulate loss of the arm acknowledgement by discarding the return.
        ticket=arm(q.reg,1,q.a)
        assert ticket
    if stage in ("installed","staged","effect"):
        assert local_activate(q.dest[q.a],q.cut,q.a,ticket)
    if stage in ("staged","effect"):
        model.run(q.dest[q.a],model.AKEY,2,"after-stage" if stage=="staged" else "after-commit")
    if accessible and stage!="no-arm":
        received=local_close(q,q.a,1)
    swap=reassign(q,received)
    # Independent state-machine reference for the admitted states.
    assert swap==(accessible or stage=="no-arm")
    if not swap:
        side_step()
        assert q.read()==(1,q.a,1) and not arm(q.reg,2,q.b)
        assert model.op(q.dest[q.b],model.AKEY,2)["status"]=="refused"
        return [stage,accessible,"wait",True]
    # A stale prepared nomination never produces an arm. After arm, the old
    # ticket itself can be in flight; the actual local barrier rejects it.
    assert not arm(q.reg,1,q.a)
    if received:
        assert not local_activate(q.dest[q.a],q.cut,q.a,ticket)
        assert model.op(q.dest[q.a],model.AKEY,2)["status"]=="refused"
    era=cooperative_retirement(q,received)
    got=model.op(q.dest[q.b],model.AKEY,era)["status"]
    assert got==("cached" if stage=="effect" else "applied")
    assert model.op(q.dest[q.b],model.AKEY,era)["status"]=="cached"
    assert model.op(q.src,model.AKEY,1)["status"]=="refused"
    side_step()
    return [stage,accessible,got,True]

def held_cut(root):
    q=Setup(root)
    ticket=arm(q.reg,1,q.a)
    assert local_activate(q.dest[q.a],q.cut,q.a,ticket)
    cmd=[sys.executable,"-B",str(Path(__file__).with_name("overlap.py")),sys.argv[1],"worker",
         str(q.dest[q.a]),model.AKEY,"2","held"]
    p=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    try:
        assert p.stdout.readline()=="held\n"
        with closing(sqlite3.connect(q.dest[q.a],timeout=0,isolation_level=None)) as c:
            try:c.execute("begin immediate")
            except sqlite3.OperationalError as e:assert e.sqlite_errorcode==sqlite3.SQLITE_BUSY
            else:raise AssertionError("competing closure escaped transaction barrier")
        assert not reassign(q)
        stdout,stderr=p.communicate("go\n",timeout=15)
        assert p.returncode==0 and "applied" in stdout,stderr
    finally:
        if p.poll() is None:p.kill();p.communicate()
    seal=local_close(q,q.a,1)
    assert reassign(q,seal)
    era=cooperative_retirement(q,seal)
    assert model.op(q.dest[q.b],model.AKEY,era)["status"]=="cached"
    return "held effect linearizes before closure; successor keeps its keyed result"

def skipped_local_check(root):
    q=Setup(root)
    ticket=arm(q.reg,1,q.a)
    assert ticket
    # An arm has been issued but actual local install is paused.
    proof=local_close(q,q.a,1)
    assert reassign(q,proof)
    era=cooperative_retirement(q,proof)
    assert model.op(q.dest[q.b],model.AKEY,era)["status"]=="applied"
    # Excluded ablation: old ticket installed without consulting the local barrier.
    assert local_activate(q.dest[q.a],q.cut,q.a,ticket,blocked_check=False)
    assert model.op(q.dest[q.a],model.AKEY,2)["status"]=="applied"
    return "ignoring the effect-local block admits two independent native commits"

def invoke(q,role,phase="none"):
    return [sys.executable,"-B",str(Path(__file__)),sys.argv[1],role,str(q.reg),q.a,q.b,phase]

def arm_crash(root,phase):
    q=Setup(root)
    p=subprocess.run(invoke(q,"arm",phase),text=True,capture_output=True)
    assert p.returncode==79 and not p.stdout,p
    won=reassign(q)
    assert won==(phase=="before-arm-commit")
    if won:
        assert not arm(q.reg,1,q.a)
        era=cooperative_retirement(q,None)
        assert model.op(q.dest[q.b],model.AKEY,era)["status"]=="applied"
    else:
        ticket=arm(q.reg,1,q.a)
        assert ticket
        assert not local_activate(q.dest[q.b],q.cut,q.b,ticket)
        assert local_activate(q.dest[q.a],q.cut,q.a,ticket)
        assert model.op(q.dest[q.a],model.AKEY,2)["status"]=="applied"
    return [phase,won]

def choice_race(root):
    q=Setup(root)
    ps=[subprocess.Popen(invoke(q,role),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True) for role in ("arm","swap")]
    results=[]
    for p in ps:
        out,err=p.communicate(timeout=20)
        assert p.returncode==0,err
        results.append(json.loads(out))
    assert sorted(results)==[False,True]
    if results[0]:
        assert q.read()==(1,q.a,1)
    else:
        assert q.read()==(2,q.b,0)

def main():
    cases=[]
    for cut,access in product(("no-arm","arm-only","installed","staged","effect"),(False,True)):
        with tempfile.TemporaryDirectory() as dir:cases.append(execute(Path(dir),cut,access))
    with tempfile.TemporaryDirectory() as dir:held=held_cut(Path(dir))
    with tempfile.TemporaryDirectory() as dir:unsafe=skipped_local_check(Path(dir))
    crashes=[]
    for phase in ("before-arm-commit","after-arm-commit"):
        with tempfile.TemporaryDirectory() as dir:crashes.append(arm_crash(Path(dir),phase))
    for _ in range(4):
        with tempfile.TemporaryDirectory() as dir:choice_race(Path(dir))
    print(json.dumps({"cases":cases,"held_control":held,"excluded_ablation":unsafe,
          "actual_arm_crashes":crashes,"choice_races":4},sort_keys=True,separators=(",",":")))
if __name__=="__main__":
    if len(sys.argv)>2:
        mode,p,a,b,phase=sys.argv[2:]
        if mode=="arm":out=bool(arm(p,1,a,phase))
        else:
            assert mode=="swap";out=reassign(SimpleNamespace(reg=p,a=a,b=b))
        print(json.dumps(out))
    else:main()
