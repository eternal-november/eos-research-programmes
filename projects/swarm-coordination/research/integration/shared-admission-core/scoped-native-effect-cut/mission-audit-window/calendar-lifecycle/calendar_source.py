"""Civil simulated calibration owner. Effective intervals and exact edit receipts share a WAL."""
import json
import os
import sqlite3
import subprocess
import sys

CLOCK="cave-rest-clock"

def open_calendar(path):
    d=sqlite3.connect(path, isolation_level=None)
    d.execute("pragma journal_mode=WAL")
    d.execute("pragma synchronous=FULL")
    return d

def initialize(path,cuts,w):
    with open_calendar(path) as d:
        d.executescript("""
        CREATE TABLE Hold(clock TEXT NOT NULL, mask INTEGER NOT NULL,t0 INTEGER,t1 INTEGER);
        CREATE TABLE Calendar(actor INTEGER PRIMARY KEY, lo INTEGER, hi INTEGER);
        CREATE TABLE Edit(key TEXT PRIMARY KEY, request TEXT NOT NULL, decision TEXT NOT NULL);
        CREATE TABLE Applied(key TEXT PRIMARY KEY);
        CREATE TABLE Operation(actor INTEGER, cut INTEGER, PRIMARY KEY(actor,cut));
        """)
        d.execute("begin immediate")
        d.execute("insert into Hold values (?,?,?,?)",(CLOCK,w,*cuts))
        # Two admitted role owners have a narrow service-relevant
        # calibration. Third calibration is a different physical source.
        d.executemany("insert into Calendar values (?,?,?)",
            [(a,cuts[0],cuts[0]+1000) for a in range(3)])
        d.commit()

def read_plan(d):
    clock,w,t0,t1=d.execute("select * from Hold").fetchone()
    assert clock==CLOCK and t0<t1 and w
    rows={a:(lo,hi) for a,lo,hi in d.execute("select * from Calendar")}
    assert len(rows)==3
    return w,(t0,t1),rows

def project(rows,cuts):
    return tuple(sum(1<<j for j,t in enumerate(cuts) if rows[i][0]<=t<rows[i][1])
                 for i in (0,1))

def pending_read(path):
    with open_calendar(path) as d:
        w,cuts,rows=read_plan(d)
        return project(rows,cuts)

def tick(path,t):
    # Here calibration is a physical source operation in the simulator:
    # a due appointment records actual start at its sampled native cut.
    # Neither source readiness nor the old audit depends on bytes alone.
    with open_calendar(path) as d:
        d.execute("begin immediate")
        _,cuts,rows=read_plan(d)
        assert t in cuts
        # The source's work-start evidence arises at this cut, not when
        # admission was calculated. An unexecuted command is not a sample.
        due={i for i,(lo,hi) in rows.items() if lo<=t<hi}
        for i in due:d.execute("insert into Operation values (?,?)",(i,t))
        d.commit()
        return tuple(int(i in due) for i in (0,1))

def apply(path,key,kind,policy,phase):
    with open_calendar(path) as d:
        d.execute("begin immediate")
        req=json.dumps([kind,policy],separators=(",",":"))
        r=d.execute("select request,decision from Edit where key=?",(key,)).fetchone()
        if r is not None:
            assert req==r[0]
            d.rollback()
            return r[1]
        w,cuts,rows=read_plan(d)
        actors={"none":(),"east":(0,),"west":(1,),"paired":(0,1),"out":(2,)}[kind]
        # Scope is the expressly authorized modeled owner or a valid
        # two-owner joint request. No authority inference from the route.
        scope=all(i in rows for i in actors)
        prop=dict(rows)
        for i in actors:prop[i]=(cuts[1],cuts[1]+1000)
        old=project(rows,cuts);new=project(prop,cuts)
        if policy=="shared":
            # Singleton supports, each at most one missed cut. Both
            # candidate calendars must leave an old opportunity TOGETHER.
            room=bool(w&~(new[0]|new[1]))
            got=subprocess.check_output([os.environ["SCOPED_CUT_BIN"],"effect",
                         str(int(scope)),"1",str(int(room)),"1"],text=True)
            admit=int(got)==6
        elif policy=="direct":
            admit=scope and any((w&(1<<j)) and all(not(prop[i][0]<=t<prop[i][1]) for i in (0,1))
                                for j,t in enumerate(cuts))
        elif policy=="separate":
            admit=scope and all(w&~mask for mask in new)
        elif policy=="frozen":
            admit=scope and old==new
        else:raise ValueError(policy)
        result="installed" if admit else "refused"
        if admit:
            for i in actors:d.execute("update Calendar set lo=?,hi=? where actor=?",(*prop[i],i))
            d.execute("insert into Applied values (?)",(key,))
        d.execute("insert into Edit values (?,?,?)",(key,req,result))
        if phase=="before":os._exit(71)
        d.commit()
        if phase=="after":os._exit(72)
        return result

if __name__=="__main__":print(apply(*sys.argv[1:]))
