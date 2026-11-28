from contextlib import closing
from pathlib import Path
from sys import argv
from lease_binding import bind,Context,Content,Lease
import json,os,sqlite3
path,verb,*args=argv[1:]
with closing(sqlite3.connect(path,isolation_level=None)) as db:
    db.execute("PRAGMA synchronous=FULL")
    db.execute("BEGIN IMMEDIATE")
    if verb=="transfer":
        site,prior=db.execute("SELECT gate,owner FROM Authority").fetchone()
        assert int(args[0])==site and prior==10
        db.execute("UPDATE Authority SET owner=11")
        db.execute("COMMIT")
        os._exit(44)
    _,key,principal,t,span,mode,cut=(verb,*args)
    site,owner=db.execute("SELECT gate,owner FROM Authority").fetchone()
    stated,actor,time,d=key,int(principal),int(t),int(span)
    raw=db.execute("SELECT key,actor,start,end FROM Committed WHERE key=? AND gate=?",(stated,site)).fetchone()
    historical=Lease(*raw) if raw else None
    # Raw authoritative resource query, verified inside serialization.
    # Comparator drops old-operator leases despite same physical gate.
    if mode=="owner-only":
        leases=tuple(Lease(*x) for x in db.execute(
            "SELECT key,actor,start,end FROM Committed WHERE gate=? AND actor=?",(site,owner)))
    else:
        assert mode=="full"
        leases=tuple(Lease(*x) for x in db.execute(
            "SELECT key,actor,start,end FROM Committed WHERE gate=?",(site,)))
    clear,=db.execute("SELECT clear FROM Physical WHERE gate=?",(site,)).fetchone()
    decision,value=bind(Context(owner,leases),Content(bool(clear),historical),key,actor,time,d)
    if decision=="install":
        db.execute("INSERT INTO Committed VALUES (?,?,?,?,?)",(*value,site))
    if cut=="before":os._exit(51)
    db.execute("COMMIT")
    if cut=="after":os._exit(52)
    assert cut=="reply"
    print(json.dumps([decision,value]))
