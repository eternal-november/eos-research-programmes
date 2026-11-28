"""The two docks consume bytes actually accepted by the pinned broker."""
from pathlib import Path
from subprocess import Popen, PIPE, run
from tempfile import TemporaryDirectory
import sqlite3, collections, json, os, sys

def start(path):
    db=sqlite3.connect(path)
    db.execute("PRAGMA synchronous=FULL")
    return db
def reconcile(db,wire,duplicate_bug=False):
    key=wire[:1]
    db.execute("BEGIN IMMEDIATE")
    got=db.execute("SELECT result FROM receipt WHERE id=?",(key,)).fetchone()
    if got is not None and not duplicate_bug:
        if got[0]!=wire:
            db.rollback()
            raise ValueError("same named duty conflicts with committed result")
    else:
        db.execute("INSERT INTO effect(id,result) VALUES (?,?)",(key,wire))
        db.execute("INSERT OR REPLACE INTO receipt VALUES (?,?)",(key,wire))
    db.commit()
    return wire if got is None or duplicate_bug else got[0]

def direct(db,wire):
    key=wire[:1]
    db.execute("BEGIN IMMEDIATE")
    db.execute("INSERT INTO effect(id,result) SELECT ?,? WHERE NOT EXISTS "
               "(SELECT 1 FROM receipt WHERE id=?)",(key,wire,key))
    db.execute("INSERT OR IGNORE INTO receipt VALUES (?,?)",(key,wire))
    ans,=db.execute("SELECT result FROM receipt WHERE id=?",(key,)).fetchone()
    if ans!=wire:
        db.rollback()
        raise ValueError("one key cannot name conflicting results")
    db.commit()
    return ans

def worker():
    _,_,db,phase=sys.argv
    wire=sys.stdin.read().strip()
    assert len(wire)==5 and wire.startswith("I")
    if phase=="before":os._exit(81)
    with start(db) as conn:
        res=direct(conn,wire) if phase=="direct" else reconcile(conn,wire,duplicate_bug=phase=="blind")
    if phase=="after":os._exit(82)
    print(res)
    raise SystemExit

if len(sys.argv)>1 and sys.argv[1]=="worker":
    worker()

def dock(path,phase,wire):
    return run([sys.executable,__file__,"worker",str(path),phase],
                input=wire+"\n",capture_output=True,text=True,check=False)

def trace(binary,sites,world,miss,mode,cap,phase,promote,variant):
    with TemporaryDirectory() as scratch:
        db=Path(scratch)/"docks.sqlite"
        with start(db) as conn:
            conn.executescript("""
               CREATE TABLE receipt (id TEXT PRIMARY KEY, result TEXT NOT NULL);
               CREATE TABLE effect (seq INTEGER PRIMARY KEY, id TEXT, result TEXT);
               CREATE TABLE audit (slot INTEGER PRIMARY KEY, sample TEXT NOT NULL);
               INSERT INTO receipt VALUES ('J', 'J3503');
               INSERT INTO effect(id,result) VALUES ('J', 'J3503');
            """)
        with Popen([binary,sites,str(world),str((miss<<2)|mode),str(cap),str(variant)],
                   stdin=PIPE,stdout=PIPE,stderr=PIPE,text=True) as p:
            def read(tag,n):
                fields=p.stdout.readline().strip().split()
                assert len(fields)==n+1 and fields[0]==tag,(fields,tag)
                return fields[1:]
            def write(x):
                p.stdin.write(x+'\n');p.stdin.flush()
            def audit(which,x):
                if x!="-":
                   with start(db) as conn:
                      conn.execute("INSERT INTO audit VALUES (?,?)",(which,x))
            announced,inspect=read("inspection",2)
            x,primary,cut=read("primary",3)
            audit(1,x)
            primary_effect=0
            if primary!="-":
                assert primary==announced
                child=dock(db,phase,primary)
                assert child.returncode in (81,82) and not child.stdout and not child.stderr,child
                primary_effect=int(phase=="after")
            write('-')  # Same application-visible absence of reply.
            backup,resume=read("backup",2)
            if backup!="-" and promote!="absent":
                assert backup==announced
                child=dock(db,promote,backup)
                assert child.returncode==0 and not child.stderr,child
                write(child.stdout.strip())
            else:
                write('-')
            ack,y,egress,tx,diag,early=read("return",6)
            audit(2,y)
            p.stdin.close()
            errors=p.stderr.read()
            assert p.wait()==0,errors
            assert ('skipping DispatchMessages()' in errors)==(variant!=1)
            assert ('No clients for endpoint D1' in errors)==(variant==3)
        with start(db) as conn:
            completed=conn.execute("SELECT result FROM effect WHERE id='I'").fetchall()
            audit_rows=conn.execute("SELECT slot,sample FROM audit ORDER BY slot").fetchall()
            assert conn.execute("SELECT result FROM receipt WHERE id='J'").fetchone()==('J3503',)
        assert int(inspect)<int(cut)<int(resume)<int(egress)
        assert all(x==(announced,) for x in completed)
        assert ack in ("-",announced)
        return dict(ack=ack!="-",effects=len(completed),audit=[k for k,_ in audit_rows],
                    inspect=int(inspect),cut=int(cut),egress=int(egress),tx=int(tx),
                    primary_commit=primary_effect,primary_arrival=primary!="-",
                    backup_arrival=backup!="-", diagnostic=diag!="-", early=int(early))

def main(binary,sites):
    # Full Cartesian product, without visible observation of the primary crash cut.
    summary={}

    for variant in range(5):
        rows=[trace(binary,sites,w,miss,3,6,phase,"checked",variant)
              for w in range(2) for miss in range(3) for phase in ("before","after")]
        acks=sum(r["ack"] and r["effects"]==1 for r in rows)
        audits=sum(r["audit"]==[1,2] for r in rows)
        diags=sum(r["diagnostic"] for r in rows)
        joint=sum(r["ack"] and r["effects"]==1 and r["audit"]==[1,2] and r["diagnostic"] for r in rows)
        assert all(r["effects"] in (0,1) for r in rows)
        summary[variant]=dict(n=len(rows), acknowledgments=acks, audits=audits, diagnostics=diags,
             all_four=joint, eg_max=max(r["egress"] for r in rows),early=sum(r["early"] for r in rows))
    assert [v["acknowledgments"] for v in summary.values()]==[0,12,12,12,12]
    assert [v["audits"] for v in summary.values()]==[12,12,0,12,12]
    assert [v["diagnostics"] for v in summary.values()]==[12,12,12,0,12]
    assert [v["all_four"] for v in summary.values()]==[0,12,0,0,12]
    assert summary[1]["eg_max"] < summary[4]["eg_max"] < 455000000 < 456498169
    print(json.dumps(summary,sort_keys=True))
if __name__=="__main__":
    main(*sys.argv[1:])
