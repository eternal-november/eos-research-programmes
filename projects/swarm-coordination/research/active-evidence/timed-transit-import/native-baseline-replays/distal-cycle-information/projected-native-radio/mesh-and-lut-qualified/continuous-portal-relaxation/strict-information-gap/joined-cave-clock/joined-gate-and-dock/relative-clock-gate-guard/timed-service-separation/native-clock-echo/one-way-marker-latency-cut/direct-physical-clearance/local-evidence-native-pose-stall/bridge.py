"""The two docks consume bytes actually accepted by the pinned broker."""
from pathlib import Path
from subprocess import Popen, PIPE, run
from tempfile import TemporaryDirectory
import sqlite3, collections, json, os, sys, ast
from itertools import product
from fractions import Fraction


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

def invoke_gate(db,args,status):
    worker=Path(__file__).with_name('worker.py')
    p=run([sys.executable,str(worker),str(db),*map(str,args)],capture_output=True,text=True,timeout=10)
    assert p.returncode==status and not p.stderr,p
    return p.stdout.strip()

def gate_setup(base, portal):
    source=ast.parse(Path(__file__).with_name('trace.py').read_text())
    fn=next(x for x in source.body if isinstance(x,ast.FunctionDef) and x.name=='scenario')
    queries=[ast.literal_eval(x.args[0]) for x in ast.walk(fn) if isinstance(x,ast.Call)
             and isinstance(x.func,ast.Attribute) and x.func.attr=='executescript']
    assert len(queries)==1
    with start(base) as g:
         g.executescript(queries[0]+"""
             CREATE TABLE ExitReceipt(gate INTEGER,era INTEGER,mission TEXT);
             CREATE TABLE Authority(gate INTEGER,era INTEGER);
         """)
         g.execute("INSERT INTO Authority VALUES (?,7)",(portal['gate'],))
         g.executemany("INSERT INTO Hold VALUES (?,?)",portal['hulls'])
    maint=portal['hulls'][0][1]+1_000_000
    assert invoke_gate(base,('issue','M',maint,250000),43)==''
    assert invoke_gate(base,('issue','Q',maint+2_000_000,250000),43)==''
    return maint

def trace(binary,sites,world,miss,mode,cap,phase,promote,gaterule,gatecut,phasebit,calib):
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
        with Popen([binary,sites,str(world),str((miss<<2)|mode),str(cap)],
                   stdin=PIPE,stdout=PIPE,stderr=PIPE,text=True) as p:
            def read(tag,n):
                fields=p.stdout.readline().strip().split()
                assert len(fields)==n+1 and fields[0]==tag,(fields,tag,p.stderr.read() if not fields else "")
                return fields[1:]
            def write(x):
                p.stdin.write(x+'\n');p.stdin.flush()
            def audit(which,x):
                if x!="-":
                   with start(db) as conn:
                      conn.execute("INSERT INTO audit VALUES (?,?)",(which,x))
            selected=int(read("schedule",1)[0])
            assert selected==1-world
            portal=portals[selected]
            assert portal['gate']==selected
            gate_db=Path(scratch)/"gate.sqlite"
            when=gate_setup(gate_db,portal)
            inner=portal['cores'][1]
            hold=portal['hulls'][1][1]
            spec=cases[selected,"bounded"]
            local=calib=="local-slow-repair"
            source=int(local)
            sample=spec["witness"]+(10000 if local else 0)
            repair=spec["witness"]+{"radio-fast-repair":40000,"radio-slow-repair":70000,"local-slow-repair":70000}[calib]
            apply=sample+10000 if local else repair
            assert when==spec["slot"] and hold==spec["h"]
            other=[spec[k] for k in ("witness","error","bias","axis","sign")]+[int(spec["body"]),float(Fraction(spec["plane"]))]
            rw=" ".join(map(str,[when,apply,*other,source,sample,repair]))
            write(rw)
            tick,k=map(int,read("maintenance",2))
            assert tick==when
            assert invoke_gate(gate_db,('apply','M',tick,'effect','reply'),0)=='closed'
            write("ok")
            announced,inspect=read("inspection",2)
            rc,diag,seen=map(int,read("clearance",3))
            assert diag==int(not local) and seen==spec["witness"] and rc==1
            with start(gate_db) as gx:
                if rc:gx.execute("INSERT INTO ExitReceipt VALUES (?,7,'return')",(selected,))
            tick,k=map(int,read("actuation",2))
            assert tick==apply and int(inspect)<tick and k==spec["at"]
            event=('apply','Q',tick,'clearance')
            assert invoke_gate(gate_db,(*event,gatecut),{"before":51,"after":52}[gatecut])==''
            got=invoke_gate(gate_db,(*event,'reply'),0)
            with start(gate_db) as gx:
                rows=gx.execute("SELECT key,start,finish FROM Installed ORDER BY start").fetchall()
                assert gx.execute("SELECT COUNT(*) FROM Receipt").fetchone()==(2,)
                assert gx.execute("SELECT COUNT(*) FROM Event").fetchone()==(2,)
            assert rows[0]==('M',when,when+249999)
            assert (got=='closed')==(rc==1)==(len(rows)==2)
            collides=any(max(inner[0],a)<=min(inner[1],b) for _,a,b in rows)
            outer=any(max(s,a)<=min(t,b) for _,a,b in rows for s,t in portal['hulls'])
            assert collides==outer
            assert collides==(calib=="point" and rc==1)
            write("contact" if collides else "ok")
            if collides:
                assert int(read("no_egress",1)[0])==tick
                assert p.wait(timeout=5)==0
                return dict(ack=False,effects=0,audit=[],egress=-1,contact=True,timely_effect=False,diag=bool(diag),acquired=bool(rc))
            recovered,proof=read("repaired",2)
            assert int(recovered)==repair and proof=="Y"
            diag=1
            timely_effect=rc and rows[-1][1]<=hold+75000
            x,primary,cut=read("primary",3)
            assert max(b for _,a,b in rows)<int(cut)  # no transient slab during RF
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
            ack,y,egress,tx=read("return",4)
            audit(2,y)
            p.stdin.close()
            errors=p.stderr.read()
            assert p.wait()==0,errors
            assert 'skipping DispatchMessages()' in errors and "AuxX" in errors
        with start(db) as conn:
            completed=conn.execute("SELECT result FROM effect WHERE id='I'").fetchall()
            audit_rows=conn.execute("SELECT slot,sample FROM audit ORDER BY slot").fetchall()
            assert conn.execute("SELECT result FROM receipt WHERE id='J'").fetchone()==('J3503',)
        assert int(inspect)<int(cut)<int(resume)<int(egress)
        assert all(x==(announced,) for x in completed)
        assert ack in ("-",announced)
        return dict(acquired=bool(rc),diag=bool(diag),ack=ack!="-",effects=len(completed),timely_effect=timely_effect,audit=[k for k,_ in audit_rows],
                    inspect=int(inspect),cut=int(cut),egress=int(egress),tx=int(tx),
                    primary_commit=primary_effect,primary_arrival=primary!="-",backup_arrival=backup!="-")

portals=[json.loads(l) for l in Path(__file__).with_name('PORTAL.jsonl').read_text().splitlines()]
def main(binary,sites,posefile):
    global cases
    cases={(r["gate"],r["mode"]):r for r in json.loads(Path(posefile).read_text())}
    summary={}
    for calib in ("radio-fast-repair","radio-slow-repair","local-slow-repair"):
        runs=[trace(binary,sites,w,miss,3,6,dc,'checked',"clearance",gc,bit,calib)
              for w,miss,dc,gc,bit in product(range(2),range(3),("before","after"),("before","after"),range(1))]
        summary[calib]=dict(n=len(runs),complete=sum(r['ack'] and r['effects']==1 and r['audit']==[1,2] for r in runs),
           contact=sum(r.get('contact',False) for r in runs),
           timely_bundle=sum(r['timely_effect'] and r['diag'] and r['ack'] and r['effects']==1 and r['audit']==[1,2] for r in runs),
           clearance_receipt=sum(r["acquired"] for r in runs),protected_diag=sum(r["diag"] for r in runs),
           max_egress_us=max(r['egress'] for r in runs))
    assert [v["contact"] for v in summary.values()]==[0]*3
    assert [v["timely_bundle"] for v in summary.values()]==[24,0,24]
    assert all(v["complete"]==v["protected_diag"]==24 for v in summary.values())
    assert [v["clearance_receipt"] for v in summary.values()]==[24]*3
    assert all(v["max_egress_us"]<454000000 for v in summary.values())
    print(json.dumps(summary,sort_keys=True))
if __name__=="__main__":
    main(*sys.argv[1:])
