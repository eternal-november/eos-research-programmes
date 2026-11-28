"""The two docks consume bytes actually accepted by the pinned broker."""
from pathlib import Path
from subprocess import Popen, PIPE, run
from tempfile import TemporaryDirectory
import sqlite3, collections, json, os, sys, ast
from itertools import product
from clock_law import source,fit,earliest_after,deny,transported

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
              CREATE TABLE Echo(era INTEGER, s INTEGER, g INTEGER, r INTEGER);
              CREATE TABLE ActiveClock(era INTEGER);
              CREATE TABLE ClockHandoff(old INTEGER,new INTEGER);
              CREATE TABLE ClockBridge(old INTEGER,new INTEGER,low INTEGER,high INTEGER);
              INSERT INTO ActiveClock VALUES (6);
         """)
         g.executemany("INSERT INTO Hold VALUES (?,?)",portal['hulls'])
    assert invoke_gate(base,('promote',6,7),44)==''
    with start(base) as db:
        assert db.execute("SELECT old,new FROM ClockHandoff").fetchone()==(6,7)
        assert db.execute("SELECT era FROM ActiveClock").fetchone()==(7,)
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
            def record(samples):
                with start(gate_db) as gx:gx.executemany("INSERT INTO Echo VALUES (?,?,?,?)",samples)
            # Plant fixture owns phase; actor's Echo table is filled
            # only by the native reply callback, not this generator.
            actual=[]
            apply,stamp=source("cumulative",phasebit,hold,actual.append)
            stale=[]
            source("cumulative",1-phasebit,hold,stale.append)
            write(f"{calib} {phasebit}")
            samples=[]
            acquired=False
            diagnostic=False
            for j,tag in enumerate("WN"):
                got,era,a,g,b,diag=read("echo",6)
                assert got==tag
                if a!="-":
                    v=tuple(map(int,(a,g,b)))
                    is_old=j==1
                    rec=(stale if is_old else actual)[0][j]
                    assert v==rec and int(era)==(6 if is_old else 7)
                    samples.append((int(era),*v))
                    if j==1:acquired=True
                else:
                    assert j==1 and g==b=="-"
                if j==0:assert diag=="0"
                else:diagnostic=diag=="1"
            assert acquired and diagnostic
            record(samples)
            former,current,d,receipt=read("clockbridge",4)
            if d!="-":
                assert (former,current)==("6","7") and int(receipt)<when
                dd=int(d)
                # Certified sampling mode is an independent fixture
                # capability: equal cut or 0..120ms sequential read.
                skew_bound=120000 if calib=="skew-bounded" else 0
                assert dd==2*(stamp-apply)+skew_bound
                with start(gate_db) as gx:
                    gx.execute("INSERT INTO ClockBridge VALUES (?,?,?,?)",(6,7,dd-skew_bound,dd))
            else:assert calib=="no-bridge" and (former,current,receipt)==("-","-","-")
            with start(gate_db) as gx:offsets=transported(gx)
            assert offsets.low<=stamp-apply<=offsets.high
            write(f"{when} {apply}")
            tick,k=map(int,read("maintenance",2))
            assert tick==when
            assert invoke_gate(gate_db,('apply','M',tick,'effect','reply'),0)=='closed'
            write("ok")
            announced,inspect=read("inspection",2)
            tick,k=map(int,read("actuation",2))
            assert tick==apply and int(inspect)<tick and k==(4,5)[selected]
            event=('apply','Q',tick,gaterule)
            assert invoke_gate(gate_db,(*event,gatecut,stamp),{"before":51,"after":52}[gatecut])==''
            got=invoke_gate(gate_db,(*event,'reply',stamp),0)
            def installed(n):
                with start(gate_db) as gx:
                    rows=gx.execute("SELECT key,start,finish FROM Installed ORDER BY start").fetchall()
                    assert gx.execute("SELECT COUNT(*) FROM Receipt").fetchone()==(n,)
                    assert gx.execute("SELECT COUNT(*) FROM Event").fetchone()==(n,)
                assert rows[0]==('M',when,when+249999)
                contact=any(max(inner[0],a)<=min(inner[1],b) for _,a,b in rows)
                outer=any(max(s,a)<=min(t,b) for _,a,b in rows for s,t in portal['hulls'])
                assert contact==outer
                return rows,contact

            rows,collides=installed(2)
            assert (got=='closed')==(len(rows)==2)
            assert not collides
            # Native simulation monitor, not an advance observation.
            write("contact" if collides else "ok")
            if collides:
                assert int(read("no_egress",1)[0])==tick
                assert p.wait(timeout=5)==0
                return dict(ack=False,effects=0,audit=[],egress=-1,contact=True,wait=0,timely_effect=False,diag=diagnostic,acquired=acquired,qualified=False)
            wait=0
            if gaterule=='effect':
                # Generous calendar baseline has real time, not just stamps.
                if got=='blocked':
                    wait=hold+1-tick
            elif got=='blocked':
                assert gaterule in ('bounded','unbound')
                wait=earliest_after(hold,stamp,offsets)
                assert wait>=1 and not deny(portal['hulls'],250000,stamp+wait,offsets)
                assert deny(portal['hulls'],250000,stamp+wait-1,offsets)
            write(str(tick+wait if wait else 0))
            if wait:
                resumed,k=map(int,read("retry",2))
                assert resumed==tick+wait and k==(4,5)[selected]
                # Fresh policy-authorized rescheduling: old reply still
                # records refusal; only the distinct retry key may act.
                assert invoke_gate(gate_db,('issue','Q2',when+2_000_000,250000),43)==''
                assert invoke_gate(gate_db,('apply','Q2',resumed,gaterule,'reply',stamp+wait),0)=='closed'
                rows,collides=installed(3)
                assert len(rows)==2 and not collides and rows[-1][0]=='Q2'
                write("ok")
            assert len(rows)==2
            # Independent evaluator, not a field revealed by the
            # worker's ambiguous local clock or an extra signal.
            timely_effect = rows[-1][1] <= hold+75000
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
            assert ('skipping DispatchMessages()' in errors)==(mode==2)
        with start(db) as conn:
            completed=conn.execute("SELECT result FROM effect WHERE id='I'").fetchall()
            audit_rows=conn.execute("SELECT slot,sample FROM audit ORDER BY slot").fetchall()
            assert conn.execute("SELECT result FROM receipt WHERE id='J'").fetchone()==('J3503',)
        assert int(inspect)<int(cut)<int(resume)<int(egress)
        assert all(x==(announced,) for x in completed)
        assert ack in ("-",announced)
        return dict(qualified=calib!="no-bridge",acquired=acquired,diag=diagnostic,ack=ack!="-",effects=len(completed),wait=wait,timely_effect=timely_effect,audit=[k for k,_ in audit_rows],
                    inspect=int(inspect),cut=int(cut),egress=int(egress),tx=int(tx),
                    primary_commit=primary_effect,primary_arrival=primary!="-",backup_arrival=backup!="-")

portals=[json.loads(l) for l in Path(__file__).with_name('PORTAL.jsonl').read_text().splitlines()]
def main(binary,sites):
    for portal in portals:
      samples=[]
      p=[source("wide",phase,portal['hulls'][1][1],samples.append) for phase in (0,1)]
      assert p[0][1]==p[1][1] and p[0][0]!=p[1][0] and samples[0]==samples[1]
      last=portal['hulls'][1][1]+75000-p[1][0]
      a,b=portal['cores'][1]
      assert last==24995 and a<=p[0][0]<=p[0][0]+last<=b
    summary={}
    for rule,calib in (("bounded","simultaneous"),("bounded","skew-bounded"),("bounded","no-bridge")):
        runs=[trace(binary,sites,w,miss,3,6,dc,'checked',rule,gc,bit,calib)
              for w,miss,dc,gc,bit in product(range(2),range(3),("before","after"),("before","after"),range(2))]
        summary[rule+"/"+calib]=dict(n=len(runs),complete=sum(r['ack'] and r['effects']==1 and r['audit']==[1,2] for r in runs),
           contact=sum(r.get('contact',False) for r in runs),
           timely_bundle=sum(r['timely_effect'] and r['diag'] and r['ack'] and r['effects']==1 and r['audit']==[1,2] for r in runs),
           delivered_echo=sum(r["acquired"] for r in runs),transport_witness=sum(r["qualified"] for r in runs),protected_diag=sum(r["diag"] for r in runs),
           max_egress_us=max(r['egress'] for r in runs))
    assert [v["complete"] for v in summary.values()]==[48,48,48]
    assert [v["timely_bundle"] for v in summary.values()]==[48,24,24]
    assert [v["contact"] for v in summary.values()]==[0,0,0]
    assert max(v["max_egress_us"] for v in summary.values())<454000000
    print(json.dumps(summary,sort_keys=True))
if __name__=="__main__":
    main(*sys.argv[1:])
