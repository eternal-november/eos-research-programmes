#!/usr/bin/env python3
"""Two SQLite stores, native SubT checkpoint transfer, retry and exact radio reply."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess as sp
import sys
import tempfile

HERE=Path(__file__).resolve().parent
P=next(x for x in (HERE,*HERE.parents) if (x/"replay_effect_cut.py").is_file())
K=next(x for x in (HERE,*HERE.parents) if (x/"motion_journal.py").is_file())
sys.path[:0]=[str(P),str(K)]
import replay_effect_cut as setup
import motion_journal as j

def pin(path,digest):
    b=path.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==digest

def grant_source(plant, path, prior, blocked, mode, inputs, support):
    source=j.connect(path)
    j.apply(source,plant,None,3) # independent plant movement
    source.close()
    key=j.OLD if prior else j.SAME_PHYSICAL_UNRELATED
    child=sp.run([sys.executable,"-B",K/"motion_journal.py",path,key,inputs],
                 env={**os.environ,"PYTHONPATH":str(support)},capture_output=True)
    assert child.returncode==77 and not child.stdout and not child.stderr,child
    source=j.connect(path)
    if blocked:assert j.apply(source,plant,None,2)==("new",[3,2,2,2])
    # Explicit local donor fence. Ordinary writers using these tables can
    # no longer extend its state. This is not a physical/remote interlock.
    source.executescript("""
     BEGIN IMMEDIATE;
     CREATE TABLE donor_sealed(v INTEGER PRIMARY KEY);
     INSERT INTO donor_sealed VALUES (1);
     CREATE TRIGGER no_donor_motion BEFORE INSERT ON motion
     WHEN EXISTS (SELECT 1 FROM donor_sealed)
     BEGIN SELECT RAISE(ABORT,'sealed donor'); END;
     CREATE TRIGGER no_donor_settlement BEFORE INSERT ON receipt
     WHEN EXISTS (SELECT 1 FROM donor_sealed)
     BEGIN SELECT RAISE(ABORT,'sealed donor'); END;
     COMMIT;
    """)
    rows=list(source.execute("select * from motion order by tick"))
    old=j.resolved(source,j.OLD)
    assert old==([2,0,2,1] if prior else None)
    try:
        j.apply(source,plant,None,-1)
        raise AssertionError("sealed writer accepted")
    except sqlite3.IntegrityError as e:
        assert str(e)=="sealed donor"
        source.rollback()
    assert list(source.execute("select * from motion order by tick"))==rows
    source.close()
    # Prefix compression is specific to a preinstalled deterministic plant:
    # actor IDs suffice to reconstruct the checked motion result and tick.
    motion=b"M"+bytes(actor for _,actor,_ in rows)
    data=b"p" if old is None else b"k"+bytes(old)
    if mode==1:data=b""   # missing proof - not negative evidence
    if mode==2:data=b"x"+data[1:] # stale receipt namespace; still radio debit
    return motion,data,rows,old

def install(db,plant,data):
    if data[:1]==b"M":
        assert db.execute("select count(*) from motion").fetchone()[0]==0
        assert tuple(data[1:]) in ((3,0),(3,0,2))
        db.execute("begin immediate")
        w=plant.start()
        for actor in data[1:]:
            r=plant.step(w,actor)
            db.execute("insert into motion values (?,?,?)",(r[0],actor,j.enc(r)))
        db.execute("insert into prefix_ready values (?)",(w._cur_steps,))
        db.commit()
        return 1
    if data[:1]==b"x":return 0
    db.execute("begin immediate")
    assert db.execute("select * from prefix_ready").fetchone() is not None
    if data==b"p":
        assert j.resolved(db,j.OLD) is None
    else:
        assert data[:1]==b"k" and len(data)==5
        r=list(data[1:])
        row=db.execute("select result from motion where tick=?",(r[0],)).fetchone()
        assert row and json.loads(row[0])==r
        db.execute("insert into receipt values (?,?,?,?)",(j.OLD,j.LAW,r[0],j.enc(r)))
    db.execute("insert into held_key values (7)")
    db.commit()
    return 1

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    a.support=a.support.resolve();a.warehouse=a.warehouse.resolve()
    setup.read(a.support)
    pin(P/"first_effect.hpp","1e1624f0de957d627ea57182d94dbbb28d06c8a4")
    pin(K/"motion_journal.py","19447b46bd35310370ddd386ed2c29b3a60f60b5")
    sys.path.insert(0,str(a.support.parent))
    import support
    iso,n=support.load(a.warehouse)
    plant=j.Plant(iso,n)
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        for f in ("extract_radio.py","extract_visible.py","visibility_shim.hpp"):
            (root/f).write_bytes(setup.read(a.source/f))
        for f in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc","Vector3.hh",
                  "world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/f,root/f)
        for f in ("extract_visible.py","extract_radio.py"):
            sp.run([sys.executable,"-B",f],cwd=root,check=True)
        setup.read(root/"staged_replay.inc")
        shutil.copyfile(HERE/"journal_wire.cc",root/"journal_wire.cc")
        shutil.copyfile(P/"first_effect.hpp",root/"first_effect.hpp")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","journal_wire.cc","-o","wire"],cwd=root,check=True)
        # The paired source histories are generated by real worker exits.
        states={}
        for prior,blocked in product(range(2),repeat=2):
            vals=grant_source(plant,root/f"donor-{prior}-{blocked}",prior,blocked,0,a.warehouse,a.support.parent)
            states[prior,blocked]=vals
        for blocked in range(2):assert states[0,blocked][2]==states[1,blocked][2]
        cases=product(range(2),range(2),range(3),(4,5,9),(4,8),range(2),(0,1,4),range(4),range(2))
        stats=Counter();examples={}
        with sp.Popen([root/"wire"],cwd=root,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for case in cases:
                prior,blocked,mode,qcap,bcap,edge,load,arm,order=case
                motion,data,rows,old=states[prior,blocked]
                if mode==1:data=b""
                if mode==2:data=b"x"+data[1:]
                a0=root/"replacement"
                if a0.exists():a0.unlink()
                db=j.connect(a0)
                db.execute("create table held_key(epoch integer primary key)")
                db.execute("create table prefix_ready(tick integer primary key)")
                emit(qcap,bcap,edge,load,arm,order,motion.hex(),data.hex() or "-")
                service=None
                installed=[]
                while True:
                    line=proc.stdout.readline().split()
                    assert line
                    if line[0]=="H":
                        raw=bytes.fromhex(line[1]);installed.append(raw)
                        emit(install(db,plant,raw))
                    elif line[0]=="I":
                        assert list(db.execute("select * from motion order by tick"))==rows
                        known=bool(db.execute("select * from held_key").fetchone())
                        cached=j.resolved(db,j.OLD)
                        assert known==(mode==0)
                        assert cached==(old if known else None)
                        local_world=plant.native(db)
                        decision=(known and (cached is not None or int(local_world.grid[0,2,2])==0))
                        if arm==3:decision=True # missing-as-pending ablation in callback
                        emit(int(decision))
                    elif line[0]=="C":
                        known=bool(db.execute("select * from held_key").fetchone())
                        if known or arm==3:
                            _, service=j.apply(db,plant,j.OLD,1)
                        emit(bytes(service).hex() if service else "-")
                    else:
                        assert line[0]=="O";break
                prefix,seal,req,report,side,tx,btx=map(int,line[1:8])
                assert installed==[motion]+([data] if data else [])
                active=len(data) if edge==0 else 0
                radio=active+4<=qcap
                reply=(load if order==0 else 0)+4<=bcap
                allow=mode==0 and (prior or not blocked)
                tried=(allow and radio and reply) if arm<2 else allow if arm==2 else radio
                hit=tried and radio
                expected=None
                if hit and (mode==0 or arm==3):
                    if mode==0 and prior:expected=old
                    elif not blocked:expected=[len(rows)+1,1,2,2]
                got=bytes.fromhex(line[-1]) if line[-1]!="-" else b""
                actual=expected is not None and reply
                assert (prefix,seal,req,report,side,tx,btx)==(
                    1,int(mode==0),int(hit),int(actual),int(load>0),int(tried)*4,int(expected is not None)*4), (case,line,expected)
                assert service==expected and got==(bytes(expected) if actual else b"")
                assert plant.native(db)._cur_steps==len(rows)+int(expected is not None and expected!=old)
                duplicate=int(prior and mode>0 and expected is not None and expected!=old)
                stats[f"reported/{arm}"]+=report
                stats[f"spent_without_return/{arm}"]+=int(tx>0 and not report)
                stats[f"duplicate_effect/{arm}"]+=duplicate
                stats[f"cases/{arm}"]+=1
                if qcap in (4,9) and bcap==4 and load in (0,1) and (edge or blocked==0):
                    if (prior,blocked,mode,edge,load,arm) in {
                        (1,0,0,0,0,0),(0,0,0,0,0,0),(1,1,0,1,0,0),
                        (0,1,0,1,0,0),(1,0,1,1,0,3),(0,0,0,1,1,0),(0,0,0,1,1,2)}:
                        examples[str(case)]=[len(motion),len(data),tx,btx,req,report,duplicate,line[-1]]
                db.close()
            proc.stdin.close();assert proc.wait()==0
        assert stats["reported/0"]==stats["reported/1"]
    print(json.dumps({"results":dict(stats),"columns":["prefix_tx","key_tx","Q_tx","B_tx",
          "request_rx","reply_rx","duplicate","reply"],"witnesses":examples},sort_keys=True))
if __name__=="__main__":main()
