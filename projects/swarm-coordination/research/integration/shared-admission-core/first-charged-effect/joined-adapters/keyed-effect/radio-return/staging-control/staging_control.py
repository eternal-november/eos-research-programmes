#!/usr/bin/env python3
"""Run the unchanged native journal and radio under three matched transfer policies."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess as sp
import sys
import tempfile
HERE=Path(__file__).resolve().parent
def parent(name):
    return next(d for d in (HERE,*HERE.parents) if (d/name).is_file())
R=parent("journal_wire.py")
sys.path.insert(0,str(R))
import journal_wire as w

def pinned(path, expected):
    b=path.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==expected
    return b.decode()

def compact(db, raw):
    if len(raw)!=1 or not 16<=raw[0]<24:return None
    scope,ordinal=divmod(raw[0]-16,4)
    observed=tuple(x[0] for x in db.execute("select actor from motion order by tick"))
    if scope!={(3,0):0,(3,0,2):1}.get(observed):return None
    rec=db.execute("select result from motion where tick=?",(ordinal,)).fetchone()
    return b"p" if ordinal==0 else (b"k"+bytes(json.loads(rec[0])) if rec else None)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    a.support=a.support.resolve(); a.warehouse=a.warehouse.resolve()
    w.setup.read(a.support)
    pinned(R/"journal_wire.py","4ee45dc22a92962a631cc68cfec8d0ea37b8b8e9")
    original=pinned(R/"journal_wire.cc","bb093dd00911db1ebcd4a1a998d2986bca77d5dc")
    sys.path.insert(0,str(a.support.parent))
    import support
    iso,n=support.load(a.warehouse)
    plant=w.j.Plant(iso,n)
    # Only selectable presentation time is new in the radio bridge.
    assert original.count("order>>pref>>transfer")==1
    cpp=original.replace("order>>pref>>transfer","order>>pref>>transfer>>status_time")
    cpp=cpp.replace("std::string pref,transfer;","std::string pref,transfer; double status_time;")
    assert cpp.count('unhex(transfer),0.')==1
    cpp=cpp.replace('unhex(transfer),0.','unhex(transfer),status_time')
    stats=Counter()
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        for f in ("extract_radio.py","extract_visible.py","visibility_shim.hpp"):
            (root/f).write_bytes(w.setup.read(a.source/f))
        for f in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc","Vector3.hh",
                  "world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/f,root/f)
        for f in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",f],cwd=root,check=True)
        w.setup.read(root/"staged_replay.inc")
        (root/"wire.cc").write_text(cpp)
        fp=parent("first_effect.hpp")/"first_effect.hpp"
        (root/"first_effect.hpp").write_text(pinned(fp,"1e1624f0de957d627ea57182d94dbbb28d06c8a4"))
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","wire.cc","-o","wire"],cwd=root,check=True)
        states={(p,b):w.grant_source(plant,root/f"donor{p}{b}",p,b,0,a.warehouse,a.support.parent)
                  for p,b in product(range(2),repeat=2)}
        for b in range(2):assert states[0,b][2]==states[1,b][2]
        # Different legal actor order, identical final pose, different meaning
        # of row 2. The compact token must not authorize that other prefix.
        original_db=w.j.connect(root/"donor10")
        wrong_db=w.j.connect(root/"reordered")
        w.j.apply(wrong_db,plant,None,0);w.j.apply(wrong_db,plant,None,3)
        def positions(db):
            return [(x.x,x.y) for x in plant.native(db).agents]
        assert positions(original_db)==positions(wrong_db)
        raw=bytes([18])
        assert compact(original_db,raw)==b"k"+bytes(states[1,0][3])
        assert compact(wrong_db,raw) is None
        assert json.loads(wrong_db.execute("select result from motion where tick=2").fetchone()[0])!=states[1,0][3]
        stats["reordered_prefix_rejected"]=1
        original_db.close();wrong_db.close()
        with sp.Popen([root/"wire"],cwd=root,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for arm,prior,blocked,mode,qcap,bcap,edge,load,order in product(
                range(3),range(2),range(2),range(3),(4,5,9),(4,8),range(2),(0,1,4),range(2)):
                motion,full,rows,old=states[prior,blocked]
                # Two preinstalled complete actor sequences identify the supported basis.
                basis={(3,0):0,(3,0,2):1}[tuple(motion[1:])]
                data=(bytes([16+4*basis+(old[0] if old else 0)]) if arm==1 else full)
                if mode==1:data=b""
                if mode==2:data=(b"\xff" if arm==1 else b"x"+data[1:])
                path=root/"replacement"
                if path.exists():path.unlink()
                db=w.j.connect(path)
                db.execute("create table held_key(epoch integer primary key)")
                db.execute("create table prefix_ready(tick integer primary key)")
                emit(qcap,bcap,edge,load,0,order,motion.hex(),data.hex() or "-", -3 if arm==2 else 0)
                db.execute("create table staging(payload blob not null)")
                staged=None
                reached_guard=False
                service=None
                while True:
                    line=proc.stdout.readline().split()
                    assert line
                    if line[0]=="H":
                        raw=bytes.fromhex(line[1])
                        if raw.startswith(b"M"):emit(w.install(db,plant,raw));continue
                        # Packet is buffered without granting B any power.
                        assert db.execute("select * from held_key").fetchone() is None
                        staged=compact(db,raw) if arm==1 else (None if raw.startswith(b"x") else raw)
                        if staged is None:emit(0);continue
                        db.execute("insert into staging values (?)",(staged,))
                        staged=None
                        emit(1)
                    elif line[0]=="I":
                        # Activation is the same original control cut in every arm.
                        # Read the durable staging row after an actual reopen.
                        db.close(); db=w.j.connect(path)
                        row=db.execute("select payload from staging").fetchone()
                        staged=row[0] if row else None
                        assert db.execute("select * from held_key").fetchone() is None
                        reached_guard=True
                        assert list(db.execute("select * from motion order by tick"))==rows
                        if staged is not None:assert w.install(db,plant,staged)==1
                        known=bool(db.execute("select * from held_key").fetchone())
                        cached=w.j.resolved(db,w.j.OLD)
                        assert known==(mode==0) and cached==(old if known else None)
                        state=plant.native(db)
                        emit(int(known and (cached is not None or int(state.grid[0,2,2])==0)))
                    elif line[0]=="C":
                        assert reached_guard and staged is not None
                        _,service=w.j.apply(db,plant,w.j.OLD,1)
                        assert service is not None
                        emit(bytes(service).hex())
                    else:
                        assert line[0]=="O";break
                prefix,seal,req,report,side,tx,btx=map(int,line[1:8])
                active=len(data) if edge==0 and arm!=2 else 0
                fit=mode==0 and (prior or not blocked) and active+4<=qcap and (load if order==0 else 0)+4<=bcap
                expected=(old if prior else [len(rows)+1,1,2,2]) if fit else None
                got=bytes.fromhex(line[-1]) if line[-1]!="-" else b""
                assert service==expected and got==(bytes(expected) if fit else b"")
                assert (prefix,seal,req,report,side,tx,btx)==(1,int(mode==0),int(fit),int(fit),int(load>0),4*int(fit),4*int(fit))
                assert plant.native(db)._cur_steps==len(rows)+int(fit and not prior)
                stats[f"cases/{arm}"]+=1;stats[f"reply/{arm}"]+=report
                db.close()
            proc.stdin.close();assert proc.wait()==0
    print(json.dumps(dict(stats),sort_keys=True))
if __name__=="__main__":main()
