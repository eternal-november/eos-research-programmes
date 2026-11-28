#!/usr/bin/env python3
"""Keep a historical exact result when the future actor binding changes."""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse
import hashlib
import json
import shutil
import subprocess as sp
import sys
import tempfile

HERE=Path(__file__).resolve().parent
def parent(name):
    return next(x for x in (HERE,*HERE.parents) if (x/name).is_file())
P=parent("replay_effect_cut.py"); J=parent("motion_journal.py")
sys.path[:0]=[str(P),str(J)]
import replay_effect_cut as setup
import motion_journal as j

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    setup.read(a.support)
    b=(J/"motion_journal.py").read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="19447b46bd35310370ddd386ed2c29b3a60f60b5"
    sys.path.insert(0,str(a.support.resolve().parent));import support
    iso,n=support.load(a.warehouse)
    class Plant(j.Plant):
        def __init__(self,blocked_row):super().__init__(iso,n);self.blocked_row=blocked_row
        def start(self):
            w=super().start()
            w.agents[2].y=self.blocked_row+1
            w._recalc_grid()
            return w
    totals=Counter();res={};example={}
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (w/name).write_bytes(setup.read(a.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(a.source/name,w/name)
        for name in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",name],cwd=w,check=True)
        setup.read(w/"staged_replay.inc");shutil.copyfile(HERE/"retry_bound.cc",w/"retry_bound.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","retry_bound.cc","-o","retry"],cwd=w,check=True)
        with sp.Popen([w/"retry"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for initial,obstruction,load,new_role,disclose,arm in product(range(2),range(2),range(2),range(3),range(2),range(3)):
                plant=Plant(initial)
                path=w/"dock"
                path.unlink(missing_ok=True)
                db=j.connect(path)
                assert j.apply(db,plant,None,3)==("new",[1,3,3,4])
                db.close()
                emit(load)
                first=None;extra=0;final_reply=None
                while True:
                    row=proc.stdout.readline().split();assert row
                    if row[0]=="C":
                        db=j.connect(path)
                        if row[1]=="0":
                            if obstruction:j.apply(db,plant,None,2)
                            current=plant.native(db)
                            actor=initial if current.grid[0,initial+1,2]==0 else 1-initial
                            kind,first=j.apply(db,plant,j.OLD,actor)
                            assert kind=="new" and first==[2+obstruction,actor,2,actor+1]
                            emit(1,*first)
                        else:
                            assert load==1
                            assert j.resolved(db,j.OLD)==first
                            actor=None if new_role==2 else first[1]^new_role
                            if not disclose:emit(0)
                            elif arm==0:
                                preserved=j.resolved(db,j.OLD)
                                assert preserved==first
                                emit(1,*preserved)
                            elif arm==1:
                                # Ordinary exact result cache before any actuator.
                                preserved=j.resolved(db,j.OLD)
                                emit(1,*preserved)
                            else:
                                # Deliberately treat the same request as fresh under
                                # a new actor. This is not a correct direct baseline.
                                if actor is None:emit(0)
                                else:
                                    kind,second=j.apply(db,plant,j.SAME_PHYSICAL_UNRELATED,actor)
                                    if kind=="new":
                                        extra+=1;emit(1,*second)
                                    else:
                                        assert kind=="blocked";emit(0)
                        db.close()
                    else:
                        assert row[0]=="O";break
                visits,replies,side,r0,tx0=map(int,row[1:6])
                final_reply=list(map(int,row[6:])) if len(row)>6 else None
                assert visits==1+load and side==load and r0==1-load and tx0==4
                expect_duplicate=bool(load and disclose and arm==2 and new_role==1 and not obstruction)
                assert extra==int(expect_duplicate)
                correct=not load or (arm!=2 and disclose)
                assert bool(correct)==(final_reply==first)
                assert replies==int(correct or expect_duplicate)
                db=j.connect(path)
                before=plant.native(db)
                assert j.resolved(db,j.OLD)==first and before._cur_steps==2+obstruction+extra
                assert support.pos(before.agents[3])==(3,4)
                db.close()
                totals[f"cases/{arm}"]+=1
                totals[f"exact_reply/{arm}"]+=int(correct)
                totals[f"duplicate/{arm}"]+=extra
                totals[f"no_reply/{arm}"]+=int(final_reply is None)
                res[(initial,obstruction,load,new_role,disclose,arm)]=(first,final_reply,extra)
                if (initial,obstruction,load,new_role,disclose)==(0,0,1,1,1):
                    example[str(arm)]=[first,final_reply,extra]
            proc.stdin.close();assert proc.wait()==0
    for k,v in res.items():
        if k[-1]==0:assert v==res[k[:-1]+(1,)]
    print(json.dumps({"counts":dict(totals),"same_key_later_actor":example},sort_keys=True))
if __name__=="__main__":main()
