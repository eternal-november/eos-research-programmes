#!/usr/bin/env python3
"""Test effect of late old authority frames without refunding their radio debit."""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse
import json
import shutil
import subprocess as sp
import sys
import tempfile
HERE=Path(__file__).resolve().parent
ROOT=next(d for d in (HERE,*HERE.parents) if (d/"local_authority.py").is_file())
sys.path.insert(0,str(ROOT))
import local_authority as a
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    args=p.parse_args()
    a.setup.read(args.support)
    a.pinned(ROOT/"local_authority.py","9dee7d5ec9ddfcc6cbea065b906e6886aaa999ec")
    sys.path.insert(0,str(args.support.resolve().parent))
    import support
    iso,n=support.load(args.warehouse)
    totals=Counter();cases={}
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        for name in ("extract_radio.py","visibility_shim.hpp","extract_visible.py"):
            (w/name).write_bytes(a.setup.read(args.source/name))
        for name in ("VISIBILITY.tsv","upstream_replay.cpp","table.cc","model.cc","range.cc",
                     "Vector3.hh","world.dot","world.sdf","broker.cc",*(f"src{i}" for i in range(6))):
            shutil.copyfile(args.source/name,w/name)
        for name in ("extract_visible.py","extract_radio.py"):sp.run([sys.executable,"-B",name],cwd=w,check=True)
        a.setup.read(w/"staged_replay.inc")
        f=a.parent("first_effect.hpp")/"first_effect.hpp"
        (w/f.name).write_bytes(a.pinned(f,"1e1624f0de957d627ea57182d94dbbb28d06c8a4"))
        shutil.copyfile(HERE/"late_grant.cc",w/"late_grant.cc")
        sp.run(["g++","-std=c++17","-O2","-Wno-return-type","late_grant.cc","-o","late"],cwd=w,check=True)
        with sp.Popen([w/"late"],cwd=w,text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as proc:
            def emit(*x):proc.stdin.write(" ".join(map(str,x))+"\n");proc.stdin.flush()
            for old,first,block,load,lost,cap,edge,kind,arm in product(
                    range(2),range(4),(2,3),(0,1,3),range(2),(4,5,6),range(2),range(4),range(4)):
                first_action,second_action,free,move=a.plant(support,iso,n,old,first,block)
                emit(old,load,lost,cap,edge,arm,kind)
                while True:
                    row=proc.stdout.readline().split();assert row
                    if row[0]=="P":owner=first_action();emit(owner)
                    elif row[0]=="L":
                        second_action()
                        cells=[free(k) for k in (0,1)]
                        emit(1)
                    elif row[0]=="I":emit(int(free(int(row[1]))))
                    elif row[0]=="M":emit(move(int(row[1])))
                    else:
                        assert row[0]=="O";break
                paid,fresh,refused,moves,side,tx,stale,htx=map(int,row[1:])
                valid=owner<2 and not lost
                old_tx=kind<3 and arm!=3
                old_same=old_tx and owner==1-old
                old_live=old_same and (kind==2 or (kind==1 and edge==0))
                closed=not valid or (arm==2 and old_same and kind!=0)
                has_room=4+int(valid and edge==0)+int(old_live)+4*int(owner==load)<=cap
                expected=bool(not closed and cells[owner] and has_room)
                assert (paid,fresh,refused,moves,side,tx,stale)==(
                    int(expected),int(valid),0,int(expected),2,4*int(expected),int(old_tx))
                # Native ledger at H is only lazily expired during a H send,
                # not by the later unrelated Q request.
                assert htx==int(owner<2 and not (kind==2 and edge and old_tx))+int(old_tx)
                totals[f"cases/{arm}"]+=1;totals[f"settled/{arm}"]+=paid
                if (old,first,block,load,lost)==(0,0,3,3,0):
                    cases[str((cap,edge,kind,arm))]=[paid,fresh,stale,tx,htx]
            proc.stdin.close();assert proc.wait()==0
    assert totals["settled/0"]==totals["settled/1"]
    print(json.dumps({"counts":dict(totals),"columns":["settled","fresh_arrivals","old_arrivals","Q_tx","H_ledger"],"same_holder_witness":cases},sort_keys=True))
if __name__=="__main__":main()
