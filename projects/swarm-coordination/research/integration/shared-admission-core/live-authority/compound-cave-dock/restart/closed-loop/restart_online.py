#!/usr/bin/env python3
"""Install the stable endpoint adapter, then drive it with the unchanged checker."""
import argparse
import hashlib
from collections import Counter
from itertools import product
from pathlib import Path
import importlib.util
import json
from subprocess import Popen, PIPE, run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"restart.py").is_file() else HERE.parent
parent_blob=(PARENT/"restart.py").read_bytes()
assert hashlib.sha1(f"blob {len(parent_blob)}\0".encode()+parent_blob).hexdigest()==    "2f1cf373df50d8b47b5b88d441c35d77a34a431a"
spec=importlib.util.spec_from_file_location("restart_fixture",PARENT/"restart.py")
restart=importlib.util.module_from_spec(spec)
sys.modules["restart_fixture"]=restart
spec.loader.exec_module(restart)
f=restart.f

DUE={"older":7,"inspection":7,"reconciled":7}

def policy(core,tape,active,a,cap,h):
    # This is a conditional operating family for reliable handoff and
    # scheduled install after the locally read departure. The concrete
    # prior paid/unpaid bit, remote receiver and RX data are not inputs.
    assert tape and tape[0]=="eR"
    grant=[e[-1] for e in tape if e[0]=="g"]
    assert len(grant)==1 and grant[0] in ("R","S")
    obs=tuple((k,"Q",t) for k,t in enumerate(tape))
    # gS proves the transfer already ran. gR can be the current owner,
    # or an early grant before a late move to S. Keep both rows.
    roles=("S",) if grant[0]=="S" else ("R","S")
    cases=[]
    for prior,receiver in product((False,True),roles):
        old=(core.Event(0,0,paid=("older",)),) if prior else ()
        side=core.Event(2,0,uses=(core.Use(("TX","Q"),active,cap,8),),
                        paid=("inspection",))
        # Transfer has its own sender and cap. Debit S only, and make
        # the future Q send test its actual sender cap on that RX row.
        absorb=()
        if receiver=="S":
            k=3 if grant[0]=="S" else 6
            absorb=(core.Event(k,1,uses=(core.Use(("RX","S"),h,32,8),)),)
        op=core.Event(7,0,uses=(core.Use(("TX","Q"),a,cap,8),
            core.Use(("RX",receiver),a,cap,8)),
            paid=("reconciled",) if prior else ("older","reconciled"))
        cases.append(core.Row(obs,frozenset(),old+(side,)+absorb,{"Dock":(op,)}))
    the_view=core.view(cases[0],"Q",7)
    assert all(core.view(r,"Q",7)==the_view for r in cases)
    accepts=core.admitted(cases,"Q",7,DUE,("Dock",))[the_view]==("Dock",)
    direct=(a+max(active,h)<=cap)  # an S branch is possible with either grant
    assert accepts==direct
    return accepts

def check(work,core):
    # Admitted temporal and communication schedule. Sizes include
    # boundary negative controls; omission variants are outside this
    # promise and are evaluated in the parent/native proof.
    family=[x for x in product(range(3),range(2),[0],(0,3),range(1,5),
                  range(1,5),range(1,10),range(2)) if x[6]>=x[5]]
    stat=Counter()
    twinned={}
    with Popen([work/"closed"],cwd=work,stdin=PIPE,stdout=PIPE,
               text=True,bufsize=1) as p:
        for case in family:
            p.stdin.write(" ".join(map(str,case))+"\n");p.stdin.flush()
            shift,dup,_,mode,a,b,c,prior=case
            while True:
                r=p.stdout.readline().split()
                assert r
                if r[0]=="J":
                    p.stdin.write(restart.station(work,r[1:])+"\n");p.stdin.flush()
                elif r[0]=="V":
                    # Drive the action using only the typed local
                    # inputs, not the simulator's case fields:
                    # a, c and h are known configuration emitted at Q.
                    active,local_size,local_cap,h=map(int,r[1:5])
                    obs=tuple(r[5:])
                    send=policy(core,obs,active,local_size,local_cap,h)
                    p.stdin.write(("SEND" if send else "REFUSE")+"\n");p.stdin.flush()
                else:
                    break
            assert tuple(map(int,r[:8]))==case
            new,side,wrong=map(int,r[8:11])
            old,reconciled=map(int,r[18:20])
            assert old==prior and side==1 and not wrong
            assert new+reconciled==int(send)
            assert not send or old+new==1
            stat[f"mode{mode}_admitted_and_reconciled"]+=int(send)
            stat[f"mode{mode}_side_paid"]+=side
            if mode==0 and shift==0 and b==1 and c==a+1:
                assert not send
                stat["still_r_but_hidden_late_s_prevents_guarantee"]+=1
            if mode==3 and shift==2 and c==a+b:
                assert send
                stat["tight_late_s_reconciled"]+=1
            if case[:-1] not in twinned:
                twinned[case[:-1]]=(obs,send)
            else:
                assert twinned.pop(case[:-1])==(obs,send)
        p.stdin.close()
        assert p.wait()==0
    assert not twinned
    print(json.dumps(dict(controller_cases=len(family),**stat),sort_keys=True))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--core",type=Path,default=(HERE/"core.py" if (HERE/"core.py").is_file()
                    else HERE.parents[3]/"core.py"))
    a=p.parse_args()
    f.checked(a.core,f.CORE)
    core=f.mod("frozen_core",a.core)
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        f.compile_native(a.geom,a.source,w)
        restart.add_adapter(w)
        cpp=w/"compound.cpp"
        src=restart.replace(cpp.read_text(),
            'std::cout<<"V "<<w.state("Q").bytes_sent_this_epoch;',
            'std::cout<<"V "<<w.state("Q").bytes_sent_this_epoch<<" "<<oldBytes'
            '<<" "<<cap<<" "<<(policy==3?1:2);')
        needle='  if(!to.empty())send("Q",to,archived,.875);'
        patch='''  std::string decision;assert(bool(std::cin>>decision));
  assert(decision=="SEND" || decision=="REFUSE");
  if(decision=="REFUSE")to="";
'''+needle
        cpp.write_text(restart.replace(src,needle,patch))
        run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","closed"],
            cwd=w,check=True)
        check(w,core)
if __name__=="__main__":main()
