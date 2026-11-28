#!/usr/bin/env python3
"""Closed-loop variant. C++ stops at the native dispatch cut for a decision."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
from itertools import product
import json
from subprocess import Popen, PIPE, run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"compound.cpp").is_file() else HERE.parent
PARENT_PINS={
    "compound.cpp":"b7ee8ea3aed3dcaa9c78e26253924c6f75e5edd0",
    "replay.py":"2cbeaf8222e0e39a66cc107d3b0cc40d2ea55b25",
}
for name,expect in PARENT_PINS.items():
    src=(PARENT/name).read_bytes()
    assert hashlib.sha1(f"blob {len(src)}\0".encode()+src).hexdigest()==expect
s=importlib.util.spec_from_file_location("family",PARENT/"replay.py")
family=importlib.util.module_from_spec(s)
sys.modules["family"]=family
s.loader.exec_module(family)

HOST="// asks the isolated controller at the next native transmit cut"
NEEDLE='  if(!to.empty())send("Q",to,archived,.875);'
ADAPTED=HOST+'''
  if(policy==3){
    std::cout<<"ASK "<<oldBytes<<" "<<cap<<" "<<w.state("Q").bytes_sent_this_epoch;
    for(const auto& r:receipts)std::cout<<" "<<r.first<<r.second;
    std::cout<<std::endl;  // synchronize with the external checker
    std::string chosen;assert(bool(std::cin>>chosen));
    assert(chosen=="R" || chosen=="S" || chosen=="-");
    to=(chosen=="-"?"":chosen);
  }
'''+NEEDLE

def decide(core,qty,cap,active,tape):
    # Local tape is tagged data from completed radio callbacks at Q.
    # Q has an instrumented typed read of its own native sender ledger.
    # No physical pose, global move flag, terminal commit or inspection
    # receiver event is supplied to the controller.
    assert tape[0]=="eR"
    live=[e[1] for e in tape if e[0]=="g"]
    assert len(live)<=1
    receipt=tuple((k,"Q",x) for k,x in enumerate(tape))
    scope=core.Event(2,0,uses=(core.Use(("TX","Q"),active,cap,8),),
                     paid=("inspection",))
    possible=[]
    # Authority is determined by the declared source/receipt law,
    # not by querying a simulator world from the controller.
    for address in ("R","S"):
        if live and address!=live[0]:
            continue
        auth=("qualified-current",address)
        arm=core.Event(7,0,need=frozenset((auth,)),uses=(
             core.Use(("TX","Q"),qty,cap,8),),paid=("older",))
        possible.append(core.Row(receipt,frozenset([auth]) if live else frozenset(),
                                 (scope,),{address:(arm,)}))
    cell=core.admitted(possible,"Q",7,{"inspection":7,"older":7},("R","S"))
    arms=cell[core.view(possible[0],"Q",7)]
    candidate=arms[0] if len(arms)==1 else "-"
    direct=live[0] if live and active+qty<=cap else "-"
    assert candidate==direct
    return candidate

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--geom",type=Path,default=HERE/"geometry")
    ap.add_argument("--source",type=Path,default=HERE/"source")
    ap.add_argument("--core",type=Path,default=(HERE/"core.py" if (HERE/"core.py").is_file()
                    else HERE.parents[2]/"core.py"))
    a=ap.parse_args()
    family.checked(a.geom/"egress.py",family.EGRESS)
    family.checked(a.core,family.CORE)
    core=family.mod("unchanged_core",a.core)
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        family.compile_native(a.geom,a.source,work)
        cpp=work/"compound.cpp"
        z=cpp.read_text()
        assert z.count(NEEDLE)==1
        cpp.write_text(z.replace(NEEDLE,ADAPTED))
        run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","online"],
            check=True,cwd=work)
        recs=list(product(range(2),range(2),range(3),[3],range(1,5),range(1,5),range(1,11)))
        recs=[x for x in recs if x[-1]>=x[-2]]
        with Popen([work/"online"],cwd=work,stdin=PIPE,stdout=PIPE,
                   text=True,bufsize=1) as p:
            met=0; abstain=0; good_side=0; tight_witness=0
            for c in recs:
                p.stdin.write(" ".join(map(str,c))+"\n");p.stdin.flush()
                tag,n,limit,debit,*tape=p.stdout.readline().split()
                assert tag=="ASK"
                choice=decide(core,int(n),int(limit),int(debit),tape)
                p.stdin.write(choice+"\n");p.stdin.flush()
                z=p.stdout.readline().split()
                assert tuple(map(int,z[:7]))==c
                paid,side,wrong=map(int,z[7:10])
                assert not wrong and paid==(choice!="-") and side
                met+=paid;good_side+=side;abstain+=(choice=="-")
                if c[0]==1 and c[1]==1 and c[2]==0 and c[-1]==c[-2]+c[-3]:
                    assert choice=="S" and paid
                    tight_witness+=1
            p.stdin.close()
            assert p.wait()==0 and not p.stdout.read()
    print(json.dumps(dict(callback_to_action_runs=len(recs),met_both=met,
                          declined_older=abstain,side_report=good_side,
                          tight_switched_with_stale_receipt=tight_witness),sort_keys=True))

if __name__=="__main__":main()
