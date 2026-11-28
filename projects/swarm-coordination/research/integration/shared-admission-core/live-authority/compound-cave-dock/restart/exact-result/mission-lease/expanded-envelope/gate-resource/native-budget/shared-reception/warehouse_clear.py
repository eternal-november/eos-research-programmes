#!/usr/bin/env python3
"""Transfer the gate-receipt checker to native warehouse commands and positions."""
import argparse
from itertools import product
import hashlib
import json
from pathlib import Path
from subprocess import check_output,run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=next(p for x in (HERE,*HERE.parents) for p in (x,x/"conditional-support")
    if (p/"support.py").is_file())
raw=(PARENT/"support.py").read_bytes()
assert hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="b0e6c09b6ba593ccd373371541f0d20a0ff8a414"
sys.path.insert(0,str(PARENT))
import support

BRIDGE='''#include <iostream>
#include "gate_receipt.hpp"
int main(){int fresh,epoch,live,role,hold;
while(std::cin>>fresh>>epoch>>live>>role>>hold){
  auto q=qualification(fresh,epoch);
  std::cout<<q<<" "<<may_use(q,live,role,hold)<<"\\n";
}}
'''

def one(iso,n,issue_late,return_request,protection,epoch_matches,entitled):
    w=iso.make(n,False)
    q,helper=w.agents
    # Clear the shelf fixture so gate access is purely robot occupancy.
    # Native calls still use the same movement rules. At most one requested
    # move per tick, as required by the source extraction.
    w.shelfs=[];w.goals=[];w.request_queue=[]
    cell=(2,1)
    act=n.Action
    def step(q_a,h_a=act.NOOP):
        n.step(w,[q_a.value,h_a.value])
    w._recalc_grid()
    assert support.pos(q)==(2,0) and support.pos(helper)==(1,1)
    step(act.FORWARD)
    assert support.pos(q)==cell
    early=w._cur_steps
    early_clear=support.pos(q)!=cell
    step(act.FORWARD)
    assert support.pos(q)==(2,2)
    late=w._cur_steps
    late_clear=support.pos(q)!=cell
    # Reading at cut: an ordinary inspection's bytes don't encode whether
    # they were fixed at the occupied cut or the later cleared cut.
    qualified=late_clear if issue_late else early_clear
    # Two turns don't affect the protected cell and remain admissible.
    step(act.LEFT);step(act.LEFT)
    previous=support.pos(q)
    assert previous==(2,2)
    if return_request and not protection:
        step(act.FORWARD)
    else:
        step(act.NOOP)
    clear=support.pos(q)!=cell
    consume=w._cur_steps
    assert (early,late,consume)==(1,2,5)
    inputs=(int(qualified),7 if epoch_matches else 6,7,int(entitled),int(protection))
    return w,step,clear,inputs,cell,act

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p=a.parse_args()
    iso,n=support.load(p.warehouse)
    cases=list(product((False,True),repeat=5))
    requests=[one(iso,n,*c)[3] for c in cases]
    with tempfile.TemporaryDirectory() as d:
        d=Path(d);(d/"bridge.cpp").write_text(BRIDGE)
        run(["g++","-std=c++17","-O2","-I",HERE,d/"bridge.cpp","-o",d/"gate"],check=True)
        raw=check_output([d/"gate"],input="".join(" ".join(map(str,r))+"\n" for r in requests),text=True)
    answers=[tuple(map(int,line.split())) for line in raw.splitlines()]
    assert len(answers)==len(cases)
    report={"cases":len(cases),"qualified_use":0,"qualified_but_no_hold_unsafe":0,
            "unrelated_turns_allowed":0,"matching_direct":0,"fresh_reread_admits_extra":0}
    for c,(scope,passed) in zip(cases,answers):
        late,requested,protected,epoch,entitled=c
        w,step,clear,_,cell,act=one(iso,n,*c)
        assert passed==(late and protected and epoch and entitled)
        if passed:
            assert clear
            step(act.NOOP,act.FORWARD)
            assert support.pos(w.agents[1])==cell
            report["qualified_use"]+=1
        if late and requested and not protected and epoch and entitled:
            assert scope==7 and not clear and not passed
            step(act.NOOP,act.FORWARD)
            assert support.pos(w.agents[1])!=(2,1)
            report["qualified_but_no_hold_unsafe"]+=1
        # Give the reference an additional exact consumed-at-use observation,
        # independently acquire it from native positions, and count the
        # safe opportunity the observation buys in this fixture.
        if late and epoch and entitled and clear and not passed:
            w,step,clear,_,cell,act=one(iso,n,*c)
            assert clear and support.pos(w.agents[0])!=cell
            step(act.NOOP,act.FORWARD)
            assert support.pos(w.agents[1])==cell
            report["fresh_reread_admits_extra"]+=1
        assert w.agents[0].dir.name=="UP"
        report["unrelated_turns_allowed"]+=1
        report["matching_direct"]+=1
    print(json.dumps(report,sort_keys=True))
if __name__=="__main__":main()
